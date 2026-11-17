""" CSeq Program Analysis Framework
	lazy sequentialisation: data race detection module

...

Authors:
    Alex Coto, Emerson Sales

Changes:
    2021.11.20  merged with ignoreassertion module
    2021.11.17  first version

To do:
  - implement AST-based variable name extraction (name_of_addr_var_for)
  - code review

"""

import re
import core.module
import core.parser
import core.utils
import pycparser.c_ast
from pycparserext.ext_c_parser import FuncDeclExt


class racedetector(core.module.Translator):
    def __init__(self):
        self.visitingfunction = False  # true while vising a function definition
        self.visitingcompound = False  # true while visiting a compound

        self.lvalue = None

        self.mutexes = []
        self.threads = []

        self.reads = []
        self.writes = []

        self.visiting_lhs = False
        self.visiting_rhs = False

        self.arrays = []

        self.atomicsection = False

        # False while the text of a member access is generated: then
        # visit_StructRef tracks what the access reads and writes
        self.tracking = True
        # the names of the fields that are (maybe) arrays or bit-fields and
        # the typedefs, see array_fields()
        self.arrayfields = None
        self.bitfields = set()
        self.typedefs = {}
        # the ids of the operands that are evaluated only under a condition
        # (the right operands of && and ||, the branches of ?:): the checks
        # run before the statement, unconditionally, so the accesses in
        # these operands are not checked (a race there is missed, none is
        # made up, and no check dereferences a pointer that the program
        # tests first, as in p && p->n->v)
        self.conditional = set()
        # the variables that a statement changes left of a comma operator
        # (None: a call there, which may change any)
        self.comma_changed = set()
        # whether the statement calls pthread_join, a wait or a lock
        self.sync_call = False
        # whether the statement creates a thread
        self.create_call = False
        # the definitions of the structs and unions by name, and the
        # numbers of array dimensions of the fields by name, see array_fields()
        self.structdefs = {}
        self.fielddims = {}
        self.declsbyname = {}
        self.ambiguoustypedefs = set()
        self.ambiguousstructs = set()

        super().__init__()

    def init(self):
        super().extend()

        self.inputparam(
            "data-race-check",
            "Enable data race detection (and disable assertions)",
            "",
            default=False,
            optional=True,
        )

    def loadfromstring(self, string, env):
        self.dataracecheck = (
            True if self.getinputparam("data-race-check") is not None else False
        )

        if not self.dataracecheck:
            return super().loadfromstring(string, env)

        self.thread_no = self.getinputparam("threads")

        # header = core.utils.printFile("data_race_header.c")
        header = "extern void __VERIFIER_error() __attribute__ ((__noreturn__)); void __dummy__(){}; void* __cs_thread_to_write_pos[NTHREADS + 1] = {};\n"
        header = header.replace("NTHREADS", str(self.thread_no))

        super().loadfromstring(string, env)

        self.insertheader(header)

    def visit(self, node, *args, **kwargs):
        # typeof does not evaluate its operand (as sizeof)
        if (id(node) not in self.conditional and
                node.__class__.__name__ not in ("TypeOfExpression", "TypeOfDeclaration")):
            return super().visit(node, *args, **kwargs)
        tracking, self.tracking = self.tracking, False
        try:
            return super().visit(node, *args, **kwargs)
        finally:
            self.tracking = tracking

    def visit_FuncDef(self, n):
        # a function that is no thread (or main) was not inlined:
        # __VERIFIER_atomic_* or called through a pointer; its accesses
        # would be checked as the accesses of thread 0, also against the
        # write position that its caller set for the statement that calls
        # it, so they are not checked (a race there is missed)
        if (not self.dataracecheck or n.decl.name == "main" or
                n.decl.name in self.Parser.threadIndex):
            return super().visit_FuncDef(n)
        tracking, self.tracking = self.tracking, False
        try:
            return super().visit_FuncDef(n)
        finally:
            self.tracking = tracking

    def visit_BinaryOp(self, n):
        if self.dataracecheck and n.op in ("&&", "||"):
            self.conditional.add(id(n.right))
        return super().visit_BinaryOp(n)

    def visit_TernaryOp(self, n):
        if self.dataracecheck:
            self.conditional.add(id(n.iftrue))
            self.conditional.add(id(n.iffalse))
        return super().visit_TernaryOp(n)

    def visit_ExprList(self, n):
        # the comma operator: the checks of the statement run before it, so
        # a side effect left of a comma could change the addresses that
        # the checks compute, as i in (i = 1, a[i]); keep the variables
        # that it changes, visit_Compound refuses the statement if an
        # address uses one of them
        if (self.dataracecheck and self.tracking and
                not isinstance(self.stacknodes[-2] if len(self.stacknodes) > 1 else None,
                               pycparser.c_ast.FuncCall)):
            for e in n.exprs[:-1]:
                self.note_changed(e)
        return super().visit_ExprList(n)

    def note_changed(self, n):
        """Note the variables that evaluating n changes, in comma_changed"""
        nodes = [n]
        while nodes and self.comma_changed is not None:
            m = nodes.pop()
            if isinstance(m, (pycparser.c_ast.FuncCall, pycparser.c_ast.Compound)):
                self.comma_changed = None  # (a call may change any)
            elif (isinstance(m, pycparser.c_ast.Assignment) or
                    isinstance(m, pycparser.c_ast.UnaryOp) and
                    m.op in ("++", "--", "p++", "p--")):
                target = m.lvalue if isinstance(m, pycparser.c_ast.Assignment) else m.expr
                if not isinstance(target, pycparser.c_ast.ID):
                    # *q = 1 may change any variable (q == &i)
                    self.comma_changed = None
                    continue
                ids = [target]
                while ids:
                    i = ids.pop()
                    if isinstance(i, pycparser.c_ast.ID):
                        self.comma_changed.add(i.name)
                    ids.extend(c for _, c in i.children())
            if m is not None:
                nodes.extend(c for _, c in m.children())

    def is_scanf_argument(self):
        """Whether the node visited is an argument of scanf, fscanf or sscanf,
        which write the objects that their arguments point to; the other
        library functions (the program's are inlined) are not trusted to
        access what an argument points to, as pthread_create(&t, 0, f, &x)"""
        if len(self.stacknodes) < 3:
            return False
        args, call = self.stacknodes[-2], self.stacknodes[-3]
        return (isinstance(args, pycparser.c_ast.ExprList) and
                isinstance(call, pycparser.c_ast.FuncCall) and call.args is args and
                isinstance(call.name, pycparser.c_ast.ID) and
                call.name.name in ("scanf", "fscanf", "sscanf", "__isoc99_scanf",
                                   "__isoc99_fscanf", "__isoc99_sscanf"))

    def has_side_effects(self, n):
        """Whether evaluating n may change a variable or call a function:
        the checks evaluate the expressions that they print once more,
        before the statement (also an expression without side effects is
        evaluated once more, but that changes nothing)."""
        nodes = [n]
        while nodes:
            m = nodes.pop()
            if (isinstance(m, (pycparser.c_ast.Assignment, pycparser.c_ast.FuncCall,
                               pycparser.c_ast.Compound)) or
                    isinstance(m, pycparser.c_ast.UnaryOp) and
                    m.op in ("++", "--", "p++", "p--")):
                return True
            nodes.extend(child for name, child in m.children())
        return False

    def refuse_side_effects(self, n):
        if self.tracking and self.has_side_effects(n):
            self.error("data race check: an access whose address has a side effect")

    def visit_Assignment(self, n):
        """
        op: =, +=, /= etc.

        Assignment: [op, lvalue*, rvalue*]
        """

        if not self.dataracecheck:
            return super().visit_Assignment(n)

        # self.lvalue = n.lvalue
        # original = super().visit_Assignment(n)
        # self.lvalue = None

        self.visiting_lhs = True
        lvalue = super().visit(n.lvalue)
        self.visiting_lhs = False

        self.visiting_rhs = True
        rvalue = super().visit(n.rvalue)
        self.visiting_rhs = False

        # (a comma expression binds weaker than the assignment)
        if isinstance(n.rvalue, pycparser.c_ast.ExprList):
            rvalue = "(%s)" % rvalue
        result = lvalue + n.op + rvalue

        # ignore stuff added by previous stages of cseq
        # lhs = result.split(n.op)[0].strip()
        # if not lhs.startswith('__cs_') and self.scope.find('pthread') == -1:
        #     self.writes.add(lhs)

        return "".join([l for l in result.splitlines() if not l.startswith("#")])

    def visit_ID(self, n):
        """
        ID: [name]
        """
        original = super().visit_ID(n)

        if (
            not self.dataracecheck
            or self.is_cseq_metadata(original)  # Skip stuff generated by cseq
            or self.current_scope_is_global()  # Skip global static initializers
            or (not self.is_global_var(n) and not self.is_pointer(original))
            or self.is_a_thread_or_mutex(n)
            or self.decays(n)
        ):
            return original

        if self.visiting_rhs or not self.visiting_lhs:
            self.track_read_from(n.name)
        elif self.visiting_lhs:
            self.track_write_to(n.name)

        return original

    def track_write_to(self, s, add_addr_of=True):
        if not self.tracking:
            return
        while s[0] == "(" and s[-1] == ")" and self.outer_parens_match(s):
            s = s[1:-1]
        elem = "&(%s)" % s if add_addr_of else s
        if elem not in self.writes:
            self.writes.append(elem)

    def outer_parens_match(self, s):
        """Whether the first ( of s closes at its last character"""
        depth = 0
        for i, c in enumerate(s):
            depth += {"(": 1, ")": -1}.get(c, 0)
            if depth == 0:
                return i == len(s) - 1
        return False

    def track_read_from(self, s, add_addr_of=True):
        if not self.tracking:
            return
        elem = "&(%s)" % s if add_addr_of else s
        if elem not in self.reads:
            self.reads.append(elem)

    def stop_tracking_write(self, s, add_addr_of=True):
        if not self.tracking:
            return
        elem = "&(%s)" % s if add_addr_of else s
        if elem in self.writes:
            self.writes.remove(elem)

    def stop_tracking_read(self, s, add_addr_of=True):
        if not self.tracking:
            return
        elem = "&(%s)" % s if add_addr_of else s
        if elem in self.reads:
            self.reads.remove(elem)

    def current_scope_is_global(self):
        """Returns whether the current scope is global. Duh."""
        return self.currentFunct == ""

    def is_a_thread_or_mutex(self, n):
        """Returns true if n is of type pthread_mutex_t or pthread_t."""
        s = self.threads + self.mutexes
        return (hasattr(n, "name") and n.name in s) or (n in s)

    def is_global_var(self, n):
        # if self.Parser.isglobal('0', n.name): #  and not self.Parser.ispointer(self.blockid, n.name)
        """ "Returns whether the given variable is global."""
        return ("0", n.name) in self.Parser.vars

    def is_in_pthread_aux_function(self):
        return self.scope.find("pthread") != -1

    def is_cseq_metadata(self, s):
        return (
            "__cs_" in s
            and not self.is_pointer(s)
            and "local" not in s
            and "param" not in s
        )

    def is_pointer(self, n):
        current_block = self.Parser.fblock[self.currentFunct]
        # TODO: Cannot use self.blockid here, is this a bug?
        # ispointer also returns true for functions, bug?
        return (
            self.Parser.ispointer(current_block + ".0", n)
            and n not in self.Parser.funcName
        )

    def visit_ArrayRef(self, n):
        """
        Example: a[i]

        ArrayRef: [name*, subscript*]
        """
        # original = super().visit_ArrayRef(n)
        # ((*pp)[1], ((int *) cp)[1], (c ? a : b)[0]: the base in parentheses)
        name = self._parenthesize_unless_simple(n.name)
        subscript = super().visit(n.subscript)
        original = "%s[%s]" % (name, subscript)

        if not self.dataracecheck or self.is_cseq_metadata(name):
            return original

        self.refuse_side_effects(n)

        # a row of an array of arrays (m[1], p->grid[1]) is an array, which
        # decays to the address of its first element: no access
        if self.tracking and self.yields_array(n):
            return original

        # TODO: Probably need to differentiate here pointers from arrays.
        if self.visiting_rhs or not self.visiting_lhs:
            # self.track_read_from(name)
            self.stop_tracking_read(name)
            self.track_read_from(original)
        elif self.visiting_lhs:
            # self.track_read_from(name)
            self.track_write_to(original)
            self.stop_tracking_write(name)

        return original

    def visit_StructRef(self, n):
        """
        type: . or ->
        name.field or name->field

        StructRef: [name*, type, field*]
        """
        if not self.dataracecheck:
            return super().visit_StructRef(n)

        # CSeq prints a union as a struct (workarounds), so that the
        # members of a union get different addresses
        if (n.field.name in getattr(self.cseqenv, "unionfields", ()) and
                not self.current_scope_is_global() and
                not self.is_in_pthread_aux_function()):
            self.error("data race check: an access to a member of a union (%s)" % n.field.name)

        # A member access accesses the member only, at &(original): not the
        # struct (or the array element or the enclosing member) that
        # contains it, which has the address of its first member, so that
        # two threads that access different members of one struct do not
        # race; nor the field, which is no variable. Generate the text
        # without tracking, then track the member and the reads that
        # compute its address (the pointers it dereferences, its indices).
        tracking, self.tracking = self.tracking, False
        original = super().visit_StructRef(n)
        self.tracking = tracking

        if (not tracking or self.current_scope_is_global() or
                self.is_in_pthread_aux_function()):
            return original  # global static initializers, CSeq's functions

        self.track_address_reads(n)

        # an array member is only its address (decays), *p->arr and
        # p->arr[i] track the element; the members of local variables are
        # not tracked (as the local variables); &(f().a) and & of a
        # bit-field do not compile
        root = n
        while (isinstance(root, pycparser.c_ast.StructRef) and root.type == "." or
                isinstance(root, pycparser.c_ast.ArrayRef) and self.maybe_array(root.name)):
            root = root.name
        if (self.decays(n) or self.is_bitfield(n) or
                isinstance(root, pycparser.c_ast.ID) and (
                    not self.is_global_var(root) or self.is_cseq_metadata(root.name)) or
                not isinstance(root, (pycparser.c_ast.ID, pycparser.c_ast.StructRef,
                                      pycparser.c_ast.ArrayRef, pycparser.c_ast.UnaryOp)) or
                isinstance(root, pycparser.c_ast.UnaryOp) and root.op != "*"):
            return original

        self.refuse_side_effects(n)

        if self.visiting_rhs or not self.visiting_lhs:
            self.track_read_from(original)
        else:
            self.track_write_to(original)

        return original

    def decays(self, n):
        """Whether n is (maybe) an array that decays to the address of its
        first element, which accesses nothing; also an array passed to a
        function: a library function (memset(a + 4, ...)) accesses what it
        accesses, not a[0], and the accesses of the program's functions
        are checked in their bodies (the races of library functions are
        missed)."""
        return self.maybe_array(n)

    def track_address_reads(self, n):
        """Track the reads that compute the address of the lvalue n: the
        pointers it dereferences and its indices, not n itself."""
        if isinstance(n, pycparser.c_ast.StructRef) and n.type == ".":
            self.track_address_reads(n.name)
        elif isinstance(n, pycparser.c_ast.ArrayRef):
            self.track_value_reads(n.subscript)
            self.track_pointer_reads(n.name)
        elif isinstance(n, pycparser.c_ast.StructRef):  # p->f
            self.track_pointer_reads(n.name)
        elif isinstance(n, pycparser.c_ast.UnaryOp) and n.op == "*":
            self.track_pointer_reads(n.expr)
        elif not isinstance(n, pycparser.c_ast.ID):
            self.track_value_reads(n)

    def track_pointer_reads(self, n):
        """Track the reads of the pointer n that is dereferenced: none if n
        is an array (as arr in arr[i] or arr->f), which is only its address."""
        if self.maybe_array(n):
            self.track_address_reads(n)
        else:
            self.track_value_reads(n)

    def track_value_reads(self, n):
        """Track the reads of evaluating the expression n."""
        lhs, rhs = self.visiting_lhs, self.visiting_rhs
        self.visiting_lhs, self.visiting_rhs = False, True
        self.visit(n)
        self.visiting_lhs, self.visiting_rhs = lhs, rhs

    def maybe_array(self, n):
        """Whether the lvalue n may be an array: an array is only its
        address (it decays to a pointer to its first element), reading it
        reads nothing. Unknown types are maybe arrays (then a race check is
        missing, but no check is wrong)."""
        if isinstance(n, pycparser.c_ast.StructRef):
            return n.field.name in self.array_fields()
        if isinstance(n, pycparser.c_ast.ID):
            decl = self.decl_of(n.name)
            return decl is None or self.is_array_type(decl.type)
        # a[i] or *a: the element type of a
        if (isinstance(n, pycparser.c_ast.ArrayRef) and isinstance(n.name, pycparser.c_ast.ID) or
                isinstance(n, pycparser.c_ast.UnaryOp) and n.op == "*" and
                isinstance(n.expr, pycparser.c_ast.ID)):
            decl = self.decl_of(n.name.name if isinstance(n, pycparser.c_ast.ArrayRef) else n.expr.name)
            if decl is None:
                return True
            t = self.resolve_typedef(decl.type)
            return (not isinstance(t, (pycparser.c_ast.ArrayDecl, pycparser.c_ast.PtrDecl)) or
                    self.is_array_type(t.type))
        return True

    def yields_array(self, n):
        """Whether the lvalue n (a[i] or *p) is an array; refuses when its
        type is unknown"""
        t = self.type_of(n)
        if t is not None:
            return isinstance(t, pycparser.c_ast.ArrayDecl)
        # the type of a member access is not known: count the dimensions
        # of the fields with its name
        k, base = 0, n
        while (isinstance(base, pycparser.c_ast.ArrayRef) or
                isinstance(base, pycparser.c_ast.UnaryOp) and base.op == "*"):
            k, base = k + 1, base.name if isinstance(base, pycparser.c_ast.ArrayRef) else base.expr
        self.array_fields()
        layers = self.fielddims.get(base.field.name) if isinstance(base, pycparser.c_ast.StructRef) else None
        if layers and None not in layers:
            # after k indexes or dereferences, an array if the next layer is
            # an array (int f[2][2], int (*f)[2] with k = 1)
            arrays = {len(l) > k and l[k] for l in layers}
            if arrays == {True}:
                return True
            if arrays == {False}:
                return False
        self.error("data race check: the type of %s is not known" % self.visit_no_tracking(n))

    def raw_shape(self, t):
        """The declarator layers of the type t and its base names, without
        resolving typedefs (to compare two definitions of a name)"""
        shape = []
        while isinstance(t, (pycparser.c_ast.ArrayDecl, pycparser.c_ast.PtrDecl,
                             pycparser.c_ast.TypeDecl)):
            shape.append(t.__class__.__name__)
            t = t.type
        return tuple(shape) + (t.__class__.__name__,
                               tuple(getattr(t, "names", None) or [getattr(t, "name", None)]))

    def type_shape(self, t):
        """The array and pointer layers of the type t, or None"""
        shape = []
        t = self.resolve_typedef(t)
        while isinstance(t, (pycparser.c_ast.ArrayDecl, pycparser.c_ast.PtrDecl)):
            shape.append(t.__class__.__name__)
            t = self.resolve_typedef(t.type)
        if not isinstance(t, pycparser.c_ast.TypeDecl):
            return None
        base = t.type
        return tuple(shape) + (base.__class__.__name__,
                               tuple(getattr(base, "names", None) or [getattr(base, "name", None)]))

    def visit_no_tracking(self, n):
        tracking, self.tracking = self.tracking, False
        try:
            return super().visit(n)
        finally:
            self.tracking = tracking

    def type_of(self, n):
        """The type of the expression n (a typedef name resolved), or None"""
        C = pycparser.c_ast
        if isinstance(n, C.ID):
            decl = self.decl_of(n.name)
            if decl is None:
                # (the parameters of inlined functions are declared in
                # inner blocks): the declarations of the name anywhere, if
                # they agree on the shape of the type
                self.array_fields()
                decls = self.declsbyname.get(n.name, [])
                shapes = {self.type_shape(d.type) for d in decls}
                decl = decls[0] if len(shapes) == 1 and None not in shapes else None
            return self.resolve_typedef(decl.type) if decl is not None else None
        if isinstance(n, C.ArrayRef) or isinstance(n, C.UnaryOp) and n.op == "*":
            t = self.type_of(n.name if isinstance(n, C.ArrayRef) else n.expr)
            if isinstance(t, (C.ArrayDecl, C.PtrDecl)):
                return self.resolve_typedef(t.type)
            return None
        if isinstance(n, C.StructRef):
            t = self.type_of(n.name)
            if n.type == "->":
                t = self.resolve_typedef(t.type) if isinstance(t, (C.ArrayDecl, C.PtrDecl)) else None
            su = t.type if isinstance(t, C.TypeDecl) else None
            if not isinstance(su, (C.Struct, C.Union)):
                return None
            if su.decls is None and su.name in self.ambiguousstructs:
                return None  # (a tag defined twice)
            decls = su.decls if su.decls is not None else self.structdefs.get(su.name)
            for d in decls or []:
                if d.name == n.field.name:
                    return self.resolve_typedef(d.type)
            return None
        if isinstance(n, C.UnaryOp) and n.op == "&":
            t = self.type_of(n.expr)
            return C.PtrDecl([], t) if t is not None else None
        if isinstance(n, C.TernaryOp):
            return self.type_of(n.iftrue)
        if isinstance(n, C.Cast):
            return self.resolve_typedef(n.to_type.type)
        if isinstance(n, C.BinaryOp) and n.op in ("+", "-"):
            for t in (self.type_of(n.left), self.type_of(n.right)):
                if isinstance(t, (C.ArrayDecl, C.PtrDecl)):
                    return t  # (an array decays to a pointer to its element)
            return None
        return None

    def decl_of(self, name):
        block = self.Parser.blockdefid(self.Parser.fblock[self.currentFunct] + ".0", name)
        return self.Parser.symbols.get((block, name)) if block is not None else None

    def resolve_typedef(self, t, seen=()):
        """t, or the type that its typedef name stands for"""
        self.array_fields()  # collects the typedefs
        if (isinstance(t, pycparser.c_ast.TypeDecl) and
                isinstance(t.type, pycparser.c_ast.IdentifierType) and
                len(t.type.names) == 1 and t.type.names[0] not in seen):
            name = t.type.names[0]
            if name in self.ambiguoustypedefs:
                return None  # (a typedef name defined twice: unknown)
            typedef = self.typedefs.get(name)
            if typedef is not None:
                return self.resolve_typedef(typedef.type, seen + (name,))
        return t

    def is_bitfield(self, n):
        """Whether n is a member access (maybe) to a bit-field."""
        self.array_fields()  # collects the bit-fields
        return isinstance(n, pycparser.c_ast.StructRef) and n.field.name in self.bitfields

    def is_array_type(self, t):
        t = self.resolve_typedef(t)
        return t is None or isinstance(t, pycparser.c_ast.ArrayDecl)  # (unknown: maybe)

    def array_fields(self):
        """The names of the fields of the structs and unions that are
        arrays (in any of them: the type of a member access is unknown);
        collects the bit-fields and the typedefs too."""
        if self.arrayfields is None:
            self.arrayfields, self.typedefs, fields = set(), {}, []
            members = set()
            # (without recursion, the AST is deep)
            nodes = [self.ast]
            while nodes:
                node = nodes.pop()
                if isinstance(node, pycparser.c_ast.Typedef):
                    if (node.name in self.typedefs and
                            self.raw_shape(self.typedefs[node.name].type) != self.raw_shape(node.type)):
                        self.ambiguoustypedefs.add(node.name)
                    self.typedefs[node.name] = node
                elif (isinstance(node, pycparser.c_ast.Decl) and node.name and
                        id(node) not in members):
                    self.declsbyname.setdefault(node.name, []).append(node)
                elif isinstance(node, (pycparser.c_ast.Struct, pycparser.c_ast.Union)):
                    fields.extend(d for d in node.decls or [] if d.name)
                    members.update(id(d) for d in node.decls or [])
                    if node.decls is not None and node.name:
                        if (node.name in self.structdefs and
                                [(d.name, self.raw_shape(d.type)) for d in self.structdefs[node.name]] !=
                                [(d.name, self.raw_shape(d.type)) for d in node.decls]):
                            self.ambiguousstructs.add(node.name)
                        self.structdefs[node.name] = node.decls
                    self.bitfields.update(d.name for d in node.decls or []
                                          if d.name and d.bitsize is not None)
                nodes.extend(child for name, child in node.children())
            self.arrayfields.update(d.name for d in fields if self.is_array_type(d.type))
            # the array and pointer layers of the fields by name (None:
            # unknown), see yields_array()
            for d in fields:
                layers, t = [], self.resolve_typedef(d.type)
                while isinstance(t, (pycparser.c_ast.ArrayDecl, pycparser.c_ast.PtrDecl)):
                    layers.append(isinstance(t, pycparser.c_ast.ArrayDecl))
                    t = self.resolve_typedef(t.type)
                self.fielddims.setdefault(d.name, set()).add(tuple(layers) if t is not None else None)
        return self.arrayfields

    def visit_Decl(self, n):
        """
        Maybe remove?

        # name: the variable being declared
        # quals: list of qualifiers (const, volatile)
        # funcspec: list function specifiers (i.e. inline in C99)
        # storage: list of storage specifiers (extern, register, etc.)
        # type: declaration type (probably nested with all the modifiers)
        # init: initialization value, or None
        # bitsize: bit field size, or None
        #
        Decl: [name, quals, storage, funcspec, type*, init*, bitsize*]
        """

        if not self.dataracecheck:
            return super().visit_Decl(n)

        if isinstance(n.type, pycparser.c_ast.Struct):
            pass
        elif isinstance(n.type, pycparser.c_ast.ArrayDecl):
            if n.name not in self.arrays:
                self.arrays.append(n.name)
        elif hasattr(n.type, "type") and isinstance(
            n.type.type, pycparser.c_ast.IdentifierType
        ):
            if "pthread_t" in n.type.type.names:
                self.threads.append(n.name)
            if "pthread_mutex_t" in n.type.type.names:
                self.mutexes.append(n.name)

        old = self.visiting_rhs
        self.visiting_rhs = True
        # TODO: check for declarations without initializers
        ret = super().visit_Decl(n)
        self.visiting_rhs = old

        return ret

    def visit_Compound(self, n):
        """
        Compound statement in C99 is a list of block items (declarations or
        statements).

        Compound: [block_items**]
        """

        if not self.dataracecheck:
            return super().visit_Compound(n)

        # the accesses of a condition (if (!(g++ < 1)) goto ... of an
        # unrolled loop) are checked before the first statement of the
        # branch; its write position would be reset after that statement,
        # which may be a goto, so the writes are only checked as reads
        if self.sync_call:  # (a join or a wait in the condition)
            self.reads, self.writes, self.sync_call = [], [], False
        self.demote_writes()
        self.refuse_changed_by_comma(self.reads)

        old = self.visitingcompound
        self.visitingcompound = True

        start = self._make_indent() + "{\n"
        s = ""
        cur_thr_idx = (
            self.Parser.threadIndex[self.scope]
            if self.scope in self.Parser.threadIndex
            else 0
        )
        should_close_atomic_section = False

        if n.block_items:
            for stmt in n.block_items:
                self.comma_changed = set()
                self.sync_call = self.create_call = False
                s += self._generate_stmt(stmt)
                if self.sync_call:
                    self.reads, self.writes, self.sync_call = [], [], False
                if self.create_call:
                    self.demote_writes()
                    self.create_call = False

                # the reset of the write position after a statement that
                # does not continue (return g = v; goto) would be dead: the
                # position would stay set, so the writes are only checked
                # as reads
                if self.does_not_continue(stmt):
                    self.demote_writes()

                if len(self.writes) > 1:
                    self.error("Multiple writes on a single statement not supported")

                # This is needed because of metadata from previous modules.
                lines = s.splitlines()

                stmt_line = lines.pop()

                read_writes = self.writes + self.reads

                # a variable that the statement changes left of a comma,
                # before an access whose address uses it
                self.refuse_changed_by_comma(read_writes)
                self.comma_changed = set()

                # the checks evaluate these expressions once more, before
                # the statement (the AST checks refuse the side effects
                # already, this is for the expressions that they miss)
                for var_name in read_writes:
                    if re.search(r"\+\+|--|<<=|>>=|(?<![=!<>])=(?!=)|"
                                 r"\b(?!sizeof\b|_Alignof\b|__alignof__\b|__alignof\b)[A-Za-z_]\w*\s*\(",
                                 var_name):
                        self.error("data race check: a side effect in %s" % var_name)

                # distinct addresses need distinct variables: the names drop
                # digits and operators, (* q1).x and (* q2).x would share one
                addr_vars = {}
                for var_name in read_writes:
                    if var_name not in addr_vars:
                        k = 0
                        while self.name_of_addr_var_for(var_name, k) in addr_vars.values():
                            k += 1
                        addr_vars[var_name] = self.name_of_addr_var_for(var_name, k)

                if len(read_writes) > 0 and not self.atomicsection:
                    lines.append("__VERIFIER_atomic_begin();\n")
                    should_close_atomic_section = True

                for var_name in read_writes:
                    var_addr = addr_vars[var_name]

                    lines += [
                        "void* %s = %s;" % (var_addr, var_name),
                    ]

                    asserts = [
                        # an idle thread's position is NULL (0), as the
                        # address of the first member of a NULL pointer
                        'if (__cs_thread_to_write_pos[%d] == %s) if (%s) __cs_data_race();'
                        % (i, var_addr, var_addr)
                        for i in range(self.thread_no + 1)
                        if i != cur_thr_idx
                    ]

                    lines += asserts

                for var_name in self.writes:
                    var_addr = addr_vars[var_name]
                    lines += [
                        "__cs_thread_to_write_pos[%d] = %s;" % (cur_thr_idx, var_addr),
                    ]

                lines.append(stmt_line)  # TODO: Check if ; is needed

                if should_close_atomic_section:
                    lines.append("__VERIFIER_atomic_end();\n")
                    should_close_atomic_section = False

                for var_name in self.writes:
                    lines += [
                        "__cs_thread_to_write_pos[%d] = 0;" % (cur_thr_idx),
                    ]

                s = "\n".join(lines)

                self.writes = []
                self.reads = []

        end = self._make_indent() + "}\n"

        self.visitingcompound = old

        return start + s + end

    def refuse_changed_by_comma(self, exprs):
        """Refuses if an address in exprs uses a variable that the
        statement (or the condition) changes left of a comma"""
        if exprs and (self.comma_changed is None or any(
                re.search(r"(?<!\w)%s(?!\w)" % re.escape(v), e)
                for v in self.comma_changed for e in exprs)):
            self.error("data race check: an address that changes left of a comma")

    def demote_writes(self):
        for w in self.writes:
            if w not in self.reads:
                self.reads.append(w)
        self.writes = []

    def does_not_continue(self, stmt):
        """Whether the statement may not continue with the next one: a
        jump, or a call of a function that does not return"""
        while isinstance(stmt, pycparser.c_ast.Label):
            stmt = stmt.stmt
        if isinstance(stmt, (pycparser.c_ast.Return, pycparser.c_ast.Goto,
                             pycparser.c_ast.Break, pycparser.c_ast.Continue)):
            return True
        nodes = [stmt]
        while nodes:
            m = nodes.pop()
            if (isinstance(m, pycparser.c_ast.FuncCall) and
                    isinstance(m.name, pycparser.c_ast.ID) and
                    m.name.name in ("pthread_exit", "exit", "_exit", "_Exit", "abort",
                                    "longjmp", "siglongjmp", "__assert_fail",
                                    "__VERIFIER_error", "reach_error")):
                return True
            if m is not None and not isinstance(m, pycparser.c_ast.Compound):
                nodes.extend(c for _, c in m.children())
        return False

    def name_of_addr_var_for(self, var_read, k=0):
        name = re.sub(r"[\[\]\.\&\*\(\)]", "_", var_read) + "__"
        name = re.sub(r"[\d\s\+\-\|\>\<]", "", name)
        # (% / ! ^ ~ ? : , in an index; $, of the wmm tasks, stays as
        # before: Symbiotic does not declare these names, they do not compile)
        name = re.sub(r"[^\w$]", "_", name)
        # __<name>___ (with the k-th suffix): Symbiotic declares these once
        if not name.startswith("__"):
            name = "__" + name
        name = name.rstrip("_") + ("_%d" % k if k else "") + "___"
        return name  # TODO: Check

    def is_sizeof(self, op):
        return op in ("sizeof", "_Alignof", "__alignof__", "__alignof")

    def visit_UnaryOp(self, n):
        """
        UnaryOp: [op, expr*]
        """
        if self.dataracecheck and n.op == "&":
            # &x accesses no x (pthread_create(&t, 0, f, &x)), only what
            # computes its address (p in &p->f, i in &a[i])
            tracking, self.tracking = self.tracking, False
            original = super().visit_UnaryOp(n)
            self.tracking = tracking
            if (tracking and not self.current_scope_is_global() and
                    not self.is_in_pthread_aux_function() and
                    not self.is_cseq_metadata(original)):
                if self.is_scanf_argument():
                    self.track_value_reads(n.expr)  # scanf("%d", &x) writes x
                else:
                    self.track_address_reads(n.expr)
            return original

        reads, writes = list(self.reads), list(self.writes)
        expr = super().visit(n.expr)
        original = super().visit_UnaryOp(n)

        if self.dataracecheck and self.is_sizeof(n.op) and self.tracking:
            # sizeof (and _Alignof) does not evaluate its operand
            self.reads, self.writes = reads, writes

        if (
            not self.dataracecheck
            or self.is_cseq_metadata(expr)
            or self.is_in_pthread_aux_function()
            or self.is_sizeof(n.op)
            or self.is_a_thread_or_mutex(expr)
        ):
            return original

        # Stuff to ignore:
        # sizeof
        # __cs_
        # stuff containing *?
        # unary -

        # (the operator, not the text: -(i++) writes no -(i++))
        inc_or_dec = n.op in ("++", "--", "p++", "p--")
        if n.op == "*" or inc_or_dec:
            self.refuse_side_effects(n.expr)

        # Right now we're just considering ++ and --
        if inc_or_dec and not self.is_bitfield(n.expr):
            self.track_write_to(expr)  # (& of a bit-field does not compile)

        # *(& x) reads no pointer (and & (& x) would not compile)
        reads_pointer = not (isinstance(n.expr, pycparser.c_ast.UnaryOp) and n.expr.op == "&")

        # the pointer is read (an lvalue: &(p + 1) would not compile, the
        # visits of p + 1 and (int *) &g tracked their reads)
        # (*m with m an array, m[2][2], s.rows, a[1] of a 3-D array, reads
        # no pointer: &m is the address of its first element)
        reads_pointer = reads_pointer and not self.maybe_array(n.expr) and isinstance(
            n.expr, (pycparser.c_ast.ID, pycparser.c_ast.ArrayRef, pycparser.c_ast.StructRef)) or (
            isinstance(n.expr, pycparser.c_ast.UnaryOp) and n.expr.op == "*")
        # *pa where pa points to an array is an array (it decays): no access
        pointee = n.op == "*" and not (self.tracking and self.yields_array(n))
        if n.op == "*":
            if self.visiting_rhs or not self.visiting_lhs:
                if reads_pointer:
                    self.track_read_from(expr)
                if pointee:
                    self.track_read_from("(%s)" % expr, add_addr_of=False)
            elif self.visiting_lhs:
                if reads_pointer:
                    self.track_read_from(expr)
                if pointee:
                    self.track_write_to("(%s)" % expr, add_addr_of=False)
                self.stop_tracking_write(expr)

        return original

    def is_unary_inc_or_dec(self, original):
        return original.find("++") >= 0 or original.find("--") >= 0

    def is_function_pointer(self, s):
        current_block = self.Parser.fblock[self.currentFunct]
        try:
            # TODO: Implement this without exceptions
            return isinstance(
                self.Parser.vars[(current_block, s.name)].type.type, FuncDeclExt
            )
        except Exception as e:
            return False
        # return s.strip().endswith('()') and '*' in s

    def is_unsupported_pthread_function(self, n):
        return n.name in (
            "pthread_rwlock_rdlock",
            "pthread_rwlock_wrlock",
            "pthread_rwlock_rdlock",
        )

    def visit_FuncCall(self, n):
        """
        # name: Id
        # args: ExprList
        #
        FuncCall: [name*, args*]
        """
        if not self.dataracecheck:
            return super().visit_FuncCall(n)

        if hasattr(n.name, "name"):
            if self.is_unsupported_pthread_function(n.name):
                self.error("%s not supported" % n.name.name, snippet=True, lineno=True)
            if self.is_function_pointer(n.name):
                self.error("Function pointers (%s) not supported." % n.name.name)

            # When data race checking,
            # remove any assertion statements that
            # may occur in the source code.
            #
            if self.dataracecheck:
                if n.name.name in [
                    "assert",
                    "ASSERT",
                    "reach_error",
                    "abort",
                    "__VERIFIER_error",
                ]:
                    return "__dummy__()"

        visitingfunction, self.visitingfunction = self.visitingfunction, True

        fref = self._parenthesize_unless_simple(n.name)

        if fref == "__VERIFIER_atomic_begin":
            self.atomicsection = True
        elif fref == "__VERIFIER_atomic_end":
            self.atomicsection = False

        ret = super().visit_FuncCall(n)

        self.visitingfunction = visitingfunction

        if fref == "pthread_create":
            # the write position of a write in the statement would stay
            # set until after the next context switch, which the created
            # thread may take: the writes are only checked as reads
            # (pthread_create(&t, 0, f, (void *)(long)cnt++)), see visit_Compound
            self.create_call = True

        if (fref in ["pthread_mutex_unlock", "pthread_mutex_lock", "pthread_mutex_init",
                     "pthread_join"] or fref.startswith("pthread_cond_wait") or
                fref.startswith("pthread_cond_timedwait") or
                # (an atomic function may block: assume(lk == 0))
                fref.startswith("__VERIFIER_atomic_") and
                fref not in ("__VERIFIER_atomic_begin", "__VERIFIER_atomic_end")):
            # If this is a mutex function call, skip processing the reads and writes.
            # (also of a join or a wait: the checks run before the call,
            # the rest of the statement after it, g = pthread_join(t, 0);
            # the accesses after the call in the statement are dropped when
            # the statement ends, see visit_Compound)
            self.reads.clear()
            self.writes.clear()
            self.sync_call = True

        return ret

    def visit_Label(self, n):
        """
        Label: [name, stmt*]
        """
        ret = super(self.__class__, self).visit_Label(n)

        if not self.dataracecheck:
            return ret

        if "ERROR" in n.name:
            return self._generate_stmt(n.stmt)

        return ret
