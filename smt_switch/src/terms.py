# This file is part of the smt-switch project.
# See the file LICENSE in the top-level source directory for licensing information.

from abc import ABCMeta
from . import sorts
from fractions import Fraction
from .functions import func_enum, func_symbols, operator
import re


class TermBase(metaclass=ABCMeta):
    def __init__(self, smt, solver_term, sort, op=None, children=None):
        self._smt = smt
        self._solver_term = solver_term
        self._value = None
        self._sort = sort
        self._op = op
        self._children = children
        self._issym = False

    @property
    def sort(self):
        return self._sort

    @property
    def op(self):
        return self._op

    @property
    def children(self):
        return self._children

    @property
    def solver_term(self):
        return self._solver_term

    def __eq__(self, other):
        return self._smt.ApplyFun(self._smt.Equals, self, other)

    def __ne__(self, other):
        return self._smt.ApplyFun(self._smt.Not, self == other)

    def __add__(self, other):
        if self.sort.__class__ == sorts.BitVec:
            return self._smt.ApplyFun(self._smt.BVAdd, self, other)
        elif self.sort.__class__ == sorts.FP:
            return self._smt.ApplyFun(self._smt.FPAdd, self._smt.Round.default, self, other)
        else:
            return self._smt.ApplyFun(self._smt.Add, self, other)

    def __radd__(self, other):
        return self.__add__(other)

    def __sub__(self, other):
        # override for bitvectors
        if self.sort.__class__ == sorts.BitVec:
            return self._smt.ApplyFun(self._smt.BVSub, self, other)
        elif self.sort.__class__ == sorts.FP:
            return self._smt.ApplyFun(self._smt.FPSub, self._smt.Round.default, self, other)
        else:
            return self._smt.ApplyFun(self._smt.Sub, self, other)

    def __rsub__(self, other):
        # override for bitvectors
        if self.sort.__class__ == sorts.BitVec:
            return self._smt.ApplyFun(self._smt.BVSub, other, self)
        else:
            return self._smt.ApplyFun(self._smt.Sub, other, self)

    def __neg__(self):
        if self.sort.__class__ == sorts.BitVec:
            return self._smt.ApplyFun(self._smt.BVNeg, self)
        elif self.sort.__class__ == sorts.FP:
            return self._smt.ApplyFun(self._smt.FPNeg, self._smt.Round.default, self)
        else:
            zero = self._smt.TheoryConst(self.sort, 0)
            return self._smt.ApplyFun(self._smt.Sub, zero, self)

    def __mul__(self, other):
        if self.sort.__class__ == sorts.BitVec:
            return self._smt.ApplyFun(self._smt.BVMul, self, other)
        elif self.sort.__class__ == sorts.FP:
            return self._smt.ApplyFun(self._smt.FPMul, self._smt.Round.default, self, other)
        else:
            raise NotImplementedError("Haven't added nonlinear arithmetic operators yet.")

    def __rmul__(self, other):
        return self.__mul__(other)

    def __mod__(self, other):
        if self.sort.__class__ == sorts.BitVec:
            return self._smt.ApplyFun(self._smt.BVUrem, self, other)
        else:
            raise NotImplementedError("Haven't added nonlinear arithmetic operators yet.")

    def __truediv__(self, other):
        if self.sort.__class__ == sorts.BitVec:
            return self._smt.ApplyFun(self._smt.BVUdiv, self, other)
        elif self.sort.__class__ == sorts.FP:
            return self._smt.ApplyFun(self._smt.FPDiv, self._smt.Round.default, self, other)
        else:
            raise NotImplementedError("Haven't added nonlinear arithmetic operators yet.")

    def __rtruediv__(self, other):
        if self.sort.__class__ == sorts.BitVec:
            return self._smt.ApplyFun(self._smt.BVUdiv, other, self)
        else:
            raise NotImplementedError("Haven't added nonlinear arithmetic operators yet.")

    def __lt__(self, other):
        assert not hasattr(other, "sort") or self.sort == other.sort, \
          "Operator expects 2 arguments of same sort"
        if self.sort.__class__ == sorts.BitVec:
            return self._smt.ApplyFun(self._smt.BVSlt, self, other)
        elif self.sort.__class__ == sorts.FP:
            return self._smt.ApplyFun(self._smt.FPLt, self, other)

        return self._smt.ApplyFun(self._smt.LT, self, other)

    def __le__(self, other):
        assert not hasattr(other, "sort") or self.sort == other.sort, \
          "Operator expects 2 arguments of same sort"
        if self.sort.__class__ == sorts.BitVec:
            return self._smt.ApplyFun(self._smt.BVSle, self, other)
        elif self.sort.__class__ == sorts.FP:
            return self._smt.ApplyFun(self._smt.FPLe, self, other)

        return self._smt.ApplyFun(self._smt.LEQ, self, other)

    def __gt__(self, other):
        assert not hasattr(other, "sort") or self.sort == other.sort, \
          "Operator expects 2 arguments of same sort"
        if self.sort.__class__ == sorts.BitVec:
            return self._smt.ApplyFun(self._smt.BVSgt, self, other)
        elif self.sort.__class__ == sorts.FP:
            return self._smt.ApplyFun(self._smt.FPGt, self, other)

        return self._smt.ApplyFun(self._smt.GT, self, other)

    def __ge__(self, other):
        assert not hasattr(other, "sort") or self.sort == other.sort, \
          "Operator expects 2 arguments of same sort"
        if self.sort.__class__ == sorts.BitVec:
            return self._smt.ApplyFun(self._smt.BVSge, self, other)
        elif self.sort.__class__ == sorts.FP:
            return self._smt.ApplyFun(self._smt.FPGe, self._smt.Round.default, self, other)

        return self._smt.ApplyFun(self._smt.GEQ, self, other)

    # bit operations
    def __and__(self, other):
        if not issubclass(other.__class__, TermBase):
            other = self._smt.TheoryConst(self.sort, other)
        return self._smt.ApplyFun(self._smt.BVAnd, self, other)

    def __or__(self, other):
        if not issubclass(other.__class__, TermBase):
            other = self._smt.TheoryConst(self.sort, other)
        return self._smt.ApplyFun(self._smt.BVOr, self, other)

    def __xor__(self, other):
        if not issubclass(other.__class__, TermBase):
            other = self._smt.TheoryConst(self.sort, other)
        return self._smt.ApplyFun(self._smt.BVXor, self, other)

    def __lshift__(self, other):
        if not issubclass(other.__class__, TermBase):
            other = self._smt.TheoryConst(self.sort, other)
        return self._smt.ApplyFun(self._smt.BVShl, self, other)

    def __rlshift__(self, other):
        if not issubclass(other.__class__, TermBase):
            other = self._smt.TheoryConst(self.sort, other)
        return self._smt.ApplyFun(self._smt.BVShl, other, self)

    def __rshift__(self, other):
        if not issubclass(other.__class__, TermBase):
            other = self._smt.TheoryConst(self.sort, other)
        return self._smt.ApplyFun(self._smt.BVAshr, self, other)

    def __rrshift__(self, other):
        if not issubclass(other.__class__, TermBase):
            other = self._smt.TheoryConst(self.sort, other)
        return self._smt.ApplyFun(self._smt.BVAshr, other, self)

    def __invert__(self):
        assert self.sort.__class__ == sorts.BitVec
        return self._smt.ApplyFun(self._smt.BVNot, self)

    def __getitem__(self, idx):
        if self.sort.__class__ != self._smt.BitVec:
            raise ValueError('Slicing only defined for BitVec sorts')

        if isinstance(idx, slice):
            if idx.step and idx.step != 1:
                raise ValueError('Extract does not support step != 1')

            if idx.start < 0 or idx.start >= self.sort.width:
                raise ValueError('{} is not a valid index for BitVec width {}'.format(idx.start, self.sort.width))

            if idx.stop < 0 or idx.stop >= self.sort.width:
                raise ValueError('{} is not a valid index for BitVec width {}'.format(idx.stop, self.sort.width))

            if idx.start < idx.stop:
                raise ValueError('Extract is defined as [bith:bitl]')

            return self._smt.ApplyFun(self._smt.Extract(idx.start, idx.stop), self)

        elif isinstance(idx, int):
            if idx < 0 or idx >= self.sort.width:
                raise ValueError('{} is not a valid index for BitVec width {}'.format(idx, self.sort.width))

            return self._smt.ApplyFun(self._smt.Extract(idx, idx), self)
        else:
            raise ValueError('Slicing not defined for {}'.format(idx))


class CVC4Term(TermBase):
    def __init__(self, smt, solver_term):
        self._str2sort = {'int': lambda p: sorts.Int(),
                          'real': lambda p: sorts.Real(),
                          'bitvector': lambda p: sorts.BitVec(p),
                          'bitvec': lambda p: sorts.BitVec(p),
                          'bool': lambda p: sorts.Bool(),
                          'boolean': lambda p: sorts.Bool(),
                          'array': lambda ids, ds: sorts.Array(ids, ds),
                          'floatingpoint': lambda exp, sig: sorts.FP(exp, sig),
                          'roundingmode': lambda p: sorts._RoundingMode()
                          }

        p = re.compile('\(?(_ )?(?P<sort>floatingpoint|int|real|bitvector|bitvec|bool|array|roundingmode)\s?\(?(?P<param>\d+)?\)?')

        cvc4sortstr = solver_term.getType().toString().lower()

        match = p.search(cvc4sortstr)

        if not match:
            raise ValueError("Unknown type {}".format(cvc4sortstr))

        assert match.group('sort') in self._str2sort, 'Found {} for string {}'.format(match.group('sort'), cvc4sortstr)

        params = (None,)

        # TODO: Clean up array -- fix so same as other cases
        if match.group('sort') == 'array':
            # get parameterized values
            idxmatch = p.search(cvc4sortstr[match.span(0)[1]:])
            dmatch = p.search(cvc4sortstr[idxmatch.span(0)[1]:])
            idxsort = self._str2sort[idxmatch.group('sort')](idxmatch.group('param'))
            dsort = self._str2sort[dmatch.group('sort')](dmatch.group('param'))
            params = (idxsort, dsort)

        elif 'floatingpoint' in cvc4sortstr:
            # regex not quite right for floatingpoint
            # TODO: Fix regex without breaking other sorts
            sig, exp = cvc4sortstr[cvc4sortstr.find('floatingpoint')+len('floatingpoint '):].replace(")", "").split()
            sig, exp = int(sig), int(exp)
            if sig == -1:
                assert exp == -1

                # this is the result of an operation -- unknown parameters
                # don't give them values
                sig, exp = None, None

            params = (sig, exp)

        elif 'bitvec' in match.group('sort'):
            assert match.group('param'), 'BitVecs must have a width'
            params = (int(match.group('param')),)

        sort = self._str2sort[match.group('sort')](*params)

        # TODO: handle this check more elegantly -- perhaps a lambda in the dict
        extk= -1
        if solver_term.hasOperator():
            cvc4_op = solver_term.getOperator()
            extk = cvc4_op.getKind()

        k = solver_term.getKind()

        if extk == smt._solver.CVC4.BITVECTOR_EXTRACT_OP:
            assert 'cvc4_op' in locals()
            ext_op = cvc4_op.getConstBitVectorExtract()
            op = smt.Extract(ext_op.high, ext_op.low)
        elif k in smt.solver._CVC4Funs.rev:
            enum_op = smt.solver._CVC4Funs.rev[k]
            op = operator(smt, enum_op, func_symbols[enum_op.name])
        elif k in smt.solver._CVC4InvOps:
            enum_op = smt.solver._CVC4InvOps[k]
            op = operator(smt, enum_op, func_symbols[enum_op.name])
        else:
            raise KeyError('{} not a recognized CVC4 enum'.format(k))

        # query children from solver
        children = []
        for c in solver_term.getChildren():
            children.append(CVC4Term(smt, c))

        super().__init__(smt, solver_term, sort, op, children)


    def __repr__(self):
        return self.solver_term.toString()

    def as_int(self):
        if self.sort == self._smt.Int():
            return int(self._value.getConstRational().getDouble())

        elif self.sort.__class__ == self._smt.BitVec:
            return self._value.getConstBitVector().toInteger().toUnsignedInt()

        else:
            raise ValueError('Mismatched sort for request')

    def as_double(self):
        if self.sort == self._smt.Real:
            return self._value.getConstRational().getDouble()
        else:
            raise ValueError

    def as_fraction(self):
        if self.sort != self._smt.Real():
            raise ValueError
        r = self._value.getConstRational()
        return Fraction(r.getNumerator().toSignedInt(),
                        r.getDenominator().toSignedInt())

    def as_bool(self):
        if self.sort != self._smt.Bool():
            raise ValueError

        return self._value.getConstBoolean()

    def as_bitstr(self):
        return self._value.getConstBitVector().toString()

    def as_list(self):
        '''
        Gets value of array as list of tuples in order of store operators
        '''
        if self.sort.__class__ != sorts.Array:
            raise RuntimeError("Cannot call as_list on sort: {}".format(self.sort))

        kvpairs = []
        expr = self.solver_term
        while expr.hasOperator() and expr.getNumChildren() > 0:
            t = expr.getChildren()[1:]  # gets index and value
            # get CVC4Terms
            t = tuple(self._smt.GetValue(CVC4Term(self._smt, x)) for x in t)
            # TODO: Figure out best representation -- boolector uses bitstrings
            t = tuple(x.as_bitstr() if x.sort.__class__ == sorts.BitVec else x.as_int() for x in t)
            kvpairs.append(t)
            expr = expr.getChildren()[0]

        return kvpairs


class Z3Term(TermBase):
    def __init__(self, smt, solver_term):

        sts = solver_term.sort()
        sort = smt.solver._z3Sorts[sts.kind()](sts)

        # TODO: fix for uninterpreted functions
        enum_op = smt.solver._z3Funs2swFuns[solver_term.decl().kind()]
        op = operator(smt, enum_op, func_symbols[enum_op.name])

        # TODO: Find better solution than this
        if enum_op == func_enum.Extract:
            op = smt.Extract(*solver_term.decl().params())

        # create children
        children = []
        for c in solver_term.children():
            children.append(Z3Term(smt, c))

        super().__init__(smt, solver_term, sort, op, children)

    def __repr__(self):
        if self._smt.strict:
            return self.solver_term.sexpr()
        else:
            return self.solver_term.__repr__()

    def as_int(self):
        return self._value.as_long()

    def as_double(self):
        return float(self.value.as_fraction())

    def as_fraction(self):
        return self._value.as_fraction()

    def as_bool(self):
        if self.sort != self._smt.Bool():
            raise ValueError

        return bool(self._value)

    def as_bitstr(self):
        return '{0:b}'.format(int(self._value.as_string())).zfill(self.sort.width)

    def as_list(self):
        '''
        Gets value of array as list of tuples in order of store operators
        '''
        if self.sort.__class__ != sorts.Array:
            raise RuntimeError("Cannot call as_list on sort: {}".format(self.sort))

        kvpairs = []
        expr = self.solver_term
        while len(expr.children()) > 0:
            t = expr.children()[1:]  # gets index and value
            # get Z3Terms
            t = tuple(self._smt.GetValue(Z3Term(self._smt, x)) for x in t)
            # TODO: Figure out best representation -- boolector uses bitstrings
            # but might be nice to know symbolic variable name
            t = tuple(x.as_bitstr() if x.sort.__class__ == sorts.BitVec else x.as_int() for x in t)
            kvpairs.append(t)
            expr = expr.children()[0]

        return kvpairs


class BoolectorTerm(TermBase):
    def __init__(self, smt, solver_term):
        boolector = smt.solver.boolector
        sortmap = {boolector.BoolectorBVNode: lambda st: sorts.BitVec(st.width),
                   boolector.BoolectorConstNode: lambda st: sorts.BitVec(st.width),
                   boolector.BoolectorArrayNode: lambda st: sorts.Array(
                       sorts.BitVec(st.index_width), sorts.BitVec(st.width)),
                   boolector._BoolectorParamNode: lambda st: sorts.BitVec(st.width)}
        sort = sortmap[type(solver_term)](solver_term)
        super().__init__(smt, solver_term, sort)

    def __repr__(self):
        # This isn't the best solution, but boolector's __str__ and __repr__ are not implemented
        return self.solver_term.symbol

    def __str__(self):
        return self.solver_term.symbol

    def as_int(self):
        return int(self._value.assignment, base=2)

    def as_bool(self):
        if self._value.width != 1:
            raise ValueError("Can't interpret BitVec of width > 1 as a bool")

        return bool(self._value.assignment)

    def as_bitstr(self):
        return self._value.assignment

    def as_list(self):
        '''
        Gets value of array as list of tuples in order of store operators
        '''
        if self.sort.__class__ != sorts.Array:
            raise RuntimeError("Cannot call as_list on sort: {}".format(self.sort))
        return self._value.assignment

    @property
    def op(self):
        raise NotImplementedError('Boolector does not support querying the operator of a term.')

    @property
    def children(self):
        raise NotImplementedError('Boolector does not support querying children.')


class WrapperTerm:
    '''
    Holds an arbitrary solver object. Used for special solver constants that can't be combined into arbitrary expressions or just don't fit into the general term structure for some reason
    '''
    def __init__(self, smt, solver_term):
        self._smt = smt
        self._solver_term = solver_term

    @property
    def smt(self):
        return self._smt

    @property
    def solver_term(self):
        return self._solver_term

    def __eq__(self, other):
        return self.solver_term == other.solver_term

    def __ne__(self, other):
        return self.solver_term != other.solver_term


def __bool_fun(*args):
    return sorts.Bool()
