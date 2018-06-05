# This file is part of the smt-switch project.
# See the file LICENSE in the top-level source directory for licensing information.

from .. import sorts
from ..functions import func_enum
from .solverbase import SolverBase
from fractions import Fraction
from smt_switch.util import reversabledict
from collections import Sequence, namedtuple
import os


class CVC4Solver(SolverBase):
    # could also use class name instead of class itself as key
    # probably better for memory reasons?

    def __init__(self, strict):
        super().__init__(strict)

        # import CVC4
        self.CVC4 = __import__('CVC4')

        opts = self.CVC4.Options()
        opts.setOutputLanguage(self.CVC4.OUTPUT_LANG_SMTLIB_V2_5)
        self._em = self.CVC4.ExprManager(opts)

        self._smt = self.CVC4.SmtEngine(self._em)
        self.temp_file_name = "cvc4-out.smt2"
        self._smt.setOption("dump-to", self.CVC4.SExpr(self.temp_file_name))
        self._smt.setOption("dump", self.CVC4.SExpr("raw-benchmark"))

        self._CVC4Sorts = {sorts.BitVec: self._em.mkBitVectorType,
                           sorts.Int: self._em.integerType,
                           sorts.Real: self._em.realType,
                           sorts.Bool: self._em.booleanType,
                           sorts.Array: self._em.mkArrayType,
                           sorts.FP: self._em.mkFloatingPointType}

        # def create_array_sort(idxsort, dsort):
        #     # get parameterized sorts
        #     cvc4_idxsort = self._CVC4Sorts[idxsort.__class__](*idxsort.params)
        #     cvc4_dsort = self._CVC4Sorts[dsort.__class__](*dsort.params)
        #     return self._em.mkArrayType(cvc4_idxsort, cvc4_dsort)

        # self._CVC4Sorts[sorts.Array] = create_array_sort

        # this attribute is used by an inherited function to translate sorts
        self._tosorts = self._CVC4Sorts

        self._CVC4Funs = \
          reversabledict({func_enum.Extract: self.CVC4.BitVectorExtract,
                          func_enum.Concat: self.CVC4.BITVECTOR_CONCAT,
                          func_enum.ZeroExt: self.CVC4.BITVECTOR_ZERO_EXTEND,
                          func_enum.Equals: self.CVC4.EQUAL,
                          func_enum.Not: self.CVC4.NOT,
                          func_enum.And: self.CVC4.AND,
                          func_enum.Or: self.CVC4.OR,
                          func_enum.Ite: self.CVC4.ITE,
                          func_enum.Sub: self.CVC4.MINUS,
                          func_enum.Add: self.CVC4.PLUS,
                          func_enum.LT: self.CVC4.LT,
                          func_enum.LEQ: self.CVC4.LEQ,
                          func_enum.GT: self.CVC4.GT,
                          func_enum.GEQ: self.CVC4.GEQ,
                          func_enum.BVAnd: self.CVC4.BITVECTOR_AND,
                          func_enum.BVOr: self.CVC4.BITVECTOR_OR,
                          func_enum.BVXor: self.CVC4.BITVECTOR_XOR,
                          func_enum.BVAdd: self.CVC4.BITVECTOR_PLUS,
                          func_enum.BVSub: self.CVC4.BITVECTOR_SUB,
                          func_enum.BVMul: self.CVC4.BITVECTOR_MULT,
                          func_enum.BVUdiv: self.CVC4.BITVECTOR_UDIV,
                          func_enum.BVUrem: self.CVC4.BITVECTOR_UREM,
                          func_enum.BVShl: self.CVC4.BITVECTOR_SHL,
                          func_enum.BVAshr: self.CVC4.BITVECTOR_ASHR,
                          func_enum.BVLshr: self.CVC4.BITVECTOR_LSHR,
                          func_enum.BVUlt: self.CVC4.BITVECTOR_ULT,
                          func_enum.BVUle: self.CVC4.BITVECTOR_ULE,
                          func_enum.BVUgt: self.CVC4.BITVECTOR_UGT,
                          func_enum.BVUge: self.CVC4.BITVECTOR_UGE,
                          func_enum.BVSlt: self.CVC4.BITVECTOR_SLT,
                          func_enum.BVSle: self.CVC4.BITVECTOR_SLE,
                          func_enum.BVSgt: self.CVC4.BITVECTOR_SGT,
                          func_enum.BVSge: self.CVC4.BITVECTOR_SGE,
                          func_enum.BVNot: self.CVC4.BITVECTOR_NOT,
                          func_enum.BVNeg: self.CVC4.BITVECTOR_NEG,
                          func_enum._ApplyUF: self.CVC4.APPLY_UF,
                          func_enum.Select: self.CVC4.SELECT,
                          func_enum.Store: self.CVC4.STORE,
                          func_enum.Distinct: self.CVC4.DISTINCT,
                          func_enum.FPEq: self.CVC4.FLOATINGPOINT_EQ,
                          func_enum.FPAbs: self.CVC4.FLOATINGPOINT_ABS,
                          func_enum.FPNeg: self.CVC4.FLOATINGPOINT_NEG,
                          func_enum.FPAdd: self.CVC4.FLOATINGPOINT_PLUS,
                          func_enum.FPSub: self.CVC4.FLOATINGPOINT_SUB,
                          func_enum.FPMul: self.CVC4.FLOATINGPOINT_MULT,
                          func_enum.FPDiv: self.CVC4.FLOATINGPOINT_DIV,
                          func_enum.FPRem: self.CVC4.FLOATINGPOINT_REM,
                          func_enum.FPFma: self.CVC4.FLOATINGPOINT_FMA,
                          func_enum.FPSqrt: self.CVC4.FLOATINGPOINT_SQRT,
                          func_enum.FPRti: self.CVC4.FLOATINGPOINT_RTI,
                          func_enum.FPMin: self.CVC4.FLOATINGPOINT_MIN,
                          func_enum.FPMax: self.CVC4.FLOATINGPOINT_MAX,
                          func_enum.FPLe: self.CVC4.FLOATINGPOINT_LEQ,
                          func_enum.FPLt: self.CVC4.FLOATINGPOINT_LT,
                          func_enum.FPGe: self.CVC4.FLOATINGPOINT_GEQ,
                          func_enum.FPGt: self.CVC4.FLOATINGPOINT_GT
          })

        # all constants are No_op
        self._CVC4InvOps = {self.CVC4.VARIABLE: func_enum.No_op,
                            self.CVC4.CONST_RATIONAL: func_enum.No_op,
                            self.CVC4.CONST_BITVECTOR: func_enum.No_op,
                            self.CVC4.CONST_BOOLEAN: func_enum.No_op,
                            self.CVC4.BOUND_VARIABLE: func_enum.No_op,
                            # Note: losing info about op of applied function
                            # TODO: see if can extract function definition
                            self.CVC4.APPLY: func_enum.No_op,
                            self.CVC4.BITVECTOR_EXTRACT: func_enum.Extract,
                            self.CVC4.FLOATINGPOINT_FP: func_enum.No_op,
                            self.CVC4.NULL_EXPR: func_enum.No_op}

        # special constants for floating point solver
        # duplicate fenv.h values
        # make available through self._round
        FE_TONEAREST = 0
        FE_DOWNWARD = 0x400
        FE_UPWARD = 0x800
        FE_TOWARDZERO = 0xc00

        self._round = {
            'RNE': self._em.mkVar(self._em.roundingModeType(), FE_TONEAREST),
            'RTN': self._em.mkVar(self._em.roundingModeType(), FE_DOWNWARD),
            'RTP': self._em.mkVar(self._em.roundingModeType(), FE_UPWARD),
            'RTZ': self._em.mkVar(self._em.roundingModeType(), FE_TOWARDZERO),
            'RNA': self._em.mkVar(self._em.roundingModeType(), ((~FE_TONEAREST) & 0x1) | ((~FE_UPWARD) & 0x2) |
                                    ((~FE_DOWNWARD) & 0x4) | ((~FE_TOWARDZERO) & 0x8))
        }

        # set the default
        self._round['default'] = self._round['RNE']

        # The api creates an attribute for each entry in this dictionary,
        # and creates a namedtuple out of each value
        self._special_consts = {'Round': self._round}

        # Theory constant functions
        def create_bv(width, value):
            return self._em.mkConst(self.CVC4.BitVector(width, value))

        def create_int(value):
            return self._em.mkConst(self.CVC4.Rational(value))

        def create_real(value):
            if not isinstance(value, Fraction):
                value = Fraction(value).limit_denominator()
            return self._em.mkConst(self.CVC4.Rational(value.numerator, value.denominator))

        def create_bool(value):
            return self._em.mkBoolConst(value)

        def create_fp(expbits, sigbits, *args):
            if len(args) == 3:
                return self._em.mkExpr(self.CVC4.FLOATINGPOINT_FP, *args)
            elif len(args) == 1:
                assert isinstance(value, Fraction)
                return self._em.mkExpr(self.CVC4.FLOATINGPOINT_FP, self.CVC4.Rational(value.numerator, value.denominator))
            else:
                raise UnimplementedError("Don't have support for other FP instantiation techniques")

        self._CVC4Consts = {sorts.BitVec: create_bv,
                            sorts.Int: create_int,
                            sorts.Real: create_real,
                            sorts.Bool: create_bool,
                            sorts.FP: create_fp}

    def Reset(self):
        self._smt.reset()
        self._smt.setOption("dump-to", self.CVC4.SExpr(self.temp_file_name))
        self._smt.setOption("dump", self.CVC4.SExpr("raw-benchmark"))


    def CheckSat(self):
        # rely on Assert for now
        # chose this way so user can get Assertions, but also aren't added twice
        # for constraint in self.constraints:
        #    self._smt.assertFormula(constraint)
        self.Sat = self._smt.checkSat().isSat() == 1
        return self.Sat

    def SetLogic(self, logicstr):
        self._smt.setLogic(logicstr)

    def SetOption(self, optionstr, value):
        self._smt.setOption(optionstr, self.CVC4.SExpr(value))

    def DeclareFun(self, name, inputsorts, outputsort):
        assert isinstance(inputsorts, Sequence), \
          "Expecting a non-empty list of input sorts"

        cvc4sorts = [self._translate_sorts(sort) for sort in inputsorts]
        outsort = self._translate_sorts(outputsort)

        funtype = self._em.mkFunctionType(cvc4sorts, outsort)
        lam = self._em.mkVar(name, funtype)
        return lam

    def DeclareConst(self, name, sort):
        cvc4sort = self._translate_sorts(sort)
        cvc4const = self._em.mkVar(name, cvc4sort)
        return cvc4const

    def TheoryConst(self, sort, *values):
        cvc4tconst = self._CVC4Consts[sort.__class__](*(sort.params + values))
        return cvc4tconst

    def ApplyFun(self, f_enum, indices, *args):

        if f_enum not in self._CVC4Funs:
            raise NotImplementedError("{} has not been implemented in CVC4 yet".format(f_enum))

        cvc4fun = self._CVC4Funs[f_enum]

        # check if just indexer or needs to be evaluated
        # TODO: handle situation where all args together
        if not isinstance(cvc4fun, int):
            cvc4fun = self._em.mkConst(cvc4fun(*indices))
        cvc4expr = self._em.mkExpr(cvc4fun, args)
        return cvc4expr

    def ApplyCustomFun(self, func, *args):
        '''
           Apply a custom function. Don't need to look up corresponding function
           -- assume func is a CVC4 function.
        '''
        if self._smt.isDefinedFunction(func):
            cvc4expr = self._em.mkExpr(self.CVC4.APPLY, func, *args)
        else:
            cvc4expr = self._em.mkExpr(func, *args)

        return cvc4expr

    def Assert(self, c):
            self._smt.assertFormula(c)

    def Assertions(self):
        # TODO: fix iter error
        # Wanted these to be an iter but CVC4 threw an exception
        return [expr.toString() for expr in self._smt.getAssertions()]

    def GetModel(self):
        if self.Sat:
            # TODO: Fix this
            return self._smt.getValue
        elif self.Sat is not None:
            raise RuntimeError('Problem is unsat')
        else:
            raise RuntimeError('Solver has not been run')

    def GetValue(self, var):
        if self.Sat:
            return self._smt.getValue(var)
        elif self.Sat is not None:
            raise RuntimeError('Problem is unsat')
        else:
            raise RuntimeError('Solver has not been run')

    def ToSmt2(self, filename):
        wd = os.getcwd()
        os.rename(os.getcwd() + "/" + self.temp_file_name, filename)

    def Symbol(self, name, sort):
        cvc4sort = self._CVC4Sorts[sort.__class__](*sort.params)
        return self._em.mkBoundVar(name, cvc4sort)

    def DefineFun(self, name, sortlist, paramlist, fundef):
        cvc4sorts = [self._CVC4Sorts[sort.__class__](*sort.params)
                         for sort in sortlist]
        outsort = cvc4sorts[-1]
        cvc4sorts = cvc4sorts[:-1]
        funtype = self._em.mkFunctionType(cvc4sorts, outsort)
        lam = self._em.mkVar(name, funtype)
        self._smt.defineFunction(lam, paramlist, fundef)
        return lam

    def Push(self):
        self._smt.push()

    def Pop(self):
        self._smt.pop()

    @property
    def Round(self):
        '''
        Returns a namedtuple containing integers encoding the type of Floating Point Rounding

        Intended for use with a solver supporting floating point queries.
        '''
        return self._round
