# This file is part of the smt-switch project.
# See the file LICENSE in the top-level source directory for licensing information.

from .. import sorts
from .solverbase import SolverBase
from functools import reduce
from ..functions import func_enum
from collections import Sequence
import math


class BoolectorSolver(SolverBase):
    def __init__(self, strict):
        super().__init__(strict)
        
        self.boolector = __import__('boolector')
        self._btor = self.boolector.Boolector()

        # keeping track of Assertions because couldn't figure out
        # how to print a list of Assertions (other than dumping to stdout/a file)
        self._Assertions = []

        self._BoolectorSorts = {sorts.BitVec: self._btor.BitVecSort,
                                sorts.Bool: lambda: self._btor.BitVecSort(1),
                                sorts.Array: self._btor.ArraySort}
        # this attribute is used by an inherited function to translate sorts
        self._tosorts = self._BoolectorSorts
        self._BoolectorFuns = {func_enum.Equals: self._btor.Eq,
                               func_enum.And: self.And,
                               func_enum.Or: self.Or,
                               func_enum.Ite: self._btor.Cond,
                               func_enum.Not: self._btor.Not,
                               func_enum.Extract: self._btor.Slice,
                               func_enum.Concat: self._btor.Concat,
                               func_enum.BVAnd: self._btor.And,
                               func_enum.BVOr: self._btor.Or,
                               func_enum.BVXor: self._btor.Xor,
                               func_enum.BVAdd: self._btor.Add,
                               func_enum.BVSub: self._btor.Sub,
                               func_enum.BVMul: self._btor.Mul,
                               func_enum.BVUdiv: self._btor.Udiv,
                               func_enum.BVUrem: self._btor.Urem,
                               func_enum.BVShl: lambda bv, shift: bv << self.__shift_process(bv, shift),
                               func_enum.BVAshr: lambda bv, shift: self._btor.Sra(bv, self.__shift_process(bv, shift)),
                               func_enum.BVLshr: lambda bv, shift: bv >> self.__shift_process(bv,shift),
                               func_enum.BVUlt: self._btor.Ult,
                               func_enum.BVUle: self._btor.Ulte,
                               func_enum.BVUgt: self._btor.Ugt,
                               func_enum.BVUge: self._btor.Ugte,
                               func_enum.BVSlt: self._btor.Slt,
                               func_enum.BVSle: self._btor.Slte,
                               func_enum.BVSgt: self._btor.Sgt,
                               func_enum.BVSge: self._btor.Sgte,
                               func_enum.BVNot: self._btor.Not,
                               func_enum.BVNeg: self._btor.Neg,
                               func_enum.Select: self._btor.Read,
                               func_enum.Store: self._btor.Write}

        self._BoolectorConsts = {sorts.BitVec: self._btor.Const,
                                 sorts.Bool: self._btor.Const}
        # Note: Boolector does not distinguish between Bools and (_ BitVec 1)
        #       so smt_switch is not either (specifically for Boolector)
        # self._BoolectorResults = {sorts.BitVec: results.BoolectorBitVecResult,
        #                           sorts.Bool: results.BoolectorBitVecResult}
        self._BoolectorOptions = {'produce-models': self.boolector.BTOR_OPT_MODEL_GEN,
                                  'random-seed': self.boolector.BTOR_OPT_SEED,
                                  'incremental': self.boolector.BTOR_OPT_INCREMENTAL,
                                  'fun:preprop': self.boolector.BTOR_OPT_FUN_PREPROP,
                                  'prop:nprops': self.boolector.BTOR_OPT_PROP_NPROPS}

        # am I missing any?
        self._BoolectorLogics = ['QF_BV', 'QF_ABV', 'QF_UFBV', 'QF_AUFBV']

    def Reset(self):
        self.__init__(self.strict)

    def CheckSat(self):
        if self._btor.Sat() == self._btor.SAT:
            self.Sat = True
        else:
            self.Sat = False
        return self.Sat

    def SetLogic(self, logicstr):
        if logicstr not in self._BoolectorLogics:
            raise ValueError('Boolector does not support {} '.format(logicstr) +
                             'If you believe this is incorrect, please contact a ' +
                             'developer or modify the class yourself (see _BoolectorLogics)')

    def SetOption(self, optionstr, value):
        if optionstr in self._BoolectorOptions:
            self._btor.Set_opt(self._BoolectorOptions[optionstr], bool(value))
        else:
            raise RuntimeError("Unrecognized option: {}".format(optionstr))

    def DeclareFun(self, name, inputsorts, outputsort):
        assert isinstance(inputsorts, Sequence), \
          "Expecting a non-empty list of input sorts"

        btorisorts = [self._translate_sorts(sort)
                          for sort in inputsorts]

        btorosort = self._translate_sorts(outputsort)
        _funsort = self._btor.FunSort(btorisorts, btorosort)
        return self._btor.UF(_funsort)

    def DeclareConst(self, name, sort):
        btorsort = self._translate_sorts(sort)

        if sort.__class__ == sorts.Array:
            btorconst = self._btor.Array(btorsort, name)
        else:
            btorconst = self._btor.Var(btorsort, name)
        return btorconst

    def TheoryConst(self, sort, value):
        btortconst = self._BoolectorConsts[sort.__class__](*((value,) + sort.params))
        return btortconst

    def ApplyFun(self, f_enum, indices, *args):
        if f_enum not in self._BoolectorFuns:
            raise NotImplementedError("{} has not been implemented in Boolector yet".format(f_enum))
        btor_expr = self._BoolectorFuns[f_enum](*(args + indices))
        return btor_expr

    def ApplyCustomFun(self, func, *args):
        '''
           Apply a custom function. Don't need to look up corresponding function
           -- assume func is a Boolector function.
        '''
        btor_expr = self._btor.Apply(list(args), func)
        return btor_expr

    def Assert(self, c):
        self._btor.Assert(c)

    def Assertions(self):
        return self._Assertions

    def GetModel(self):
        if self.Sat:
            return self._btor.Print_model()
        elif self.Sat is not None:
            raise RuntimeError('Problem is unsat')
        else:
            raise RuntimeError('Solver has not been run')

    def GetValue(self, var):
        if self.Sat:
            # The value will be wrapped at the api level
            return var
        elif self.Sat is not None:
            raise RuntimeError('Problem is unsat')
        else:
            raise RuntimeError('Solver has not been run')

    def ToSmt2(self, filename):
        self._btor.Dump(format="smt2", outfile=filename)

    def Symbol(self, name, sort):
        btorsort = self._translate_sorts(sort)
        btorsym = self._btor.Param(btorsort, name)
        return btorsym

    def DefineFun(self, name, sortlist, paramlist, fundef):
        return self._btor.Fun(paramlist, fundef)

    def Push(self):
        raise NotImplementedError

    def Pop(self):
        raise NotImplementedError

    # extra functions specific to Boolector
    # And requires exactly two arguments in Boolector.
    # creating a reduction for ease of use
    def And(self, *args):
        if isinstance(args[0], list):
            args = args[0]

        result = reduce(lambda x, y: self._btor.And(x, y), args)
        return result

    def Or(self, *args):
        if isinstance(args[0], list):
            args = args[0]

        result = reduce(lambda x, y: self._btor.Or(x, y), args)
        return result

    def __shift_process(self, bv, shift):
        if not isinstance(shift, int):
            if hasattr(shift, 'bits'):
                shift = int(shift.bits, base=2)
            else:
                # it's symbolic and Boolector wants the log width bitvec for shifting
                w = math.ceil(math.log2(bv.width))
                # add an extra assertion which gives same performance as other solvers
                self._btor.Assert(self._btor.Or(shift[:w] == 0, bv == 0))
                shift = shift[w-1:0]
        return shift
