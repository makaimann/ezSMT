from .. import sorts
from .. import functions
from .. import terms
from .. import results
from .solverbase import SolverBase
from smt_switch.config import config
from functools import reduce
from math import ceil, log2


class BoolectorSolver(SolverBase):
    def __init__(self):
        self.boolector = __import__('boolector')
        self._btor = self.boolector.Boolector()
        # not able to reset without this --> not the best for performance
        # is there another way?
        # didn't seem to help
        # self._btor.Set_opt(self.boolector.BTOR_OPT_INCREMENTAL, 1)
        
        # keeping track of assertions because couldn't figure out
        # how to print a list of assertions (other than dumping to stdout/a file)
        self._assertions = []

        self._BoolectorSorts = {sorts.BitVec: self._btor.BitVecSort,
                                sorts.Bool: lambda: self._btor.BitVecSort(1)}
        self._BoolectorFuns = {functions.Equals: self._btor.Eq,
                               functions.And: self.And,
                               functions.Or: self.Or,
                               functions.Ite: self._btor.Cond,
                               functions.Not: self._btor.Not,
                               functions.extract: self._btor.Slice,
                               functions.concat: self._btor.Concat,
                               functions.bvand: self._btor.And,
                               functions.bvor: self._btor.Or,
                               functions.bvxor: self._btor.Xor,
                               functions.bvadd: self._btor.Add,
                               functions.bvsub: self._btor.Sub,
                               functions.bvmul: self._btor.Mul,
                               functions.bvudiv: self._btor.Udiv,
                               functions.bvurem: self._btor.Urem,
                               # Boolector doesn't follow smt lib for shifts and requires that
                               # bv << s has s.width == log2(bv.width) (with appropriate ceilings)
                               # However, it does infer the widths if pass an int, so just using int
                               functions.bvshl: lambda bv, s: \
                                                self._btor.Sll(bv, int(s.bits, base=2) if hasattr(s, 'bits') else self._btor.Const(s, ceil(log2(bv.width)))),
                               functions.bvashr: lambda bv, s: \
                                                 self._btor.Sra(bv, int(s.bits, base=2) if hasattr(s, 'bits') else self._btor.Const(s, ceil(log2(bv.width)))),
                               functions.bvlshr: lambda bv, s: \
                                                 self._btor.Srl(bv, int(s.bits, base=2) if hasattr(s, 'bits') else self._btor.Const(s, ceil(log2(bv.width)))),
                               functions.bvult: self._btor.Ult,
                               functions.bvule: self._btor.Ulte,
                               functions.bvugt: self._btor.Ugt,
                               functions.bvuge: self._btor.Ugte,
                               functions.bvslt: self._btor.Slt,
                               functions.bvsle: self._btor.Slte,
                               functions.bvsgt: self._btor.Sgt,
                               functions.bvsge: self._btor.Sgte,
                               functions.bvnot: self._btor.Not,
                               functions.bvneg: self._btor.Neg}

        self._BoolectorConsts = {sorts.BitVec: self._btor.Const,
                                 sorts.Bool: self._btor.Const}
        # Note: Boolector does not distinguish between Bools and (_ BitVec 1)
        #       so smt_switch is not either (specifically for Boolector)
        self._BoolectorResults = {sorts.BitVec: results.BoolectorBitVecResult,
                                  sorts.Bool: results.BoolectorBitVecResult}
        self._BoolectorOptions = {'produce-models': self.boolector.BTOR_OPT_MODEL_GEN}

        # am I missing any?
        self._BoolectorLogics = ['QF_BV', 'QF_ABV']

    def reset(self):
        self.__init__()

    def check_sat(self):
        if self._btor.Sat() == self._btor.SAT:
            self.sat = True
        else:
            self.sat = False
        return self.sat

    def set_logic(self, logicstr):
        if logicstr not in self._BoolectorLogics:
            raise ValueError('Boolector does not support {} '.format(logicstr) +
                             'If you believe this is incorrect, please contact a ' +
                             'developer or modify the class yourself (see _BoolectorLogics)')

    def set_option(self, optionstr, value):
        if optionstr in self._BoolectorOptions:
            self._btor.Set_opt(self._BoolectorOptions[optionstr], bool(value))

    def set_nonstandard_option(self, optionstr, value):
        self._btor.Set_opt(eval('boolector.{}'.format(optionstr)), value)

    def declare_const(self, name, sort):
        btorsort = self._BoolectorSorts[sort.__class__](*sort.params)
        btorconst = self._btor.Var(btorsort, name)
        const = terms.BoolectorTerm(self, functions.No_op, btorconst, sort, [])
        return const

    def theory_const(self, sort, value):
        btortconst = self._BoolectorConsts[sort.__class__](*((value,) + sort.params))
        tconst = terms.BoolectorTerm(self, functions.No_op, btortconst, sort, [])
        return tconst

    def apply_fun(self, fun, *args):
        if config.strict and len(args) < fun.arity['min'] or len(args) > fun.arity['max']:
            raise ValueError('In strict mode you must respect function arity:' +
                             ' {}: arity = {}'.format(fun, fun.arity))
        # handle list argument
        if isinstance(args[0], list):
            args = args[0]

        solver_args = tuple(getattr(arg, 'solver_term', arg) for arg in args)
        btor_expr = self._BoolectorFuns[fun.__class__](*(solver_args + fun.params))
        expr = terms.BoolectorTerm(self, fun, btor_expr, fun.osort(*args), list(args))
        return expr

    def Assert(self, constraints):
        if isinstance(constraints, list):
            for constraint in constraints:
                if constraint.sort != sorts.Bool():
                    raise ValueError('Can only assert formulas of sort Bool. ' +
                                     'Received sort: {}'.format(constraint.sort))
                self._btor.Assert(constraint.solver_term)
                # for now adding raw assertion to match other solvers
                # in the future add the wrapped assertion
                self._assertions.append(constraint.solver_term)
        else:
            if constraints.sort != sorts.Bool():
                raise ValueError('Can only assert formulas of sort Bool. ' +
                                 'Received sort: {}'.format(constraints.sort))
            self._btor.Assert(constraints.solver_term)
            # for now adding raw assertion to match other solvers
            # in the future add the wrapped assertion
            self._assertions.append(constraints.solver_term)

    def assertions(self):
        return self._assertions

    def get_model(self):
        if self.sat:
            return self._btor.Print_model()
        elif self.sat is not None:
            raise RuntimeError('Problem is unsat')
        else:
            raise RuntimeError('Solver has not been run')

    def get_value(self, var):
        if self.sat:
            return self._BoolectorResults[var.sort.__class__](var.solver_term)
        elif self.sat is not None:
            raise RuntimeError('Problem is unsat')
        else:
            raise RuntimeError('Solver has not been run')

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
