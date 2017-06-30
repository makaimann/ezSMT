from .. import sorts
from .. import functions
from .. import terms
from .. import results
from .solverbase import SolverBase
from fractions import Fraction
from smt_switch.config import config


class CVC4Solver(SolverBase):
    # could also use class name instead of class itself as key
    # probably better for memory reasons?

    def __init__(self, lang='auto'):
        super().__init__()

        # import CVC4
        self.CVC4 = __import__('CVC4')
        # set output language to smt2.5
        if config.strict:
            opts = self.CVC4.Options()
            opts.setOutputLanguage(eval('self.CVC4.OUTPUT_LANG_SMTLIB_V2_5'))
            self._em = self.CVC4.ExprManager(opts)
        else:
            self._em = self.CVC4.ExprManager()
        self._smt = self.CVC4.SmtEngine(self._em)
        self._CVC4Sorts = {sorts.BitVec: self._em.mkBitVectorType,
                           sorts.Int: self._em.integerType,
                           sorts.Real: self._em.realType,
                           sorts.Bool: self._em.booleanType}
        # Note: indexed operators don't index by .func because already reference unindexed function
        self._CVC4Funs = {functions.Extract: self.CVC4.BitVectorExtract,
                          functions.Concat.func: self.CVC4.BITVECTOR_CONCAT,
                          functions.Zero_extend.func: self.CVC4.BITVECTOR_ZERO_EXTEND,
                          functions.Equals.func: self.CVC4.EQUAL,
                          functions.Not.func: self.CVC4.NOT,
                          functions.And.func: self.CVC4.AND,
                          functions.Or.func: self.CVC4.OR,
                          functions.Ite.func: self.CVC4.ITE,
                          functions.Sub.func: self.CVC4.MINUS,
                          functions.Add.func: self.CVC4.PLUS,
                          functions.LT.func: self.CVC4.LT,
                          functions.LEQ.func: self.CVC4.LEQ,
                          functions.GT.func: self.CVC4.GT,
                          functions.GEQ.func: self.CVC4.GEQ,
                          functions.BVAnd.func: self.CVC4.BITVECTOR_AND,
                          functions.BVOr.func: self.CVC4.BITVECTOR_OR,
                          functions.BVXor.func: self.CVC4.BITVECTOR_XOR,
                          functions.BVAdd.func: self.CVC4.BITVECTOR_PLUS,
                          functions.BVSub.func: self.CVC4.BITVECTOR_SUB,
                          functions.BVMul.func: self.CVC4.BITVECTOR_MULT,
                          functions.BVUdiv.func: self.CVC4.BITVECTOR_UDIV,
                          functions.BVUrem.func: self.CVC4.BITVECTOR_UREM,
                          functions.BVShl.func: self.CVC4.BITVECTOR_SHL,
                          functions.BVAshr.func: self.CVC4.BITVECTOR_ASHR,
                          functions.BVLshr.func: self.CVC4.BITVECTOR_LSHR,
                          functions.BVUlt.func: self.CVC4.BITVECTOR_ULT,
                          functions.BVUle.func: self.CVC4.BITVECTOR_ULE,
                          functions.BVUgt.func: self.CVC4.BITVECTOR_UGT,
                          functions.BVUge.func: self.CVC4.BITVECTOR_UGE,
                          functions.BVSlt.func: self.CVC4.BITVECTOR_SLT,
                          functions.BVSle.func: self.CVC4.BITVECTOR_SLE,
                          functions.BVSgt.func: self.CVC4.BITVECTOR_SGT,
                          functions.BVSge.func: self.CVC4.BITVECTOR_SGE,
                          functions.BVNot.func: self.CVC4.BITVECTOR_NOT,
                          functions.BVNeg.func: self.CVC4.BITVECTOR_NEG}
        self._CVC4Results = {sorts.BitVec: results.CVC4BitVecResult,
                             sorts.Int: results.CVC4IntResult,
                             sorts.Real: results.CVC4RealResult,
                             sorts.Bool: results.CVC4BoolResult}

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

        self._CVC4Consts = {sorts.BitVec: create_bv,
                            sorts.Int: create_int,
                            sorts.Real: create_real,
                            sorts.Bool: create_bool}

    def reset(self):
        self._smt.reset()

    def check_sat(self):
        # rely on Assert for now
        # chose this way so user can get assertions, but also aren't added twice
        # for constraint in self.constraints:
        #    self._smt.assertFormula(constraint)
        self.sat = self._smt.checkSat().isSat() == 1
        return self.sat

    def set_logic(self, logicstr):
        self._smt.setLogic(logicstr)

    # TODO: Need to make this more general.
    # I don't think we always create an SExpr from the value...
    # Also need to check if optionstr is a standard option
    def set_option(self, optionstr, value):
        self._smt.setOption(optionstr, self.CVC4.SExpr(value))

    # Note: currently not different than set_option
    def set_nonstandard_option(self, optionstr, value):
        self._smt.setOption(optionstr, self.CVC4.SExpr(value))

    def declare_const(self, name, sort):
        cvc4sort = self._CVC4Sorts[sort.__class__](*sort.params)
        cvc4const = self._em.mkVar(name, cvc4sort)
        const = terms.CVC4Term(self, functions.No_op, cvc4const, [sort])
        return const

    def theory_const(self, sort, value):
        cvc4tconst = self._CVC4Consts[sort.__class__](*(sort.params + (value,)))
        tconst = terms.CVC4Term(self, functions.No_op, cvc4tconst, [sort])
        return tconst

    # if config strict, check arity and don't allow python objects as arguments
    def apply_fun(self, op, *args):

        # commented out while updating functions
        # if config.strict and len(args) < fun.arity['min'] or len(args) > fun.arity['max']:
        #     raise ValueError('In strict mode you must respect function arity:' +
        #                      ' {}: arity = {}'.format(fun, fun.arity))

        cvc4fun = self._CVC4Funs[op.func]
        # handle list argument
        if isinstance(args[0], list):
            args = args[0]

        if config.strict:
            solver_args = [arg.solver_term for arg in args]
        else:
            # find a cvc4 term to infer the sort
            # TODO: make this more robust
            cvc4term = list(filter(lambda x: isinstance(x, terms.CVC4Term), args))[-1]
            solver_args = tuple(map(lambda arg: arg.solver_term
                                    if isinstance(arg, terms.CVC4Term)
                                    else
                                    self.theory_const(cvc4term.sort, arg).solver_term,
                                    args))

        # check if just indexer or needs to be evaluated
        # TODO: handle situation where all args together
        if not isinstance(cvc4fun, int):
            cvc4fun = self._em.mkConst(cvc4fun(*op.args))
        cvc4terms = self._em.mkExpr(cvc4fun, solver_args)
        expr = terms.CVC4Term(self, op, cvc4terms, list(args))
        return expr

    def Assert(self, constraints):
        if isinstance(constraints, list):
            for constraint in constraints:
                sort = getattr(constraint, 'sort', type(constraint))
                # check that sort is bool (could be python bool)
                if sort != bool and sort != sorts.Bool():
                    raise ValueError('Can only assert formulas of sort Bool. ' +
                                     'Received sort: {}'.format(sort))
                self._smt.assertFormula(getattr(constraint, 'solver_term',
                                                self._em.mkBoolConst(constraint)))
        else:
            sort = getattr(constraints, 'sort', type(constraints))
            if sort != bool and sort != sorts.Bool():
                raise ValueError('Can only assert formulas of sort Bool. ' +
                                 'Received sort: {}'.format(sort))
            self._smt.assertFormula(getattr(constraints, 'solver_term',
                                            self._em.mkBoolConst(constraints)))

    def assertions(self):
        # TODO: fix iter error
        # Wanted these to be an iter but CVC4 threw an exception
        return [expr.toString() for expr in self._smt.getAssertions()]

    def get_model(self):
        if self.sat:
            # TODO: Fix this
            return self._smt.getValue
        elif self.sat is not None:
            raise RuntimeError('Problem is unsat')
        else:
            raise RuntimeError('Solver has not been run')

    def get_value(self, var):
        if self.sat:
            return self._CVC4Results[var.sort.__class__](self._smt.getValue(var.solver_term))
        elif self.sat is not None:
            raise RuntimeError('Problem is unsat')
        else:
            raise RuntimeError('Solver has not been run')
