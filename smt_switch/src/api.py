# This file is part of the smt-switch project.
# See the file LICENSE in the top-level source directory for licensing information.

from collections import Sequence
from types import SimpleNamespace

from . import sorts
from . import functions
from . import terms
from . import solvers


def check_solver(f):
    def eval_f(self, *args):
        if self.solver is None:
            raise ValueError('Please set solver before using a solver function')
        else:
            return f(self, *args)

    return eval_f


def check_instance(f):
    def eval_f(self, *terms):
        if isinstance(terms[0], Sequence):
            terms = terms[0]

        for term in terms:
            # if it's a term object, verify that the
            # smt api instance is the same as the one
            # currently being used
            if hasattr(term, '_smt') and term._smt != self:
                raise ValueError('Bad! Mixing terms from different api (smt) instances')

        return f(self, *terms)

    return eval_f


class smt:

    __solver_map = {'CVC4': solvers.CVC4Solver,
                    'Z3': solvers.Z3Solver,
                    'Boolector': solvers.BoolectorSolver}
    __term_map = {solvers.CVC4Solver: terms.CVC4Term,
                  solvers.Z3Solver: terms.Z3Term,
                  solvers.BoolectorSolver: terms.BoolectorTerm}

    __infer_sort = {bool: sorts.Bool(),
                    int: sorts.Int(),
                    float: sorts.Real()}

    def __init__(self, solver_name, strict=False):
        if solver_name not in self.__solver_map:
            raise ValueError('{} is not a supported solver'.format(solver_name))
        self._solver_name = solver_name

        self._solver = self.__solver_map[solver_name](strict)
        self.constraints = []

        # give the instance access to functions
        for f_enum in functions.func_enum:
            op = functions.operator(self, f_enum, functions.func_symbols[f_enum.name])
            setattr(self, f_enum.name, op)

        # give the instance access to sorts
        for s in sorts.__all__:
            setattr(self, s, sorts.__dict__[s])

        self._strict = strict

        # create attributes and SimpleNamespaces for special solver constants
        # these are used for particular tasks, such as rounding in Floating
        # Point solving but do not fit into the general term structure
        if hasattr(self._solver, '_special_consts'):
            for k, v in self._solver._special_consts.items():
                assert isinstance(v, dict), 'Expecting special consts to be <dict str: <dict str: solver_term>>'

                wrapped_consts = {s: terms.WrapperTerm(self, t) for s, t in v.items()}
                NT = SimpleNamespace(**wrapped_consts)
                assert not hasattr(self, k), "Special Const name {} is already an api function".format(k)

                setattr(self, k, NT)

    def ConstructFun(self, fun, *args):
        # partial function evaluation all handled internally
        return fun(*args)

    def ConstructSort(self, s, *args):
        return s(*args)

    @property
    def solver_name(self):
        return self._solver_name

    @property
    def solver(self):
        return self._solver

    @property
    def strict(self):
        return self._strict

    # solver functions

    def Add(self, c):
        ''' Alias for Assert '''
        self.solver.Assert(c)

    def Reset(self):
        self.solver.Reset()

    def CheckSat(self):
        return self.solver.CheckSat()

    @property
    def Sat(self):
        return self.solver.Sat

    def SetLogic(self, logicstr):
        self.solver.SetLogic(logicstr)

    def SetOption(self, optionstr, value):
        self.solver.SetOption(optionstr, value)

    def DeclareFun(self, name, inputsorts, outputsort):
        assert isinstance(inputsorts, Sequence), \
          "Expecting a (possibly empty) list of input sorts"

        if not inputsorts:
            return self.DeclareConst(name, outputsort)

        solverfun = self.solver.DeclareFun(name, inputsorts, outputsort)
        func_info = (name, solverfun)
        uf_fdata = functions.fdata(0, len(inputsorts), len(inputsorts))
        return functions.operator(self, func_info, uf_fdata)

    def DeclareConst(self, name, sort):
        assert isinstance(name, str), 'name parameter should be a string'
        sconst = self.solver.DeclareConst(name, sort)
        return self.__term_map[self.solver.__class__](self,
                                                      sconst)

    def TheoryConst(self, sort, *values):
        values = [v.solver_term if hasattr(v, 'solver_term') else v for v in values]
        stconst = self.solver.TheoryConst(sort, *values)
        return self.__term_map[self.solver.__class__](self,
                                                      stconst)

    @check_instance
    def ApplyFun(self, fun, *args):
        # handle lists of arguments
        if isinstance(args[0], Sequence):
            args = tuple(args[0])

        for arg in args:
            if arg.__class__ is not self.__term_map[self._solver.__class__] and \
               arg.__class__ in self.__term_map.values():  # raw python types are fine
                raise ValueError('Mixing terms with different solvers is not allowed.\n'
                                 'Found a {}, but the solver is {}'.format(arg.__class__,
                                                                           self._solver.__class__))

        ls_term = list(filter(lambda x: hasattr(x, 'solver_term'), args))

        if not ls_term:
            try:
                sort = self.__infer_sort[args[-1].__class__]
            except:
                raise RuntimeError("No smt term arguments and unable to infer argument(s) sort.")
        else:
            sort = ls_term[-1].sort

        if self._strict:
            solver_args = tuple([arg.solver_term for arg in args])

        else:
            solver_args = tuple([arg.solver_term
                                 if hasattr(arg, 'solver_term')
                                 else
                                 self.solver.TheoryConst(sort, arg)
                                 for arg in args])

        if fun.f_type == "builtin":
            s_term = self.solver.ApplyFun(fun.f_id, fun.args, *solver_args)
        elif fun.f_type in {"macro", "uf"}:
            assert len(fun.args) == 0, "Defined function should not have index args"
            s_term = self.solver.ApplyCustomFun(fun.f_id, *solver_args)

        return self.__term_map[self._solver.__class__](self,
                                                       s_term)

    @check_instance
    def Assert(self, *constraints):
        if isinstance(constraints[0], Sequence):
            constraints = tuple(constraints[0])

        for constraint in constraints:
            sort = getattr(constraint, 'sort', type(constraint))

            if sort not in {bool, sorts.Bool(), sorts.BitVec(1)}:
                raise ValueError('Can only assert formulas of sort Bool/BitVec(1). '
                                 'Received sort: {}'.format(sort))

            if hasattr(constraint, 'solver_term'):
                c = constraint.solver_term
            else:
                c = self.solver.TheoryConst(sorts.Bool(), constraint)

            self.solver.Assert(c)

            # add wrapped constraint to solver assertions
            self.constraints.append(constraint)

    @property
    def Assertions(self):
        return self.solver.Assertions()

    def GetModel(self):
        raise NotImplementedError()

    def GetValue(self, var):
        var._value = self.solver.GetValue(var.solver_term)
        return var

    def ToSmt2(self, filename):
        self.solver.ToSmt2(filename)

    def Symbol(self, name, sort):
        solversym = self.solver.Symbol(name, sort)
        term = self.__term_map[self._solver.__class__](self, solversym)
        term._issym = True
        return term

    def DefineFun(self, name, paramlist, fundef):
        solverparamlist = [p.solver_term for p in paramlist]
        sortlist = [p.sort for p in paramlist]
        sortlist.append(fundef.sort)
        solverfun = self.solver.DefineFun(name, sortlist, solverparamlist, fundef.solver_term)
        func_info = (name, solverfun, fundef)
        cfdata = functions.fdata(0, len(paramlist), len(paramlist))
        defined_op = functions.operator(self, func_info, cfdata)
        return defined_op

    def Push(self):
        self.solver.Push()

    def Pop(self):
        self.solver.Pop()
