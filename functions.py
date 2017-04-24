from abc import ABCMeta, abstractmethod
from math import inf
from functools import reduce
import inspect
import sorts
import terms
import smtutils
import config


class FunctionBase(metaclass=ABCMeta):
    def __init__(self, arity, usage):
        self._arity = arity
        self._usage = usage

    @property
    def arity(self):
        return self._arity

    @property
    def usage(self):
        return self._usage

    @property
    def params(self):
        '''
            Holds the parameters needed to apply the function.
            Ex// (_ extract 12 6)
            Functions with nontrivial params overload this property
        '''
        return ()

    @abstractmethod
    def osort(self, *args):
        pass

    def __call__(self, *args):
        if config.strict:
            raise ValueError('Functions are not callable in strict mode.' +
                            ' Use solver.apply_fun(fun, *args)')
        # handle list argument
        if args and isinstance(args[0], list):
            args = args[0]

        if args:
            s_terms = list(filter(lambda arg: issubclass(arg.__class__, terms.TermBase), args))
            if not s_terms:
                raise ValueError('There needs to be at least one argument of type [Solver Name]Term')
            return s_terms[0].solver.apply_fun(self, *args)
        else:
            raise ValueError('Incorrect number of arguments for' +
                             'function: {}'.format(self.__class__.__name__))

    def __repr__(self):
        return self.__class__.__name__

    def __eq__(self, other):
        '''
           Functions are defined by name and params only
        '''
        return self.__class__ == other.__class__ and self.params == other.params


class No_op(FunctionBase):
    arity = {'min': 0,
             'max': 0}

    def __init__(self):
        super().__init__(self.arity, 'No_op')

    def osort(self, *args):
        if len(args) == 0:
            raise ValueError('No_op is used when constructing constants. ' +
                             'Therefore its output sort is parameterized by a Term.' +
                             'Need to provide an argument to determine output sort')
        else:
            return args[0].sort


class Equals(FunctionBase):
    arity = {'min': 2,
             'max': 2}

    def __init__(self):
        super().__init__(self.arity, '(= arg1 arg2)')

    def osort(self, *args):
        return sorts.Bool()


class Not(FunctionBase):
    arity = {'min': 1,
             'max': 1}

    def __init__(self):
        super().__init__(self.arity, '(not formula)')

    def osort(self, *args):
        return sorts.Bool()


class And(FunctionBase):
    arity = {'min': 2,
             'max': inf}

    def __init__(self):
        super().__init__(self.arity, '(and args)')

    def osort(self, *args):
        return sorts.Bool()

    # Overloading callable FunctionBase
    def __call__(self, *args):
        if config.strict:
            raise ValueError('Functions are not callable in strict mode. ' +
                             'Use solver.apply_fun(fun, *args)')

        if args and isinstance(args[0], list):
            args = args[0]

        # With strict=False, (and arg1) --> arg1, (and ) --> True
        if len(args) > 1:
            return args[0].solver.apply_fun(self, *args)
        elif len(args) == 1:
            return args[0]
        else:
            return True


class Or(FunctionBase):
    arity = {'min': 2,
             'max': inf}

    def __init__(self):
        super().__init__(self.arity, '(or args)')

    def osort(self, *args):
        return sorts.Bool()

    # Overloading callable FunctionBase
    def __call__(self, *args):
        if config.strict:
            raise ValueError('Functions are not callable in strict mode. ' +
                             'Use solver.apply_fun(fun, *args)')
        if args and isinstance(args[0], list):
            args = args[0]

        # With strict=False, (and arg1) --> arg1, (and ) --> True
        if len(args) > 1:
            return args[0].solver.apply_fun(self, *args)
        elif len(args) == 1:
            return args[0]
        else:
            return False


class Ite(FunctionBase):
    arity = {'min': 3,
             'max': 3}

    def __init__(self):
        super().__init__(self.arity, '(ite cond arg1 arg2)')

    def osort(self, *args):
        if len(args) != 3:
            raise ValueError(self.__class__name +
                             '\'s output sort is parameterized by its arguments. ' +
                             'Need all three inputs to determine output sort.')

        arg_sorts = smtutils.sorts_list(args)

        # TODO: check for consistent output sort
        if not reduce(lambda x, y: x and y, arg_sorts[1:]):
            raise ValueError('Ite needs to have a consistent output sort. ' +
                             'Received {} and {}'.format(args[1].sort, args[2].sort))
        ite_sorts = list(filter(lambda arg: arg is not None, arg_sorts[1:]))
        if not ite_sorts:
            raise ValueError('Can\'t determine output sort based on inputs {} and {}'.format(args[1], args[2]))
        return ite_sorts[0]


class Sub(FunctionBase):
    arity = {'min': 2,
             'max': 2}

    def __init__(self):
        super().__init__(self.arity, '(- arg1 arg2)')

    def osort(self, *args):
        if len(args) == 0:
            raise ValueError(self.__class__name +
                             '\'s output sort is parameterized by its arguments. ' +
                             'Need an argument to determine output sort.')
        return args[0].sort


class Plus(FunctionBase):
    arity = {'min': 2,
             'max': inf}

    def __init__(self):
        super().__init__(self.arity, '(+ arg1 arg2)')

    def osort(self, *args):
        if len(args) == 0:
            raise ValueError(self.__class__name +
                             '\'s output sort is parameterized by its arguments. ' +
                             'Need an argument to determine output sort.')
        return args[0].sort


class LT(FunctionBase):
    arity = {'min': 2,
             'max': 2}

    def __init__(self):
        super().__init__(self.arity, '(< arg1 arg2)')

    def osort(self, *args):
        return sorts.Bool()


class LEQ(FunctionBase):
    arity = {'min': 2,
             'max': 2}

    def __init__(self):
        super().__init__(self.arity, '(<= arg1 arg2)')

    def osort(self, *args):
        return sorts.Bool()


class GT(FunctionBase):
    arity = {'min': 2,
             'max': 2}

    def __init__(self):
        super().__init__(self.arity, '(> arg1 arg2)')

    def osort(self, *args):
        return sorts.Bool()


class GEQ(FunctionBase):
    arity = {'min': 2,
             'max': 2}

    def __init__(self):
        super().__init__(self.arity, '(>= arg1 arg2)')

    def osort(self, *args):
        return sorts.Bool()


def declare_fun(identifier, *args):
    if isinstance(identifier, str):
        if identifier[0] == '(':
            # TODO: Parse S expression
            raise NotImplementedError
        else:
            return eval(identifier)(*args)
    elif inspect.isclass(identifier):
        return identifier(*args)
    else:
        raise ValueError('Expected [str | Sort] and received {}.'.format(type(identifier)))


#################### Bit Vector Operations #################################################

class extract(FunctionBase):
    arity = {'min': 1,
             'max': 1}

    def __init__(self, ub, lb):
        super().__init__(self.arity, '(extract BitVec)')
        self._ub = ub
        self._lb = lb

    @property
    def ub(self):
        return self._ub

    @property
    def lb(self):
        return self._lb

    @property
    def width(self):
        return self._ub - self._lb + 1

    @property
    def params(self):
        return (self._ub, self._lb)

    def osort(self, *args):
        return sorts.BitVec(self.width)


class _bvbinops(FunctionBase):
    '''
       A base class for all BitVector operations that take two arguments
    '''
    arity = {'min': 2,
             'max': 2}

    def __init__(self):
        super().__init__(self.arity, '({} (_ BitVec m) (_ BitVec m) (_ BitVec m))'.format(self.__class__.__name__))

    def osort(self, *args):
        arg_sorts = smtutils.sorts_list(args)
        if not reduce(lambda x, y: x and y, arg_sorts):
            raise ValueError('bvadd requires consistent sorts')
        else:
            return arg_sorts[0]


class bvand(_bvbinops):
    def __init__(self):
        super().__init__()


class bvor(_bvbinops):
    def __init__(self):
        super().__init__()


class bvadd(_bvbinops):
    def __init__(self):
        super().__init__()


class bvmul(_bvbinops):
    def __init__(self):
        super().__init__()


class bvudiv(_bvbinops):
    def __init__(self):
        super().__init__()


class bvurem(_bvbinops):
    def __init__(self):
        super().__init__()


class bvshl(_bvbinops):
    def __init__(self):
        super().__init__()


class bvlshr(_bvbinops):
    def __init__(self):
        super().__init__()


class _bvunops(FunctionBase):
    '''
       A base class for unary binary functions
    '''
    arity = {'min': 1,
             'max': 1}
    
    def __init__(self):
        super().__init__(self.arity, '({} (_ BitVec m) (_ BitVec m))')

    def osort(self, *args):
        if len(args) != 1:
            raise ValueError('Incorrect number of arguments to unary operator {}'.format(self.__class__.__name__))

        return args[0].sort


class bvnot(_bvunops):
    def __init__(self):
        super().__init__()


class bvneg(_bvunops):
    def __init__(self):
        super().__init__()
