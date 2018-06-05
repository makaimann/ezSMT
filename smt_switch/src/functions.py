# This file is part of the smt-switch project.
# See the file LICENSE in the top-level source directory for licensing information.

import sys
import enum
from collections import OrderedDict, Sequence
from functools import partial
from ..util import namedtuple_with_defaults


fdata = namedtuple_with_defaults('fdata', 'num_indices, min_arity, max_arity, custom')


# special definitions for And/Or
# this is just to support the And([]) --> True, Or([])-->False cases
def _And(*args):
    '''
       Custom and function defined for And([]) --> True, and And(x) --> x

    '''

    if len(args) == 0:
        return True

    elif len(args) == 1:
        return args[0]

    else:
        raise ValueError('Custom And should not be called with >= 2 args')


def _Or(*args):

    if len(args) == 0:
        return False

    elif len(args) == 1:
        return args[0]

    else:
        raise ValueError('Custom Or should not be called with >= 2 args')


# Use strings here so that enums are automatically generated
# if used enum here, would have to write function twice
# once in enum and once to connect with data

# make it an OrderedDict so that enum values are always the same
func_symbols = OrderedDict([('And', fdata(0, 2, sys.maxsize, _And)),
                            ('Or', fdata(0, 2, sys.maxsize, _Or)),
                            ('Equals', fdata(0, 2, 2)),
                            ('Not', fdata(0, 1, 1)),
                            ('Ite', fdata(0, 3, 3)),
                            ('Sub', fdata(0, 2, 2)),
                            ('Add', fdata(0, 2, sys.maxsize)),
                            ('LT', fdata(0, 2, 2)),
                            ('GT', fdata(0, 2, 2)),
                            ('LEQ', fdata(0, 2, 2)),
                            ('GEQ', fdata(0, 2, 2)),
                            ('Extract', fdata(2, 1, 1)),
                            ('Concat', fdata(0, 2, 2)),
                            ('ZeroExt', fdata(0, 2, 2)),
                            ('BVAnd', fdata(0, 2, 2)),
                            ('BVOr', fdata(0, 2, 2)),
                            ('BVXor', fdata(0, 2, 2)),
                            ('BVAdd', fdata(0, 2, 2)),
                            ('BVSub', fdata(0, 2, 2)),
                            ('BVMul', fdata(0, 2, 2)),
                            ('BVUdiv', fdata(0, 2, 2)),
                            ('BVUrem', fdata(0, 2, 2)),
                            ('BVShl', fdata(0, 2, 2)),
                            ('BVAshr', fdata(0, 2, 2)),
                            ('BVLshr', fdata(0, 2, 2)),
                            ('BVUlt', fdata(0, 2, 2)),
                            ('BVUle', fdata(0, 2, 2)),
                            ('BVUgt', fdata(0, 2, 2)),
                            ('BVUge', fdata(0, 2, 2)),
                            ('BVSlt', fdata(0, 2, 2)),
                            ('BVSle', fdata(0, 2, 2)),
                            ('BVSgt', fdata(0, 2, 2)),
                            ('BVSge', fdata(0, 2, 2)),
                            ('BVNot', fdata(0, 1, 1)),
                            ('BVNeg', fdata(0, 1, 1)),
                            ('Select', fdata(0, 2, 2)),
                            ('Store', fdata(0, 3, 3)),
                            ('No_op', fdata(0, 0, 0)),
                            ('_ApplyUF', fdata(0, 1, sys.maxsize)),
                            ('Distinct', fdata(0, 2, sys.maxsize)),
                            ('FPEq', fdata(0, 2, 2)),
                            ('FPAbs', fdata(0, 1, 1)),
                            ('FPAdd', fdata(0, 2, 2)),
                            ('FPSub', fdata(0, 2, 2)),
                            ('FPMul', fdata(0, 2, 2)),
                            ('FPDiv', fdata(0, 2, 2)),
                            ('FPRem', fdata(0, 2, 2)),
                            ('FPFma', fdata(0, 4, 4)),
                            ('FPSqrt', fdata(0, 2, 2)),
                            ('FPRti', fdata(0, 2, 2)),
                            ('FPMin', fdata(0, 2, 2)),
                            ('FPMax', fdata(0, 2, 2)),
                            ('FPLt', fdata(0, 2, 2)),
                            ('FPLe', fdata(0, 2, 2)),
                            ('FPGt', fdata(0, 2, 2)),
                            ('FPGe', fdata(0, 2, 2)),
                            ('FPNeg', fdata(0, 1, 1))])

# generate enums for each of these function symbols
func_d = dict()

for fname, i in zip(func_symbols.keys(), range(0, len(func_symbols))):
    func_d[fname] = i

func_enum = enum.Enum('func_enum', func_d)

# to make it iterable
func_enum.__order__ = func_symbols.keys()


class operator:
    '''
       Class that wraps all functions, builtin or defined.

       Allows for partial evaluations

       _gen_operator ensures that the partial evaluations are only for the number
       of indexes in an indexed operator (normal operators have num_index == 0)

       e.g. bvult can not be partially evaluated except with 0 arguments (because it is not indexed)
            on the other hand, extract can be partially evaluated with it's high and low bits

            ex4_2 = functions.extract(4, 2)
            ex4_2(bv)

            is equivalent to:

            functions.extract(4, 2, bv)

            ex4_2 == functions.extract(4, 2) will return True
    '''

    def __init__(self, smt, func_info, fdata, *args, **kwargs):
        self._smt = smt
        self._f_imp = None
        
        if issubclass(func_info.__class__, enum.Enum):
            self._fname = func_info.name
            self._f_id = func_info
            self._f_type = "builtin"
        elif isinstance(func_info, tuple):
            assert len(func_info) in {2, 3}, \
              "Expecting function to be (name, solver object) " + \
              "with a third parameter for the implementation if " + \
              "it's a define-fun macros"
            self._fname = func_info[0]
            self._f_id = func_info[1]
            self._f_type = "uf"
            if len(func_info) == 3:
                self._f_imp = func_info[2]
                self._f_type = "macro"
        self._fdata = fdata
        self._args = args
        self._keywords = kwargs

    def __eq__(self, other):
        return self._fname == other._fname and self._args == other._args \
                               and self._keywords == other._keywords

    def __ne__(self, other):
        return self._fname != other._fname or self._args != other._args \
                               or self._keywords != other._keywords

    @property
    def fname(self):
        return self._fname

    @property
    def f_id(self):
        return self._f_id

    @property
    def f_type(self):
        return self._f_type

    @property
    def args(self):
        return self._args

    @property
    def keywords(self):
        return self._p.keywords

    def __repr__(self):
        return '<operator: {}, {} {}>'.format(self._fname, self._args, self._keywords)

    def __call__(self, *args, **kwargs):
        if args and isinstance(args[0], Sequence):
            args = args[0]

        if len(self._args) == 0 and len(args) == self._fdata.num_indices:

            # check for custom behavior
            if self._fdata.num_indices == 0 and self._fdata.custom and not self._smt.strict:
                return self._fdata.custom(*args)

            else:
                return operator(self._smt, self._f_id, self._fdata, *args, **kwargs)

        elif len(self._args) == self._fdata.num_indices and len(args) >= self._fdata.min_arity:
            if self._smt.strict and len(args) > self._fdata.max_arity:
                raise ValueError('In strict mode and received {} args when max arity = '
                                 .format(len(args), fdata.max_arity))

            return self._smt.ApplyFun(self, *args, **kwargs)

        elif len(args) >= self._fdata.num_indices + self._fdata.min_arity:
            if self._smt.strict and len(args) - self._fdata.num_indices > self._fdata.max_arity:
                raise ValueError('In strict mode and received {} function indices and' +
                                 ' {} args when max arity = '
                                 .format(self._fdata.num_indices,
                                         len(args) - self._fdata.num_indices, fdata.max_arity))

            # always pass an operator with the minumum number of arguments
            # this is for CVC4 to construct the function
            op = operator(self._smt, self._f_id, self._fdata,
                          *args[:self._fdata.num_indices])

            args = args[self._fdata.num_indices:]

            return self._smt.ApplyFun(op, *args, **kwargs)

        else:
            # check for custom behaviour
            if self._fdata.custom and not self._smt.strict:
                return self._fdata.custom(*args, **kwargs)

            elif fdata.num_indices == 0:
                # non-indexed operator
                raise ValueError('Expected {} inputs to operator but received {}'
                                 .format(fdata.min_arity, len(args)))
            else:
                raise ValueError('Undefined behaviour for {}{}'
                                 .format(self, args))

    def __hash__(self):
        return (self._fname, self._args).__hash__()
