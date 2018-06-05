# This file is part of the smt-switch project.
# See the file LICENSE in the top-level source directory for licensing information.

from abc import ABCMeta, abstractmethod
import inspect


__all__ = ['BitVec', 'Int', 'Real', 'Bool', 'Array', 'FP', '_RoundingMode']

class SortBase(metaclass=ABCMeta):
    @abstractmethod
    def __init__(self, sexpr, children):
        self._sexpr = sexpr
        self._children = children
        self._indexedID = None

    @property
    def sexpr(self):
        return self._sexpr

    @property
    def children(self):
        return self._children

    @property
    def params(self):
        return ()

    def __repr__(self):
        return self._sexpr

    def __eq__(self, other):
        return isinstance(other, type(self)) and self._sexpr == other.sexpr

    def __ne__(self, other):
        return not isinstance(other, type(self)) or not self._sexpr == other.sexpr

    def __hash__(self):
        return hash(self._sexpr)


class BitVec(SortBase):
    def __init__(self, width):
        super().__init__('(_ BitVec {})'.format(width), [])
        self._width = width

    @property
    def width(self):
        return self._width

    @property
    def params(self):
        return (self._width,)


class Int(SortBase):
    def __init__(self):
        super().__init__('Int', [])


class Real(SortBase):
    def __init__(self):
        super().__init__('Real', [])


class Bool(SortBase):
    def __init__(self):
        super().__init__('Bool', [])


class Array(SortBase):
    def __init__(self, idxsort, dsort):
        super().__init__('(Array {} {})'.format(idxsort, dsort), [])
        self._idxsort = idxsort
        self._dsort = dsort

    @property
    def idxsort(self):
        return self._idxsort

    @property
    def dsort(self):
        return self._dsort

    @property
    def params(self):
        return (self._idxsort, self._dsort)


class FP(SortBase):
    ''' Floating Point sort '''
    def __init__(self, expbits, sigbits):
        super().__init__('(FP {} {})'.format(expbits, sigbits), [])
        self._expbits = expbits
        self._sigbits = sigbits

    @property
    def expbits(self):
        return self._expbits

    @property
    def sigbits(self):
        return self._sigbits

    @property
    def params(self):
        return (self._expbits, self._sigbits)

    def __eq__(self, other):
        # Need None parameters to match with anything
        return isinstance(other, type(self)) and \
               ((self.params[0] == other.params[0]) or (None in (self.params[0], other.params[0]))) and \
               ((self.params[1] == other.params[1]) or (None in (self.params[1], other.params[1])))

    def __ne__(self, other):
        # Need None parameters to match with anything
        return not self.__eq__(other)


class _RoundingMode(SortBase):
    '''
    RoundingMode for FloatingPoint
    Should never need to instantiate this as a user
    '''
    def __init__(self):
        super().__init__('RoundingMode', [])
