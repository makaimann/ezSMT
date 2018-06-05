import pytest
from smt_switch import smt
from smt_switch.tests import fp_solvers

def test_basic():
    '''
    Very basic floating point test
    '''

    for name in fp_solvers:
        s = smt(name, strict=False)
        s.SetLogic("QF_FP")

        b0 = s.TheoryConst(s.BitVec(1), 0)
        b200 = s.TheoryConst(s.BitVec(8), 200)
        b468 = s.TheoryConst(s.BitVec(24), 468)

        b152 = s.TheoryConst(s.BitVec(8), 152)
        b42 = s.TheoryConst(s.BitVec(24), 42)

        # TODO: Handle python integers correctly
        # Note: There's a "hidden" bit which makes it 25 instead of 24
        f = s.TheoryConst(s.FP(8, 25), b0, b200, b468)
        f2 = s.TheoryConst(s.FP(8, 25), b0, b152, b42)

        fc = s.DeclareConst("fc", s.FP(8, 25))
        fc2 = s.DeclareConst("fc2", s.FP(8, 25))

        # default rounding mode is RNE
        # used for syntactic sugar like f + f2
        assert s.Round.default == s.Round.RNE

        # can change default with
        # s.Round.default = s.Round.<RNE|RTN|RTP|RTZ|RNA>

        s.Assert(s.FPGt(fc, f + f2))
        s.Assert(s.FPLt(fc2, f - f2))

        s.Assert(s.FPLe(fc, fc2))

        assert not s.CheckSat()

if __name__ == "__main__":
    test_basic()
