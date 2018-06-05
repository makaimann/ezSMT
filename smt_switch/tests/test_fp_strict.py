import pytest
from smt_switch import smt
from smt_switch.tests import fp_solvers

def test_basic():
    '''
    Very basic floating point test
    '''

    for name in fp_solvers:
        s = smt(name, strict=True)
        s.SetLogic("QF_FP")

        bvsort1 = s.ConstructSort(s.BitVec, 1)
        bvsort8 = s.ConstructSort(s.BitVec, 8)
        bvsort24 = s.ConstructSort(s.BitVec, 24)

        # Note: There's a "hidden" bit which makes it 25 instead of 24
        fpsort8_25 = s.ConstructSort(s.FP, 8, 25)

        b0 = s.TheoryConst(bvsort1, 0)
        b200 = s.TheoryConst(bvsort8, 200)
        b468 = s.TheoryConst(bvsort24, 468)

        b152 = s.TheoryConst(s.BitVec(8), 152)
        b42 = s.TheoryConst(s.BitVec(24), 42)

        f = s.TheoryConst(fpsort8_25, b0, b200, b468)
        f2 = s.TheoryConst(fpsort8_25, b0, b152, b42)

        fc = s.DeclareConst("fc", fpsort8_25)
        fc2 = s.DeclareConst("fc2", fpsort8_25)

        fpf2 = s.ApplyFun(s.FPAdd, s.Round.RNE, f, f2)
        fmf2 = s.ApplyFun(s.FPSub, s.Round.RNE, f, f2)

        fcgtfpf2 = s.ApplyFun(s.FPGt, fc, fpf2)
        fc2ltfmf2 = s.ApplyFun(s.FPLt, fc2, fmf2)

        s.Assert(fcgtfpf2)
        s.Assert(fc2ltfmf2)

        lt = s.ApplyFun(s.FPLe, fc, fc2)
        s.Assert(lt)
        assert not s.CheckSat()

if __name__ == "__main__":
    test_basic()
