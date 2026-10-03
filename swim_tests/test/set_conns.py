# top = set_conns::test_set

import cocotb
from spade import SpadeExt
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)

    await Timer(1, units="ps")
    s.i.x.assert_eq("1")
    s.i.y.assert_eq("2")
    s.i.z.assert_eq("3")
    s.i.w.assert_eq("4")
    s.i.t.assert_eq("5")
