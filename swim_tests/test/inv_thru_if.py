# top = inv_thru_cond_blocks::thru_if

import cocotb
from spade import SpadeExt
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)

    s.i.cond = "true"
    s.i.val = "4"

    await Timer(1, units="ps")
    s.o.assert_eq("5")

    s.i.cond = "true"
    s.i.val = "5"

    await Timer(1, units="ps")
    s.o.assert_eq("6")

    s.i.cond = "false"
    s.i.val = "4"

    await Timer(1, units="ps")
    s.o.assert_eq("3")

    s.i.cond = "false"
    s.i.val = "5"

    await Timer(1, units="ps")
    s.o.assert_eq("4")
