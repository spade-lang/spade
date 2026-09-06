# top = inv_enum::main

import cocotb
from spade import SpadeExt
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)

    s.i.sel = "0"
    s.i.cond = "false"

    await Timer(1, units="ps")
    s.o.assert_eq("4")

    s.i.sel = "1"
    s.i.cond = "false"

    await Timer(1, units="ps")
    s.o.assert_eq("5")

    s.i.sel = "2"
    s.i.cond = "false"

    await Timer(1, units="ps")
    s.o.assert_eq("8")

    s.i.sel = "3"
    s.i.cond = "false"

    await Timer(1, units="ps")
    s.o.assert_eq("7")

    s.i.sel = "3"
    s.i.cond = "true"

    await Timer(1, units="ps")
    s.o.assert_eq("6")
