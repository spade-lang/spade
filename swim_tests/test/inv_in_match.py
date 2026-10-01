# top = inv_in_match::main

import cocotb
from spade import SpadeExt
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)

    s.i.a = "true"
    s.i.b = "true"
    s.i.n = "4"

    await Timer(1, units="ps")
    s.o.assert_eq("14")

    s.i.a = "true"
    s.i.b = "false"
    s.i.n = "6"

    await Timer(1, units="ps")
    s.o.assert_eq("26")

    s.i.a = "false"
    s.i.b = "false"
    s.i.n = "8"

    await Timer(1, units="ps")
    s.o.assert_eq("38")
