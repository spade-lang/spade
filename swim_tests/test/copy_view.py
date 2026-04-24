#top = copy_view::main

from spade import SpadeExt
from cocotb import cocotb
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)

    s.i.a = "false"
    s.i.c = "8"

    await Timer(1, units="ps")
    s.o.assert_eq("(false, 8)")
    s.i.b.assert_eq("-8")

    s.i.a = "true"
    s.i.c = "5"

    await Timer(1, units="ps")
    s.o.assert_eq("(true, 5)")
    s.i.b.assert_eq("5")
