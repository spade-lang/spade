#top = type_cast::main

from spade import SpadeExt
from cocotb import cocotb
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)

    await Timer(1, units="ps")
    s.o.assert_eq("13")
