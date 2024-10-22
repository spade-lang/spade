#top = port_codegen_reproducer_339::broken

from spade import SpadeExt
from cocotb import cocotb
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)
    # This only checks for compilation errors
    s.i.x = "&10"
    await Timer(1, units="ps")
    s.o.assert_eq(10)
    

