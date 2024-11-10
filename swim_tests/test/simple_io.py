#top = simple_io::simple_io

from spade import SpadeExt
from cocotb import cocotb
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)

    s.o.back.set_value__("&10")
    # This only checks for compilation errors
    await Timer(1, units="ps")
    s.o.fwd.assert_eq("&10")

