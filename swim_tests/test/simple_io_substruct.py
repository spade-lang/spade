#top = simple_io::substruct

from spade import SpadeExt
from cocotb import cocotb
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)

    # TODO: Use s.o.raw_back = ...
    s.o.raw_back.set_value__("&10")
    s.o.inner.back.set_value__("&77")
    # This only checks for compilation errors
    await Timer(1, units="ps")
    s.o.raw_fwd.assert_eq("&10")
    s.o.inner.fwd.assert_eq("&77")

