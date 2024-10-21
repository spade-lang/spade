#top = simple_io::fields

from spade import SpadeExt
from cocotb import cocotb
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)

    s.i.x = True
    s.i.y = 0
    s.i.z = 0b1111
    s.i.w = False
    # This only checks for compilation errors
    await Timer(1, units="ps")
    s.o.x.assert_eq(True)
    s.o.y.assert_eq(0)
    s.o.z.assert_eq(0b1111)
    s.o.w.assert_eq(False)
