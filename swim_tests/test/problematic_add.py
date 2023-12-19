
#top = arithmetic::problematic_add

from spade import SpadeExt
from cocotb import cocotb
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)
    s.i.x = "127"
    s.i.y = "128u"
    await Timer(1, units='ns')
    s.o.assert_eq(f"{255}u")

