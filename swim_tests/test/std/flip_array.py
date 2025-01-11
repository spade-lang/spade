#top = flip_array::bitreverse

from spade import SpadeExt
from cocotb import cocotb
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)
    s.i.a = "[true, true, false, false, true, false, true, false]"
    s.i.b = "[1,2,3,4]"
    await Timer(1, units='ns')
    s.o.assert_eq(f"([false, true, false, true, false, false, true, true], [4,3,2,1])")

