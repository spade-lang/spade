#top = range_indexing::upper_range_bool

from spade import SpadeExt
import cocotb
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)
    s.i.a = "[false, true, false, true, false, false, true, true]"
    await Timer(1, units='ns')
    s.o.assert_eq(f"[true, true]")

