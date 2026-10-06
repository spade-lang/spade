#top = range_indexing::lower_range

from spade import SpadeExt
import cocotb
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)
    s.i.a = "[0, 1, 2, 3]"
    await Timer(1, units='ns')
    s.o.assert_eq(f"[0, 1]")

