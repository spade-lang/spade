#top = unsigned_add::unsigned_add

from spade import SpadeExt
import cocotb
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)
    s.i.x = "127"
    s.i.y = "128"
    await Timer(1, units='ns')
    s.o.assert_eq(f"255")

    s.i.x = "128"
    s.i.y = "0"
    await Timer(1, units='ns')
    s.o.assert_eq(f"128u")

    s.i.x = "255"
    s.i.y = "255"
    await Timer(1, units='ns')
    s.o.assert_eq(f"510u")
