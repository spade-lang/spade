
#top = no_select_x::test

from spade import SpadeExt
from cocotb import cocotb
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)
    s.i.input = 0b0_0000

    await Timer(1, units="ps")
    s.o.assert_eq("((None, None, None), (0b0_00001, 0b0_00010, 0b0_00011))")

    s = SpadeExt(dut)
    s.i.input = 0b1_1000

    await Timer(1, units="ps")
    s.o.assert_eq("((Some(0b1001), Some(0b1010), Some(0b1011)), (0b1_01001, 0b1_01010, 0b1_01011))")
