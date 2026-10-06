#top = array_pattern::test_array_pattern

from spade import SpadeExt
import cocotb
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)
    s.i.input = "[0, 1, 2, 3]"
    await Timer(1, units='ns')
    s.o.at0.assert_eq(0)
    s.o.at1.assert_eq(1)
    s.o.at2.assert_eq(2)
    s.o.at3.assert_eq(3)
    s.o.is_1234.assert_eq(False)

    s.i.input = [1,2,3,4]
    await Timer(1, units='ns')
    s.o.is_1234.assert_eq(True)

    s.i.input = [1,2,2,4]
    await Timer(1, units='ns')
    s.o.is_1234.assert_eq(False)

    s.i.input = [0,0,0,0]
    await Timer(1, units='ns')
    s.o.is_1234.assert_eq(False)

