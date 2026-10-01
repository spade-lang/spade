#top = lir_compile_tests::simple_match

from spade import SpadeExt
from cocotb import cocotb
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)

    s.i.x = [0, 0]
    await Timer(1, units="ns")
    s.o.assert_eq(True)

    s.i.x = [1, 0]
    await Timer(1, units="ns")
    s.o.assert_eq(False)
