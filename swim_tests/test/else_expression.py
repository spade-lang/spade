#top = else_expression::operator_after_else

from spade import SpadeExt
from cocotb import cocotb
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)

    s.i.cond = "true"
    s.i.a = "5"
    s.i.b = "3"
    s.i.c = "4"
    await Timer(1, units='ns')
    s.o.assert_eq("9")

    s.i.cond = "false"
    await Timer(1, units='ns')
    s.o.assert_eq("7")
