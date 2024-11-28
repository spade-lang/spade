# top = parametrized_externs::harness

from spade import SpadeExt
from cocotb import cocotb
from cocotb.triggers import Timer


@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)

    s.i.input = "0"
    s.i.named = "false"
    await Timer(1, units="ns")
    s.o.assert_eq("3")

    s.i.input = "0"
    s.i.named = "true"
    await Timer(1, units="ns")
    s.o.assert_eq("3")
