# top=entity_without_return::void_return

import cocotb
from cocotb.triggers import Timer
from spade import SpadeExt


@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)
    s.i.input = "true"
    await Timer(1, units="ns")
    # TODO:
    # assert s.o.output.value() == "false"
    s.i.input = "false"
    await Timer(1, units="ns")
    # TODO:
    # assert s.o.output.value() == "true"
