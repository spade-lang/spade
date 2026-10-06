# top=entity_without_return::no_output

import cocotb
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    dut.input.value = True
    await Timer(1, units="ns")
    assert dut.output_mut.value == False
    dut.input.value = False
    await Timer(1, units="ns")
    assert dut.output_mut.value == True
