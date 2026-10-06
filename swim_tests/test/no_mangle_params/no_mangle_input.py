# top=no_mangle_params::no_mangle_input

import cocotb
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    dut.t.value = True
    await Timer(1, units="ns")
    assert dut.output__.value == True
