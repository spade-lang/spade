# top=no_mangle_params::no_mangle_output

import cocotb
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    dut.val.value = True
    await Timer(1, units="ns")
    assert dut.t.value == True
