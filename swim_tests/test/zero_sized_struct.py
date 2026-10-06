# top=zero_sized_struct::test

import cocotb
from cocotb.triggers import Timer
from spade import SpadeExt

@cocotb.test()
async def test(dut):
    # This test only tests for compilation errors in the generated verilog
    pass
