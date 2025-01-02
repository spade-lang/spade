
# top=zero_size_exprs::test

from spade import SpadeExt

import cocotb
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    # This only checks for codegen bugs
    pass

