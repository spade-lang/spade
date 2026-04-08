# top = stdlib_asserts::stdlib_asserts


import cocotb
from spade import SpadeExt
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut) # Wrap the dut in the Spade wrapper

    await Timer(1, units="ps")


