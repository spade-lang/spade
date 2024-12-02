#top = single_variant_recursive_enum::construction

import cocotb
from cocotb.scheduler import Timer
from spade import SpadeExt

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)

    await Timer(1, units = "ns")

