
# top=zero_size_enum::test

import cocotb
from cocotb.scheduler import Timer
from spade import SpadeExt

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)

    await Timer(1, units = "ns")
    s.o.assert_eq("true")

