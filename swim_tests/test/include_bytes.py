# top=include_bytes::test

import cocotb
from cocotb.scheduler import Timer
from spade import SpadeExt

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)

    await Timer(1, units = "ns")
    s.o.assert_eq("[72, 101, 108, 108, 111, 44, 32, 87, 111, 114, 108, 100, 33, 10]")
