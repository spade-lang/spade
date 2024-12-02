
# top = zero_size_pattern_binding::match_zs

import cocotb
from cocotb.scheduler import Timer
from spade import SpadeExt

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)

    s.i.val = "Some(ZeroSized())"
    await Timer(1, units = "ns")
    s.o.assert_eq("true")

    s.i.val = "None"
    await Timer(1, units = "ns")
    s.o.assert_eq("false")


