#top = single_variant_recursive_enum::match_one_variant

import cocotb
from cocotb.scheduler import Timer
from spade import SpadeExt

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)

    s.i.val = "Some(OneVariant::Variant())"
    await Timer(1, units = "ns")
    s.o.assert_eq("true")

    s.i.val = "None"
    await Timer(1, units = "ns")
    s.o.assert_eq("false")


