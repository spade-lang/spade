# top=single_variant_enum::test

import cocotb
from cocotb.triggers import Timer
from spade import SpadeExt

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)

    s.i.t = "T::A(true)"
    await Timer(1, units = "ns")
    s.o.assert_eq("true")
    s.i.t = "T::A(false)"
    await Timer(1, units = "ns")
    s.o.assert_eq("false")

