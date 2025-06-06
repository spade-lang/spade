# top=stdlib::option_impls::combinators

from spade import SpadeExt

import cocotb
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)
    s.i.val = "Some(102)"
    await Timer(1, units='ns')
    s.o.map.assert_eq("Some(103)")
    s.o.and_then.assert_eq("None")

    s.i.val = "Some(5)"
    await Timer(1, units='ns')
    s.o.map.assert_eq("Some(6)")
    s.o.and_then.assert_eq("Some(6)")

    s.i.val = "None"
    await Timer(1, units='ns')
    s.o.map.assert_eq("None")
    s.o.and_then.assert_eq("None")

