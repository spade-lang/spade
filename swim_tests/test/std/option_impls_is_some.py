# top=stdlib::option_impls::is_some

from spade import SpadeExt

import cocotb
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)
    s.i.opt = "Some(102)"
    await Timer(1, units='ns')
    s.o.assert_eq("true")

    s.i.opt = "None"
    await Timer(1, units='ns')
    s.o.assert_eq("false")
