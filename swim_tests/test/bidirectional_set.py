# top = bidirectional_set::connect

import cocotb
from spade import SpadeExt
from cocotb.triggers import Timer

@cocotb.test
async def test(dut):
    s = SpadeExt(dut)

    s.i.fwd.fwd = "&5"
    s.i.back.back = "&6";
    await Timer(1, units="ns")
    s.i.back.fwd.assert_eq("&5")
    s.i.fwd.back.assert_eq("&6")
