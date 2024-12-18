# top = deduplicated_mut_wires::test_struct

from spade import SpadeExt

import cocotb
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)
    s.i.x = True
    s.i.y = False
    await Timer(1, units='ns')
    s.o.assert_eq("(true, false)")

