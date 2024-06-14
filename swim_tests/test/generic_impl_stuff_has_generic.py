# top=generic_impl_stuff::has_generic_th

from spade import SpadeExt

import cocotb
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)
    await Timer(1, units='ns')
    s.o.assert_eq("123")

