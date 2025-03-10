# top = stdlib::option_unwrap_or_test


import cocotb
from spade import SpadeExt
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut) # Wrap the dut in the Spade wrapper

    s.i.default = 123;
    s.i.val = "Some(5)"
    await Timer(1, units="ps")
    s.o.assert_eq(5)

    s.i.val = "None"
    await Timer(1, units="ps")
    s.o.assert_eq(123)
