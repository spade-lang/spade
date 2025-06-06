# top = stdlib::array_map::test


import cocotb
from spade import SpadeExt
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut) # Wrap the dut in the Spade wrapper

    s.i.arr = "[1,2,3,4]"
    await Timer(1, units="ps")
    s.o.assert_eq("[2,3,4,5]")


