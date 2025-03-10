# top = stdlib::array_zip_test


import cocotb
from spade import SpadeExt
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut) # Wrap the dut in the Spade wrapper

    s.i.a = "[1,2,3]"
    s.i.b = "[4,5,6]"
    await Timer(1, units="ps")
    s.o.assert_eq("[(1, 4), (2, 5), (3, 6)]")


