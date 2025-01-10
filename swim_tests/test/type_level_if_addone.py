# top = type_level_if::addone_test

import cocotb
from cocotb.triggers import Timer
from spade import SpadeExt

@cocotb.test()
async def assert_eq_works(dut):
    s = SpadeExt(dut)
    
    s.i.seq = "[1, 2, 3, 4]"
    await Timer(1, units="ns")

    s.o.assert_eq("[2,3,4,5]")

