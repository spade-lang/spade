#top = div_and_mod::signed_div_and_mod

import math
from spade import SpadeExt
import cocotb
from cocotb.triggers import Timer

def verilog_like_div(x, y):
    if x < 0:
        return -(-x // y)
    else:
        return x // y

def verilog_like_mod(x, y):
    if x < 0:
        return -(-x % y)
    else:
        return x % y

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)

    for x in range(-127, 128):
        s.i.x = f"{x}"
        await Timer(1, units='ns')
        s.o.div_4.assert_eq(f"{verilog_like_div(x, 4)}")
        s.o.mod_4.assert_eq(f"{verilog_like_mod(x, 4)}")
        s.o.div_3.assert_eq(f"{verilog_like_div(x, 3)}")
        s.o.mod_3.assert_eq(f"{verilog_like_mod(x, 3)}")

