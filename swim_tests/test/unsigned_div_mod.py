#top = div_and_mod::unsigned_div_and_mod

import math
from spade import SpadeExt
import cocotb
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)

    for x in range(0, 255):
        print(f"Testing {x}")
        s.i.x = f"{x}"
        await Timer(1, units='ns')
        s.o.div_4.assert_eq(f"{x // 4}")
        s.o.mod_4.assert_eq(f"{x % 4}")
        s.o.div_3.assert_eq(f"{x // 3}")
        s.o.mod_3.assert_eq(f"{x % 3}")

