#top = bool_memory::test

import cocotb
from cocotb.scheduler import Timer
from cocotb.clock import Clock
from cocotb.triggers import FallingEdge
from spade import SpadeExt

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)

    clk = dut.clk_i;
    await cocotb.start(Clock(clk, 1, "ns").start())

    await FallingEdge(clk)

    for i in range(0, 255):
        s.i.addr = i
        s.i.we = True
        s.i.write = True
        await FallingEdge(clk)
        s.i.we = False
        await FallingEdge(clk)
        s.o.assert_eq(True)

        s.i.addr = i
        s.i.we = True
        s.i.write = False
        await FallingEdge(clk)
        s.i.we = False
        await FallingEdge(clk)
        s.o.assert_eq(False)

        


