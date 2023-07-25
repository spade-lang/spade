# top=pipeline_methods::get_x_test_harness

from cocotb.triggers import FallingEdge, NextTimeStep
from spade import SpadeExt
from cocotb import cocotb
from cocotb.clock import Clock

@cocotb.test()
async def clock_is_driven_correctly(dut):
    clk = dut.clk_i

    s = SpadeExt(dut)

    await cocotb.start(Clock(clk, 1, units="ns").start())

    await FallingEdge(clk)
    s.i.x = "5"
    await FallingEdge(clk)
    s.o.assert_eq("5")
    s.i.x = "6"
    await FallingEdge(clk)
    s.o.assert_eq("6")
