# top = stdlib::option_sliding_window_test

import cocotb
from spade import SpadeExt
from cocotb.clock import Clock
from cocotb.triggers import Timer, FallingEdge

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut) # Wrap the dut in the Spade wrapper

    clk = dut.clk_i

    await cocotb.start(Clock(
        clk,
        period=10,
        units='ns'
    ).start())

    s.i.default = 0;
    s.i.rst = True
    await FallingEdge(clk)
    await FallingEdge(clk)
    s.i.rst = False

    s.i.val = "None"
    await Timer(1, units="ps")
    s.o.assert_eq("None")
    await FallingEdge(clk)
    s.o.assert_eq("None")

    await FallingEdge(clk)
    s.i.val = "Some(1)"
    await Timer(1, units="ps")
    s.o.assert_eq("Some([1,0,0])")
    await FallingEdge(clk)

    s.i.val = "Some(2)"
    await Timer(1, units="ps")
    s.o.assert_eq("Some([2,1,0])")
    await FallingEdge(clk)
    s.i.val = "Some(3)"
    await Timer(1, units="ps")
    s.o.assert_eq("Some([3,2,1])")
    await FallingEdge(clk)
