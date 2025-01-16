#top = split_compound_test::test

from cocotb.clock import Clock
from spade import SpadeExt
from cocotb import cocotb
from cocotb.triggers import FallingEdge

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut) # Wrap the dut in the Spade wrapper

    # To access unmangled signals as cocotb values (without the spade wrapping) use
    # <signal_name>_i
    # For cocotb functions like the clock generator, we need a cocotb value
    clk = dut.clk_i

    await cocotb.start(Clock(
        clk,
        period=10,
        units='ns'
    ).start())

    await FallingEdge(clk)
    s.i.val = "Val(0, 1, (2, 3), [5,6,7,8,9,10,11,12])"
    await FallingEdge(clk)
    s.o.assert_eq("Val(0, 1, (2, 3), [5,6,7,8,9,10,11,12])")
