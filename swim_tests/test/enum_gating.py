#top = enum_gating::enum_gating

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
    s.i.x = "Some(10)"
    s.i.rst = "false"
    await FallingEdge(clk)
    s.o.cooked.assert_eq("Some(10)")
    s.o.raw.assert_eq("0b1_0000_1010")

    s.i.x = "None()"
    await FallingEdge(clk)
    s.o.cooked.assert_eq("None()")
    # With the optimization turned on, the lsbs keep their previous values
    s.o.raw.assert_eq("0b0_0000_1010")

