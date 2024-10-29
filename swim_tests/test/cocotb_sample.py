# top = cocotb_sample::add_mul

from cocotb.clock import Clock
from spade import SpadeExt
from cocotb import cocotb
from cocotb.triggers import FallingEdge


@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)  # Wrap the dut in the Spade wrapper

    # To access unmangled signals as cocotb values (without the spade wrapping) use
    # <signal_name>_i
    # For cocotb functions like the clock generator, we need a cocotb value
    clk = dut.clk_i

    await cocotb.start(Clock(clk, period=10, units="ns").start())

    await FallingEdge(clk)
    s.i.a = "2"
    s.i.b = "3"
    await FallingEdge(clk)
    s.o.sum.assert_eq("5")
    s.o.product.assert_eq("6")
