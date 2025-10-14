# top=stdlib::option_impls::combinators

from spade import SpadeExt

import cocotb
from cocotb.triggers import Timer, FallingEdge
from cocotb.clock import Clock

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)
    s.i.val = "Some(102)"
    await Timer(1, units='ns')
    s.o.map.assert_eq("Some(103)")
    s.o.and_then.assert_eq("None")

    s.i.val = "Some(5)"
    await Timer(1, units='ns')
    s.o.map.assert_eq("Some(6)")
    s.o.and_then.assert_eq("Some(6)")

    s.i.val = "None"
    await Timer(1, units='ns')
    s.o.map.assert_eq("None")
    s.o.and_then.assert_eq("None")


@cocotb.test()
async def pmap(dut):
    s = SpadeExt(dut)
    clk = dut.clk_i
    cocotb.start_soon(Clock(clk, 1, units="ns").start())

    din = [1,2,3,4,5]

    await FallingEdge(clk)
    async def driver():
        s.i.val = "None"
        await FallingEdge(clk)
        for d in din:
           s.i.val = f"Some({d})"
           await FallingEdge(clk)

    cocotb.start_soon(driver())

    for _ in range(0, 3):
        await FallingEdge(clk)

    s.o.pipeline_map.assert_eq("None")
    await FallingEdge(clk)
    for d in din:
        s.o.pipeline_map.assert_eq(f"Some({d})")
        await FallingEdge(clk)
