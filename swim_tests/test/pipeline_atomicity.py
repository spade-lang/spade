#top = pipeline_ready_valid::stalled_integer_producer

from collections.abc import Sequence
from typing import List
from cocotb.triggers import FallingEdge, NextTimeStep
from spade import SpadeExt
from cocotb import cocotb
from cocotb.clock import Clock
import random

async def test_sequence(dut, seq: Sequence):
    clk = dut.clk_i

    s = SpadeExt(dut)

    await cocotb.start(Clock(clk, 1, units="ns").start())

    s.i.enables = "[true, true, true, true]"
    s.i.rst = "true"

    # Let the enables propagate through the pipeline until the enabled
    # values have propagated
    [await FallingEdge(clk) for _ in range(0, 4)]

    s.i.rst = "false"

    last_val = None

    # Test all combinations of enables a few times
    for v in seq:
        await FallingEdge(clk)
        s.i.enables = f"""[
            {"true" if v & 1 == 1 else "false"},
            {"true" if v & 2 == 2 else "false"},
            {"true" if v & 4 == 4 else "false"},
            {"true" if v & 8 == 8 else "false"}
        ]"""

        if s.o.valid.is_eq("true"):
            new_val = int(s.o.val.value())

            if last_val is not None and new_val != last_val + 1:
                assert False, f"Non-sequential output value. Got {new_val} expected {last_val+1}"

            last_val = new_val
        else:
            s.o.val.assert_eq(f"{last_val}" if last_val else "0")

    # Ensure that at least one non-zero value made it through
    assert last_val is not None and last_val != 0

@cocotb.test()
async def increasing_integers(dut):
    await test_sequence(dut, range(0, 255))

@cocotb.test()
async def random_enables(dut):
    random.seed(0) # Deterministic tests are good
    await test_sequence(dut, [random.randint(0, 255) for i in range(0, 512)])



