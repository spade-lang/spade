#top = stdlib::fifo::fifo_test_harness

from typing import List
from cocotb.clock import Clock
from spade import SpadeExt
from cocotb import cocotb, random
from cocotb.triggers import FallingEdge

async def initial_setup(s, write_clk, read_clk):
    await cocotb.start(Clock(
        write_clk,
        period=10,
        units='ns'
    ).start())
    await cocotb.start(Clock(
        read_clk,
        period=11,
        units='ns'
    ).start())

    s.i.write_rst = "true"
    s.i.read_rst = "true"
    s.i.write = "None"
    s.i.ack = "false"
    await FallingEdge(read_clk)
    await FallingEdge(read_clk)
    await FallingEdge(read_clk)
    await FallingEdge(read_clk)
    s.i.write_rst = "false"
    s.i.read_rst = "false"


@cocotb.test()
async def inserting_and_removing_one_element_works(dut):
    s = SpadeExt(dut)
    write_clk = dut.write_clk_i
    read_clk = dut.read_clk_i

    await initial_setup(s, write_clk, read_clk)

    await FallingEdge(read_clk)
    await FallingEdge(read_clk)

    s.o.w_full.assert_eq("false")
    s.o.r_num_elements.assert_eq("0")
    s.o.r_read.assert_eq("None")

    await FallingEdge(write_clk)
    s.i.write = "Some(123)"
    await FallingEdge(write_clk)
    s.i.write = "None"
    # Give some time for the signal to propagate into the other domain
    await FallingEdge(read_clk)
    await FallingEdge(read_clk)
    await FallingEdge(read_clk)
    s.o.w_full.assert_eq("false")
    s.o.r_num_elements.assert_eq("1")
    s.o.r_read.assert_eq("Some(123)")

    s.i.ack = "true"
    await FallingEdge(read_clk)
    s.i.ack = "false"
    s.o.r_num_elements.assert_eq("0")
    s.o.r_read.assert_eq("None")

@cocotb.test()
async def fifo_fills_after_15_insertions(dut):
    s = SpadeExt(dut)
    write_clk = dut.write_clk_i
    read_clk = dut.read_clk_i

    await initial_setup(s, write_clk, read_clk)

    await FallingEdge(write_clk)
    for i in range(0, 15):
        s.i.write = f"Some({i})"
        await FallingEdge(write_clk)
    s.i.write = "None"
    s.o.w_full.assert_eq("true")
    # It takes a while for the new size to propagate to the read domain
    await FallingEdge(read_clk);
    await FallingEdge(read_clk);
    await FallingEdge(read_clk);
    s.o.r_num_elements.assert_eq("15")

    for i in range(0, 15):
        s.o.r_read.assert_eq(f"Some({i})")
        s.i.ack = "true"
        await FallingEdge(read_clk)
    s.o.r_read.assert_eq("None")


@cocotb.test()
async def fifo_fills_after_15_insertions_when_in_middle_of_fifo(dut):
    s = SpadeExt(dut)
    write_clk = dut.write_clk_i
    read_clk = dut.read_clk_i

    await initial_setup(s, write_clk, read_clk)

    # Move the pointers into the middle
    await FallingEdge(write_clk)
    for i in range(0, 7):
        s.i.write = f"Some({i})"
        await FallingEdge(write_clk)
    s.i.write = f"None"
    await FallingEdge(read_clk);
    await FallingEdge(read_clk);
    await FallingEdge(read_clk);
    s.o.r_num_elements.assert_eq("7")

    for i in range(0, 7):
        s.o.r_read.assert_eq(f"Some({i})")
        s.i.ack = "true"
        await FallingEdge(read_clk)
    s.i.ack = "false"
    s.o.r_num_elements.assert_eq("0")


    await FallingEdge(write_clk);
    await FallingEdge(write_clk);
    await FallingEdge(write_clk);

    await FallingEdge(write_clk)
    for i in range(0, 15):
        s.i.write = f"Some({i})"
        await FallingEdge(write_clk)
    s.i.write = "None"
    s.o.w_full.assert_eq("true")
    # It takes a while for the new size to propagate to the read domain
    await FallingEdge(read_clk);
    await FallingEdge(read_clk);
    await FallingEdge(read_clk);
    s.o.r_num_elements.assert_eq("15")

    for i in range(0, 15):
        s.o.r_read.assert_eq(f"Some({i})")
        s.i.ack = "true"
        await FallingEdge(read_clk)
    s.o.r_read.assert_eq("None")


async def smoke_test_read_side(s: SpadeExt, read_clk, seq: List[int], read_probability: float):
    await FallingEdge(read_clk)

    for elem in seq:
        while s.o.r_read.is_eq(f"None"):
            await FallingEdge(read_clk)

        s.o.r_read.assert_eq(f"Some({elem})")
        while random.random() >= read_probability:
            s.i.ack = "false"
            await FallingEdge(read_clk)
        s.i.ack = "true"
        await FallingEdge(read_clk)
        s.i.ack = "false"

async def smoke_test_write_side(s: SpadeExt, write_clk, seq: List, write_probability: float):
    for elem in seq:
        while random.random() >= write_probability:
            await FallingEdge(write_clk)

        while s.o.w_full.is_eq("true"):
            await FallingEdge(write_clk)

        s.i.write = f"Some({elem})"
        await FallingEdge(write_clk);
        s.i.write = f"None"



@cocotb.test()
async def smoke_test(dut):
    random.seed(0)
    s = SpadeExt(dut)
    write_clk = dut.write_clk_i
    read_clk = dut.read_clk_i

    await initial_setup(s, write_clk, read_clk)

    seq = list(map(lambda _: random.randint(0, 15), range(0, 100)))
    print(seq)
    read = cocotb.start_soon(smoke_test_read_side(s, read_clk, seq, 0.5))
    write = cocotb.start_soon(smoke_test_write_side(s, write_clk, seq, 0.5))

    await read
    await write

