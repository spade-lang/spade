# top = inout_read_write::test

from spade import SpadeExt
from cocotb import cocotb
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)  # Wrap the dut in the Spade wrapper

    s.i.i0 = "None"
    s.i.i1 = "Some(15)"
    s.i.i2 = "None"
    await Timer(1, units="ns")

    assert dut.single.value == "zzzzzzzz"
    assert dut.o0.value == "1zzzzzzzz"
    assert dut.o1.value == "0xxxxxxxx"
    assert dut.o2.value == "1zzzzzzzz"

    s.i.i0 = "Some(3)"
    s.i.i1 = "None"
    s.i.i2 = "Some(5)"
    await Timer(1, units="ns")

    assert dut.single.value == "00000011"
    assert dut.o0.value == "0xxxxxxxx"
    assert dut.o1.value == "1zzzzzzzz"
    assert dut.o2.value == "0xxxxxxxx"
