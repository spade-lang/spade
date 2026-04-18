# top = inout_read_write::test

from spade import SpadeExt
from cocotb import cocotb
from cocotb.triggers import Timer
from cocotb.handle import Force

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

    s.i.i0 = "None"
    s.i.i1 = "None"
    s.i.i2 = "None"
    dut.single.value = Force(0b00000011)
    dut.array.value = Force(0b1100_1010_1111_0000)

    await Timer(1, units="ns")

    s.i.o0.assert_eq("Some(0b00000011)")
    s.i.o1.assert_eq("Some(0b1111_0000)")
    s.i.o2.assert_eq("Some(0b1100_1010)")


@cocotb.test()
async def single_bit(dut):
    s = SpadeExt(dut)

    s.i.i3 = "Some(true)"
    await Timer(1, units="ns")
    assert dut.onebit.value == "1"
    s.i.o3.assert_eq("None")

    s.i.i3 = "Some(false)"
    await Timer(1, units="ns")
    assert dut.onebit.value == "0"
    s.i.o3.assert_eq("None")

    s.i.i3 = "None"
    dut.onebit.value = Force(1)
    await Timer(1, units="ns")
    s.i.o3.assert_eq("Some(true)")

    dut.onebit.value = Force(0)
    await Timer(1, units="ns")
    s.i.o3.assert_eq("Some(false)")
