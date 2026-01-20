#top = match_if::test_match_if

from spade import SpadeExt
from cocotb import cocotb
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)
    s.i.cond = True
    s.i.input = "(0i8, true, Color::Purple)"
    await Timer(1, units='ns')
    s.o.mi0.assert_eq(0)
    s.o.mi1.assert_eq(0)
    s.o.mi2.assert_eq(0)
    s.o.mi3.assert_eq(0)
    s.o.mi4.assert_eq(0)

    s.i.input = "(0i8, false, Color::Purple)"
    await Timer(1, units='ns')
    s.o.mi0.assert_eq(0)
    s.o.mi1.assert_eq(2)
    s.o.mi2.assert_eq(0)
    s.o.mi3.assert_eq(0)
    s.o.mi4.assert_eq(2)

    s.i.cond = False
    s.i.input = "(0i8, true, Color::Purple)"
    await Timer(1, units='ns')
    s.o.mi0.assert_eq(1)
    s.o.mi1.assert_eq(1)
    s.o.mi2.assert_eq(1)
    s.o.mi3.assert_eq(1)
    s.o.mi4.assert_eq(1)

    s.i.input = "(1i8, false, Color::Yellow)"
    await Timer(1, units='ns')
    s.o.mi0.assert_eq(2)
    s.o.mi1.assert_eq(3)
    s.o.mi2.assert_eq(2)
    s.o.mi3.assert_eq(1)
    s.o.mi4.assert_eq(2)
