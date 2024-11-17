# top = simple_io::inv_args

import cocotb
from cocotb.triggers import Timer
from spade import SpadeExt

@cocotb.test()
async def assert_eq_works(dut):
    s = SpadeExt(dut)
    
    s.i.a = "&1"
    s.i.b = "&2"
    s.o.x_inv = "&3"
    s.o.y_inv = "&true"
    await Timer(1, units="ns")

    s.o.a.assert_eq("&1")
    s.o.b.assert_eq("&2")
    s.i.x_inv.assert_eq("&3")
    s.i.y_inv.assert_eq("&true")
    

@cocotb.test()
async def value_works(dut):
    s = SpadeExt(dut)
    
    s.i.a = "&1"
    s.i.b = "&2"
    s.o.x_inv = "&3"
    s.o.y_inv = "&true"
    await Timer(1, units="ns")

    assert(s.o.a.value() == "1")
    assert(s.o.b.value() == "2")
    assert(s.i.x_inv.value() == "3")
    assert(s.i.y_inv.value() == "true")
    
@cocotb.test()
async def eq_value_works(dut):
    s = SpadeExt(dut)
    
    s.i.a = "&1"
    s.i.b = "&2"
    s.o.x_inv = "&3"
    s.o.y_inv = "&true"
    await Timer(1, units="ns")

    assert(s.o.a == "&1")
    assert(s.o.b == "&2")
    assert(s.i.x_inv == "&3")
    assert(s.i.y_inv == "&true")
    
