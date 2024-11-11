#top = ports::dut
import cocotb
from spade import SpadeExt

@cocotb.test()
async def setting_inv_wire(dut):
    s = SpadeExt(dut)
    s.i.back = 0

    
@cocotb.test()
async def setting_nested_inv_wire(dut):
    s = SpadeExt(dut)
    s.i.nested.back = 0


@cocotb.test()
async def setting_struct_port(dut):
    s = SpadeExt(dut)
    s.i.nested = 0

    
@cocotb.test()
async def reading_output_inv_wire(dut):
    s = SpadeExt(dut)
    s.o.back.assert_eq("0")
    
    
@cocotb.test()
async def setting_output_fwd_wire(dut):
    s = SpadeExt(dut)
    s.o.fwd = "0"

    
@cocotb.test()
async def reading_nested_output_inv_wire(dut):
    s = SpadeExt(dut)
    s.o.inner.back.assert_eq("0")


@cocotb.test()
async def setting_nested_output_fwd_wire(dut):
    s = SpadeExt(dut)
    s.o.inner.fwd = "0"
