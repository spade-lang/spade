#top = test1
import cocotb
from spade import SpadeExt

@cocotb.test()
async def missing_input(dut):
    s = SpadeExt(dut)
    s.i.missing = "1"

    
@cocotb.test()
async def missing_field_in_inner(dut):
    s = SpadeExt(dut)
    s.i.s.missing = "1"


@cocotb.test()
async def nested_python(dut):
    def inner_fn(s):
        s.i.missing = "1"

    s = SpadeExt(dut)
    inner_fn(s)


@cocotb.test()
async def missing_output_field(dut):
    s = SpadeExt(dut)
    s.o.missing.assert_eq("5")


@cocotb.test()
async def compilation_error_in_input(dut):
    s = SpadeExt(dut)
    s.i.raw = "true"


@cocotb.test()
async def compilation_error_in_output(dut):
    s = SpadeExt(dut)
    s.o.a.assert_eq("true")

    
@cocotb.test()
async def compilation_error_in_output_compare(dut):
    s = SpadeExt(dut)
    _ = s.o.a == "true"


@cocotb.test()
async def compilation_error_in_nested_field_assignment(dut):
    s = SpadeExt(dut)
    _ = s.o.nested.x == "true"


@cocotb.test()
async def value_method_error_is_good(dut):
    s = SpadeExt(dut)
    _ = s.o.nested.x.value()


@cocotb.test()
async def reading_field_on_tuple_is_error(dut):
    s = SpadeExt(dut)
    s.i.tuple.x = 5


