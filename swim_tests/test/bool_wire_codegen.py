# top=test_bool_wire_codegen::harness

import cocotb

@cocotb.test()
async def test(dut):
    # NOTE: This test checks for miscompilation of the generated verilog,
    # so no tests are actually performed
    pass

