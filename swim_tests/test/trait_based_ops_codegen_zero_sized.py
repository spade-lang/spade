# top = trait_based_ops_codegen_zero_sized::test

import cocotb

@cocotb.test()
async def test(dut):
    # This test only tests for compilation errors in the generated verilog
    pass
