import os
import colors

import cocotb
from cocotb.types import LogicArray
from .spade import BitString, ComparisonResult, Spade, SpadeType


class SpadeExt(Spade):
    def __new__(cls, dut):
        compiler_state = os.environ["SWIM_SPADE_STATE"]
        uut_name = os.environ["SWIM_UUT"]

        try:
            result = super().__new__(cls, uut_name, compiler_state)
        except FileNotFoundError as e:
            print(f"{compiler_state}")
            print("Failed to find", e.filename, " ", e.filename2)
            raise e


        result.dut = dut
        result.i = InputPorts(dut, result)
        result.o = result.o__()
        return result

    def o__(self) -> "OutputField":
        """ Get a reference to the output of the DUT"""
        return OutputField(self, [], self.output_as_field_ref(), self.dut)


class InputPorts(object):
    def __init__(self, dut, spade: SpadeExt):
        self._spade = spade
        self._dut = dut

    def __setattr__(self, name: str, value: str):
        if not name.endswith("__"):
            # Ask the spade compiler if the DUT has this field
            (port, val) = self._spade.port_value(name, value)

            self._dut._id(port, extended=False).value = LogicArray(val.inner())
        else:
            super(InputPorts, self).__setattr__(name, value)


class OutputField(object):
    def __init__(self, spade: SpadeExt, path: list[str], field_ref, dut):
        self._spade = spade
        self._path = path
        self._field_ref = field_ref
        self._dut = dut

    def assert_eq(self, expected: str):
        expected_bits, got_bits, r = self._eq_helper(expected)

        if expected_bits != got_bits:
            message = "\n"
            message += colors.red("Assertion failed") + "\n"
            message += f"\t expected: {colors.green(r.expected_spade)}\n"
            message += f"\t      got: {colors.red(r.got_spade)}\n"
            message += "\n"
            message += f"\tverilog ('{colors.green(expected_bits)}' != '{colors.red(got_bits)}')"
            raise AssertionError(message)

    def value(self):
        """
            Returns the value of the field as a string representation of the spade value.
        """
        return self._spade.field_value(
            self._field_ref,
            BitString(self._dut.output__.value.binstr)
        )

    def is_eq(self, other: str) -> bool:
        expected_bits, got_bits, _ = self._eq_helper(other)
        return expected_bits.lower() == got_bits.lower()

    def _eq_helper(self, other: str):
        r = self._spade.compare_field(
            self._field_ref,
            other,
            BitString(self._dut.output__.value.binstr)
        )
        expected_bits = r.expected_bits.inner().lower()
        got_bits = r.got_bits.inner().lower()

        return expected_bits, got_bits, r

    def __getattribute__(self, attr: str):
        if attr.endswith("__") or attr == "assert_eq" or attr == "is_eq" or attr == "value":
            return super(OutputField, self).__getattribute__(attr)
        else:
            new_path = self._path + [attr]
            return OutputField(
                self._spade,
                new_path,
                self._spade.output_field(new_path),
                self._dut
            )

__all__ = ['Spade', 'SpadeExt', 'OutputField', 'InputPorts', 'BitString', 'ComparisonResult', 'SpadeType']