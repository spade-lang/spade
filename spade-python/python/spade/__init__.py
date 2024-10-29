from typing import List, NewType, Tuple
import typing
from .spade import Spade, FieldRef, BitString

import cocotb
import colors
from cocotb.types import LogicArray
from spade import Spade

import os

# FIXME: Once we only support newer python versions, we should use this typedef
# type SpadeConvertible = str | int | bool | List[SpadeConvertible]


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
        result.o = Field(result, result.output_as_field_ref(), dut)
        return result


class Field(object):
    def __init__(self, spade: SpadeExt, field_ref: FieldRef, dut):
        self.spade__ = spade
        self.field_ref__ = field_ref
        self.dut__ = dut

    # This is not intended to be called on this struct, instead, it should be called on the
    # parent field since python does not allow overloading operator=
    def set_value__(self, value):
        value = to_spade_value(value)
        bit_string = self.spade__.compile_field_value(self.field_ref__, value)
        fwd_range = self.field_ref__.fwd_range()
        bits = LogicArray(bit_string.inner())
        signal = self.dut__._id(self.field_ref__.source.fwd_mangled(), extended=False)
        downto_range = fwd_range.as_downto(len(signal))
        if fwd_range.is_full():
            signal.value = bits
        else:
            for i, idx in enumerate(range(downto_range[0], downto_range[1])):
                signal[idx].value = bits[i]

    def assert_eq(self, expected: object):
        expected = to_spade_value(expected)
        # This shares a bit of code with is_eq, but since we need access to intermediate
        # values, we'll duplicate things for now
        r = self.spade__.compare_field(
            self.field_ref__, expected, BitString(self.dut__._id(self.field_ref__.source.back_mangled(), extended=False).value.binstr)
        )

        expected_bits = r.expected_bits.inner()
        got_bits = r.got_bits.inner()

        if not r.matches():
            message = "\n"
            message += colors.red("Assertion failed") + "\n"
            message += f"\t expected: {colors.green(r.expected_spade)}\n"
            message += f"\t      got: {colors.red(r.got_spade)}\n"
            message += "\n"
            message += f"\tverilog ('{colors.green(expected_bits)}' != '{colors.red(got_bits)}')"
            assert False, message

    def value(self):
        """
        Returns the value of the field as a string representation of the spade value.
        """
        # This shares a bit of code with is_eq, but since we need access to intermediate
        # values, we'll duplicate things for now
        return self.spade__.field_value(
            self.field_ref__, BitString(self.dut__.output__.value.binstr)
        )

    def is_eq(self, other: object) -> bool:
        return self == other

    def __ne__(self, value: object, /) -> bool:
        return not self == value

    def __eq__(self, value: object, /) -> bool:
        value = to_spade_value(typing.cast(object, value))
        r = self.spade__.compare_field(
            self.field_ref__, value, BitString(self.dut__.output__.value.binstr)
        )
        expected_bits = r.expected_bits.inner()
        got_bits = r.got_bits.inner()
        return expected_bits.lower() == got_bits.lower()

    def __getattribute__(self, __name: str):
        if __name.endswith("__") or __name in ["assert_eq", "is_eq", "value"]:
            return super(Field, self).__getattribute__(__name)
        else:
            return Field(
                self.spade__,
                self.spade__.field_of_field(self.field_ref__, __name),
                self.dut__,
            )

    def __setattr__(self, name: str, value: object):
        if not name.endswith("__"):
            self.__getattribute__(name).set_value__(value)
        else:
            super(Field, self).__setattr__(name, value)


class InputPorts(object):
    def __init__(self, dut, spade: SpadeExt):
        self.spade__ = spade
        self.dut__ = dut

    def __getattribute__(self, __name: str) -> Field:
        if __name.endswith("__"):
            return super(InputPorts, self).__getattribute__(__name)
        return Field(self.spade__, self.spade__.arg_as_field(__name), self.dut__)

    def __setattr__(self, name: str, value: object):
        if not name.endswith("__"):
            self.__getattribute__(name).set_value__(value)
        else:
            super(InputPorts, self).__setattr__(name, value)


def to_spade_value(val: object) -> str:
    if type(val) == str:
        return val
    elif type(val) == int:
        return f"{val}"
    elif type(val) == bool:
        return "true" if val else "false"
    elif type(val) == list:
        return f"[{', '.join(map(lambda v: to_spade_value(v), val))}]"
    else:
        raise TypeError(
            f"Values of type {type(val)} cannot be converted to Spade values"
        )
