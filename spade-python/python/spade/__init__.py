from typing import List, NewType
import typing
from .spade import *

import cocotb
import colors
from cocotb.types import LogicArray
from cocotb.handle import Force
from cocotb.triggers import *
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
        result.o = result.o__()
        return result

    def o__(self):
        """ Get a reference to the output of the DUT"""
        return OutputField(self, [], self.output_as_field_ref(), self.dut)


class InputPorts(object):
    def __init__(self, dut, spade: SpadeExt):
        self.spade__ = spade
        self.dut__ = dut

    def __setattr__(self, name: str, value: object):
        if not name.endswith("__"):
            value = to_spade_value(value)
            # Ask the spade compiler if the DUT has this field
            (port, val) = self.spade__.arg_value(name, value)

            self.dut__._id(port, extended=False).value = LogicArray(val.inner())
        else:
            super(InputPorts, self).__setattr__(name, value)


class OutputField(object):
    def __init__(self, spade: SpadeExt, path: List[str], field_ref, dut):
        self.spade__ = spade
        self.path__ = path
        self.field_ref__ = field_ref
        self.dut__ = dut

    # This is not intended to be called on this struct, instead, it should be called on the
    # parent field since python does not allow overloading operator=
    def set_value__(self, value):
        result = self.spade__.compile_field_value(self.field_ref__, value)
        fwd_range = self.field_ref__.fwd_range
        print(f"{self.path__}: {fwd_range}")
        value =  LogicArray(result.inner())
        signal = self.dut__._id("input__", extended=False)
        downto_range = fwd_range().as_downto(len(signal))
        for (i, idx) in enumerate(range(downto_range[0], downto_range[1])):
            print(i, " -> ", idx)
            # TODO: Don't hard code input__ here
            signal[idx].value = value[i]


    def assert_eq(self, expected: object):
        expected = to_spade_value(expected)
        # This shares a bit of code with is_eq, but since we need access to intermediate
        # values, we'll duplicate things for now
        r = self.spade__.compare_field(
            self.field_ref__,
            expected,
            BitString(self.dut__.output__.value.binstr)
        )

        expected_bits = r.expected_bits.inner();
        got_bits = r.got_bits.inner();

        if not r.matches():
            message = "\n"
            message += colors.red("Assertion failed") + "\n"
            message += f"\t expected: {colors.green(r.expected_spade)}\n";
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
            self.field_ref__,
            BitString(self.dut__.output__.value.binstr)
        )

    def is_eq(self, other: object) -> bool:
        return self == other

    def __ne__(self, value: object, /) -> bool:
        return not self == value

    def __eq__(self, value: object, /) -> bool:
        value = to_spade_value(typing.cast(object, value))
        r = self.spade__.compare_field(
            self.field_ref__,
            value,
            BitString(self.dut__.output__.value.binstr)
        )
        expected_bits = r.expected_bits.inner();
        got_bits = r.got_bits.inner();
        return expected_bits.lower() == got_bits.lower()


    def __getattribute__(self, __name: str):
        if __name.endswith("__") or __name == "assert_eq" or __name == "is_eq" or __name == "value":
            return super(OutputField, self).__getattribute__(__name)
        else:
            new_path = self.path__ + [__name]
            return OutputField(
                self.spade__,
                new_path,
                self.spade__.output_field(new_path),
                self.dut__
            )


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
        raise TypeError(f"Values of type {type(val)} cannot be converted to Spade values")
