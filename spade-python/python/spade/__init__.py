from ast import FunctionDef
from typing import Any, Callable, List, NewType, Tuple
import typing
from .spade import Spade, FieldRef, BitString, SourceCodeError, CompilationError

import cocotb
import colors
from cocotb.types import LogicArray
from spade import Spade

import os
import traceback
from pathlib import Path
import logging
import sys

class HandledAlreadyException(Exception):
    def __init__(self, inner) -> None:
        self.__cause__ = inner


# Cocotb adds a ton of extra chars to lines which makes them unnecessarily long, we'll override
# its logger with one that simply prints the log message
class SimpleFormatter(logging.Formatter):
    def _format(self, msg):
        print(msg)


# FIXME: Once we only support newer python versions, we should use this typedef
# type SpadeConvertible = str | int | bool | List[SpadeConvertible]

def handle_maybe_spade_exception(e: BaseException, stack: list[traceback.FrameSummary]):
    filtered_stack = list(filter(
        lambda frame: frame.filename != __file__ and "site-packages/cocotb" not in frame.filename,
        stack
    ))

    workdir = os.getcwd()
    top = filtered_stack[-1]
    lineno = f"{top.lineno}"
    lineno_padding = "".join(map(lambda _: " ", lineno))
    line_ref = f"{Path(top.filename).relative_to(workdir)}:{top.lineno}"

    def draw_error(kind: str, err_color: Callable[[str], Any], description: str, primary_label: str, notes: list[str]):
        print()

        print(colors.bold(f"{err_color(f'{kind}:')} {description}"))
        print(f" {lineno_padding} {colors.blue('┌─')} {line_ref}")
        print(colors.blue(f" {lineno_padding} │"))
        print(f" {colors.blue(f'{lineno} │')} {top.line}")

        if top.line is not None:
            arrows = err_color(f"{''.join(map(lambda _: '^', top.line))} {primary_label}")
            print(f" {colors.blue(f'{lineno_padding} │ ')}{arrows}", )

        print("")
        for note in notes:
            print(f"  {colors.bold(f'Help: ')}{note}")

        print("")
        if filtered_stack[:-1]:
            print("Traceback:")
            for frame in filtered_stack[:-1]:
                print(f"  {colors.green(Path(frame.filename).relative_to(workdir))}:{frame.lineno}")
        print("")

        # We've printed the exception, we don't need cocotb to do so again. So we'll just turn off 
        # logging
        logging.getLogger().handlers = []
        



    if isinstance(e, HandledAlreadyException):
        raise e
    if isinstance(e, SourceCodeError):
        description = e.args[0].description
        primary_label = e.args[0].primary_label
        notes = e.args[0].notes

        draw_error('error', lambda x: colors.red(x, style='bold'), description, primary_label, notes)
        raise HandledAlreadyException(e)
    if isinstance(e, CompilationError):
        # Spade prints the actual error itself, we just have to tell the user what python
        # line the error originated on
        draw_error("note", colors.green, "A Spade expression failed to compile", "When executing this", [])
        raise HandledAlreadyException(e)

    raise e

    

class SpadeExt(Spade):
    def __new__(cls, dut):
        # logger = logging.getLogger("cocotb").setFormatter()
        hdlr = logging.StreamHandler(sys.stdout)
        hdlr.setFormatter(SimpleFormatter())
        logging.getLogger().handlers = [hdlr]

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
        try:
            value = to_spade_value(value)
            bit_string = self.spade__.compile_field_value(self.field_ref__, value)
            fwd_range = self.field_ref__.write_dir_range()
            bits = LogicArray(bit_string.inner())
            signal = self.dut__._id(self.field_ref__.source.fwd_mangled(), extended=False)
            downto_range = fwd_range.as_downto(len(signal))
            if fwd_range.is_full():
                signal.value = bits
            else:
                for i, idx in enumerate(range(downto_range[0], downto_range[1])):
                    signal[idx].value = bits[i]
        except Exception as e:
                handle_maybe_spade_exception(e, traceback.extract_stack())

    def assert_eq(self, expected: object):
        try:
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
        except Exception as e:
            handle_maybe_spade_exception(e, traceback.extract_stack())

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
        try:
            value = to_spade_value(typing.cast(object, value))
            r = self.spade__.compare_field(
                self.field_ref__, value, BitString(self.dut__.output__.value.binstr)
            )
            expected_bits = r.expected_bits.inner()
            got_bits = r.got_bits.inner()
            return expected_bits.lower() == got_bits.lower()
        except Exception as e:
                handle_maybe_spade_exception(e, traceback.extract_stack())

    def __getattribute__(self, __name: str):
        if __name.endswith("__") or __name in ["assert_eq", "is_eq", "value"]:
            return super(Field, self).__getattribute__(__name)
        else:
            try:
                return Field(
                    self.spade__,
                    self.spade__.field_of_field(self.field_ref__, __name),
                    self.dut__,
                )
            except Exception as e:
                handle_maybe_spade_exception(e, traceback.extract_stack())


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

        try:
            return Field(self.spade__, self.spade__.arg_as_field(__name), self.dut__)
        except Exception as e:
            handle_maybe_spade_exception(e, traceback.extract_stack())

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
