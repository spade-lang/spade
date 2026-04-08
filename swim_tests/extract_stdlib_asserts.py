#!/bin/env python

# A quick and dirty script to extract "doctests" from the stdlib. These doctests are
# restricted to `assert <thing>` for now

import sys
from pathlib import Path
from typing import List, Tuple

def find_spade_files(dir: Path) -> List[Path]:
    result = []
    for file in dir.iterdir():
        if file.is_dir():
            result += find_spade_files(file)
        if file.suffix == ".spade":
            result += [file]
    return result

def handle_code_block(file: Path, lines: List[Tuple[int, str]]) -> str:
    relevant_path = file.relative_to("../spade-compiler")
    result = ""
    # result = f"entity {str(relevant_path).replace("/", "__")}_{line_num}(clk: clock, rst: bool) {{\n"
    while len(lines) != 0 and (line := lines.pop(0)):
        (num, line) = line
        if line.startswith("/// ```"):
            break
        else:
            clean_line = line.replace("///", "").strip()
            source_loc = f" // {str(relevant_path)}:{num + 1}"
            result += f"    {clean_line}{source_loc}\n"

    # result += "}\n"
    result += "\n\n"
    return result
    

def extract_tests(file: Path) -> str:
    with open(file) as f:
        content = f.read()

        lines = list(enumerate(content.splitlines()))
        code_blocks = ""

        while len(lines) != 0 and (line := lines.pop(0)):
            (_line_num, line) = line

            if line.startswith("/// ```"):
                block = handle_code_block(file, lines)
                if "notest" not in line:
                    code_blocks += block

        return code_blocks

def main():
    output_file = sys.argv[1]
    spade_files = find_spade_files(Path("../spade-compiler/stdlib")) + find_spade_files(Path("../spade-compiler/core"))

    all_asserts = """
use std::array::{
    unfold,
};
use std::ops::{
    comb_div,
    comb_mod,
};

entity stdlib_asserts() {
"""
    for file in spade_files:
        all_asserts += extract_tests(file)

    all_asserts += "}"

    with open(output_file, "w") as f:
        f.write(all_asserts)

if __name__ == "__main__":
    main()
