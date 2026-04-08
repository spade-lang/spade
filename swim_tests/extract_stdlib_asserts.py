#!/bin/env python

# A quick and dirty script to extract "doctests" from the stdlib. These doctests are
# restricted to `assert <thing>` for now

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

def handle_code_block(file: Path, line_num: int, lines: List[Tuple[int, str]]) -> str:
    relevant_path = file.relative_to("../spade-compiler").with_suffix("")
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
            (line_num, line) = line

            if line.startswith("/// ```"):
                code_blocks += handle_code_block(file, line_num, lines)

        return code_blocks

def main():
    spade_files = find_spade_files(Path("../spade-compiler/stdlib")) + find_spade_files(Path("../spade-compiler/core"))

    all_asserts = "entity stdlib_asserts() {"
    for file in spade_files:
        all_asserts += extract_tests(file)
    all_asserts += "}"
    print(all_asserts)

if __name__ == "__main__":
    main()
