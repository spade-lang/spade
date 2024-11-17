#!/bin/env python3

import shutil
import argparse
import re
import os
import subprocess
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('command', nargs = '?', default='run')

args = parser.parse_args()

root_dir = Path(__file__).parent
os.chdir(root_dir)

snapshot_dir = Path("snapshots")
if args.command:
    match args.command:
        case 'accept':
            files = os.listdir(snapshot_dir)
            for file in files:
                if file.endswith(".new"):
                    shutil.copy(snapshot_dir / file, snapshot_dir / file.replace(".new", ""))
                    os.remove(snapshot_dir / file)
            exit()
        case 'review':
            files = os.listdir(snapshot_dir)
            for file in files:
                if file.endswith(".new"):
                    with open(snapshot_dir / file) as f:
                        print(f.read())
                    while True:
                        print("[A]ccept/[R]ejecct")
                        answer = input()
                        match answer.lower():
                            case 'a':
                                shutil.copy(snapshot_dir / file, snapshot_dir / file.replace(".new", ""))
                                os.remove(snapshot_dir / file)
                                break
                            case 'r':
                                os.remove(snapshot_dir / file)
                                break
                            case other: 
                                pass
            exit()
        case 'run':
            pass


print("[snapshot.py] Running swim test")
test_result = subprocess.run(["swim", "test"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)

ansi_escape_re = re.compile(r"(\x9B|\x1B\[)[0-?]*[ -\/]*[@-~]")
lines = ansi_escape_re.sub('', test_result.stdout.decode("utf-8")).split('\n')

lines.reverse()


while not re.match("^=+$", lines[-1]):
    lines = lines[:-1]


cases = {}
while lines and re.match("^=+$", lines.pop()):
    header = lines.pop()
    matches = re.match(r" FAILED: test/(.+).py \[(.*)\]", header)

    (file, test_case) = (matches[1], matches[2])

    # Another ========
    lines.pop()

    # Skip cocotb info lines
    while re.match(r".+INFO", lines[-1]):
        lines = lines[:-1]


    ignore_line = lambda line: line.startswith("[INFO]") or line.startswith("VCD info: dumpfile")
    case = []
    while not ignore_line(line := lines.pop()):
        case += [line]

    cases[f"{file}_{test_case}"] = "\n".join(case)

    while lines and not re.match("^=+$", lines[-1]):
        lines = lines[:-1]

failed = False
        
for (case, content) in cases.items():
    old_path = snapshot_dir / case
    new_path = snapshot_dir / f"{case}.new"
    if (old_path).exists():
        with open(old_path) as f:
            old = f.read()

        if old != content:
            failed = True
            with open(new_path, 'w') as o:
                o.write(content)

            print("=================================================================")
            print(f" Diff in {old_path} vs {new_path}")
            print("=================================================================")
            os.system(f"diff --color=always {old_path} {new_path}")
    else:
        failed = True
        print("=================================================================")
        print(f" New snapshot saved as {new_path}")
        print("=================================================================")
        print(content)
        with open(new_path, 'w') as o:
            o.write(content)


if failed:
    exit(1)
else:
    print("No snapshot diffs!")
