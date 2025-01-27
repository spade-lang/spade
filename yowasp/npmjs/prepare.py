import os
import re
import tomllib
import json
import subprocess

with open("../../Cargo.toml", "rb") as f:
    data = tomllib.load(f)
    spade_version_raw = data["workspace"]["package"]["version"]

spade_git_rev_list_raw = subprocess.check_output([
    "git", "rev-list", "HEAD"
], encoding="utf-8", cwd="../../").split()
local_git_rev_list_raw = subprocess.check_output([
    "git", "rev-list", "HEAD"
], encoding="utf-8").split()


spade_version = re.match(r"^(\d+)\.(\d+).(\d+)?$", spade_version_raw)
spade_major  = int(spade_version[1])
spade_minor  = int(spade_version[2])
spade_patch = int(spade_version[3])

spade_commit = spade_git_rev_list_raw[0]
local_commit = local_git_rev_list_raw[0]

version = f"{spade_major}.{spade_minor + 1}.{spade_patch}-dev{len(spade_git_rev_list_raw)}.{len(local_git_rev_list_raw)}.{spade_commit[0:6]}-{local_commit[0:6]}"
print(f"version {version}")

with open("package-in.json", "rt") as f:
    package_json = json.load(f)
package_json["version"] = version
with open("package.json", "wt") as f:
    json.dump(package_json, f, indent=2)
