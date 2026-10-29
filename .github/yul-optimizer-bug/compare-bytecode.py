#!/usr/bin/env python3
"""Compares the creation and runtime bytecode of every artifact in two forge output directories.

usage: compare-bytecode.py <stock out dir> <patched out dir>

Exits non-zero when any bytecode differs, when the directories do not hold the same artifacts,
when the two builds did not use the same compiler release, when both builds used the same
compiler binary, or when nothing with bytecode was compiled.
"""

import json
import os
import sys


def artifacts(root):
    found = {}
    for dirpath, _, names in os.walk(root):
        for name in names:
            path = os.path.join(dirpath, name)
            rel = os.path.relpath(path, root)
            # build-info file names hash the full compiler version string, so they never match
            if not name.endswith(".json") or rel.startswith("build-info" + os.sep):
                continue
            with open(path) as f:
                artifact = json.load(f)
            found[rel] = {
                "bytecode": (artifact.get("bytecode") or {}).get("object"),
                "deployedBytecode": (artifact.get("deployedBytecode") or {}).get("object"),
                "compiler": ((artifact.get("metadata") or {}).get("compiler") or {}).get("version"),
            }
    return found


def release(compiler_version):
    return compiler_version.split("+", 1)[0]


def has_code(bytecode):
    # interfaces and abstract contracts have an empty "0x" object
    return bytecode not in (None, "", "0x")


def main():
    stock_dir, patched_dir = sys.argv[1], sys.argv[2]
    stock, patched = artifacts(stock_dir), artifacts(patched_dir)
    problems = []
    for rel in sorted(stock.keys() - patched.keys()):
        problems.append(f"{rel}: only in {stock_dir}")
    for rel in sorted(patched.keys() - stock.keys()):
        problems.append(f"{rel}: only in {patched_dir}")

    with_code = 0
    for rel in sorted(stock.keys() & patched.keys()):
        s, p = stock[rel], patched[rel]
        if s["compiler"] is None or p["compiler"] is None:
            problems.append(f"{rel}: compiler version missing from the artifact metadata")
        elif release(s["compiler"]) != release(p["compiler"]):
            problems.append(f"{rel}: compiled with {s['compiler']} and {p['compiler']}")
        elif s["compiler"] == p["compiler"]:
            problems.append(f"{rel}: both builds used the same compiler binary {s['compiler']}")
        if s["bytecode"] != p["bytecode"]:
            problems.append(f"{rel}: creation bytecode differs between stock and patched solc")
        if s["deployedBytecode"] != p["deployedBytecode"]:
            problems.append(f"{rel}: runtime bytecode differs between stock and patched solc")
        if has_code(s["bytecode"]) or has_code(p["bytecode"]):
            with_code += 1
    if with_code == 0:
        problems.append("no artifact with bytecode was compiled")

    print(f"compared {len(stock.keys() & patched.keys())} artifacts, {with_code} with bytecode")
    for problem in problems:
        print(problem)
    sys.exit(1 if problems else 0)


if __name__ == "__main__":
    main()
