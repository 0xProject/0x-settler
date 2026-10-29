#!/usr/bin/env python3
"""Emits the job matrices for the Yul optimizer bug check as GitHub Actions outputs.

A set is one `forge build` invocation whose output is bytecode that gets deployed. The build
settings mirror the deployment scripts under sh/, which define what is deployed. The solc version
of a set is the one `forge build` resolves from the pragmas of its source files.
"""

import json
import os
import re
import subprocess
import sys

# Releases whose Yul optimizer keeps stale "variable = base + offset" facts across reassignments.
FIRST_AFFECTED = (0, 8, 19)
LAST_AFFECTED = (0, 8, 37)

FIXED_SETS = [
    # sh/deploy_allowanceholder.sh
    {"name": "AllowanceHolder", "paths": ["src/allowanceholder/AllowanceHolder.sol"], "runs": "1000000"},
    # sh/deploy_new_chain.sh deploys the Deployer through `forge script` with 1,000,000 runs;
    # sh/upgrade_deployer.sh builds a replacement implementation with the default 2,000 runs.
    {"name": "Deployer (new chain)", "paths": ["src/deployer/Deployer.sol"], "runs": "1000000"},
    {"name": "Deployer (upgrade)", "paths": ["src/deployer/Deployer.sol"]},
    # sh/deploy_safeguard.sh and sh/deploy_new_chain.sh
    {"name": "SafeGuard", "paths": ["src/deployer/SafeGuard.sol"], "evm": "london", "runs": "200"},
    # sh/deploy_multicall.sh
    {"name": "MultiCall", "paths": ["src/multicall/MultiCall.sol"], "evm": "london", "runs": "1000000"},
    # sh/deploy_crosschainfactory.sh
    {
        "name": "CrossChainReceiverFactory",
        "paths": ["src/CrossChainReceiverFactory.sol"],
        "evm": "london",
        "runs": "1000000",
    },
]


def chain_sets():
    # sh/common_deploy_settler.sh and sh/common_deploy_bridge_settler.sh use the default settings
    with open("chain_config.json") as f:
        chains = [chain["displayName"] for chain in json.load(f).values()]
    return [
        {"name": f"{chain} Settlers", "paths": [f"src/chains/{chain}/"]}
        for chain in chains
        if os.path.isdir(f"src/chains/{chain}")
    ]


def resolved_versions():
    """Maps every source path to the set of solc versions forge resolves for it."""
    stdout = subprocess.run(
        ["forge", "compiler", "resolve", "--json", "-v"], check=True, capture_output=True, text=True
    ).stdout
    by_path = {}
    for entries in json.loads(stdout).values():
        for entry in entries:
            for path in entry.get("paths") or []:
                by_path.setdefault(path, set()).add(entry["version"])
    return by_path


def source_files(path):
    if not os.path.isdir(path):
        return [path]
    return sorted(
        os.path.join(dirpath, name)
        for dirpath, _, names in os.walk(path)
        for name in names
        if name.endswith(".sol")
    )


def parse_version(version):
    if not re.fullmatch(r"\d+\.\d+\.\d+", version):
        sys.exit(f"unexpected solc version string {version!r}")
    return tuple(int(part) for part in version.split("."))


def solc_version(build_set, by_path):
    versions = set()
    for path in build_set["paths"]:
        for file in source_files(path):
            if file not in by_path:
                sys.exit(f"{build_set['name']}: forge did not resolve a compiler for {file}")
            versions |= by_path[file]
    if len(versions) != 1:
        sys.exit(f"{build_set['name']}: sources resolve to several compilers: {sorted(versions)}")
    return versions.pop()


def main():
    by_path = resolved_versions()
    sets = []
    for build_set in FIXED_SETS + chain_sets():
        version = solc_version(build_set, by_path)
        sets.append(
            {
                "name": build_set["name"],
                "paths": " ".join(build_set["paths"]),
                "evm": build_set.get("evm", ""),
                "runs": build_set.get("runs", ""),
                "solc": version,
                "affected": FIRST_AFFECTED <= parse_version(version) <= LAST_AFFECTED,
            }
        )
    versions = sorted({s["solc"] for s in sets if s["affected"]}, key=parse_version)

    for s in sets:
        status = "affected" if s["affected"] else "not affected"
        print(f"{s['name']:30} solc {s['solc']:8} {status}")
    print(f"patched compilers needed: {versions}")

    lines = f"sets={json.dumps(sets)}\nversions={json.dumps(versions)}\n"
    if "GITHUB_OUTPUT" in os.environ:
        with open(os.environ["GITHUB_OUTPUT"], "a") as out:
            out.write(lines)
    else:
        sys.stdout.write(lines)


if __name__ == "__main__":
    main()
