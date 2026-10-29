#!/bin/bash
# Compiles one set of deployable contracts with the stock solc and with the patched solc and
# compares the resulting bytecode. Reads from the environment:
#   SET_PATHS     space-separated source files or directories to build
#   SET_EVM       EVM version override, or empty for the foundry.toml default
#   SET_RUNS      optimizer runs override, or empty for the foundry.toml default
#   PATCHED_SOLC  path to the patched solc binary
set -Eeufo pipefail

here=$(cd "$(dirname "$0")" && pwd)
if [[ -n ${SET_EVM:-} ]] ; then
    export FOUNDRY_EVM_VERSION=$SET_EVM
fi
if [[ -n ${SET_RUNS:-} ]] ; then
    export FOUNDRY_OPTIMIZER_RUNS=$SET_RUNS
fi
read -ra paths <<<"$SET_PATHS"
patched=$(realpath "$PATCHED_SOLC")
work=$(mktemp -d)

FOUNDRY_OUT="$work"/out-stock FOUNDRY_CACHE_PATH="$work"/cache-stock forge build -- "${paths[@]}"
FOUNDRY_OUT="$work"/out-patched FOUNDRY_CACHE_PATH="$work"/cache-patched forge build --use "$patched" -- "${paths[@]}"
python3 -I "$here"/compare-bytecode.py "$work"/out-stock "$work"/out-patched
