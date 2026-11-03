#!/bin/bash
# Compiles one set of deployable contracts with the stock solc and with the patched solc and
# compares the resulting bytecode. Reads from the environment:
#   SET_PATHS     space-separated source files to build individually
#   SET_EVM       EVM version override, or empty for the foundry.toml default
#   SET_RUNS      optimizer runs override, or empty for the foundry.toml default
#   SET_SOLC      stock solc version
#   SET_FLATTEN   true for Settlers, whose deployment builds use flattened sources
#   PATCHED_SOLC  path to the patched solc binary
set -Eeuo pipefail -o noglob

here=$(cd "$(dirname "$0")" && pwd)
if [[ -n ${SET_EVM:-} ]] ; then
    export FOUNDRY_EVM_VERSION=$SET_EVM
fi
if [[ -n ${SET_RUNS:-} ]] ; then
    export FOUNDRY_OPTIMIZER_RUNS=$SET_RUNS
fi
read -ra paths <<<"$SET_PATHS"
if (( ${#paths[@]} == 0 )) ; then
    echo 'No source files selected for comparison' >&2
    exit 1
fi
patched=$(realpath "$PATCHED_SOLC")
work=$(mktemp -d)
flat_dir=
trap 'rm -r -- "$work"; if [[ -n $flat_dir ]]; then rm -r -- "$flat_dir"; fi' EXIT

if [[ ${SET_FLATTEN:-false} == true ]] ; then
    mkdir -p src/flat
    flat_dir=$(mktemp -d src/flat/yul-optimizer-bug.XXXXXX)
fi

failed=0
for source in "${paths[@]}" ; do
    name=${source##*/}
    if [[ -n $flat_dir ]] ; then
        chain=$(basename "$(dirname "$source")")
        flat="$flat_dir/${chain}${name%.sol}Flat.sol"
        forge flatten -o "$flat" "$source"
        source=$flat
    fi
    FOUNDRY_OUT="$work/$name/out-stock" FOUNDRY_CACHE_PATH="$work/$name/cache-stock" \
        forge build --use "$SET_SOLC" -- "$source"
    FOUNDRY_OUT="$work/$name/out-patched" FOUNDRY_CACHE_PATH="$work/$name/cache-patched" \
        forge build --use "$patched" -- "$source"
    if ! node "$here/../../js/compare-bytecode.js" "$work/$name/out-stock" "$work/$name/out-patched" ; then
        failed=1
    fi
done
exit "$failed"
