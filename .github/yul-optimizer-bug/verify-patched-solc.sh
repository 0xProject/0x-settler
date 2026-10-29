#!/bin/bash
# usage: verify-patched-solc.sh <solc version> <patched solc path>
# Runs the upstream regression tests for the bug with the stock release and with the patched
# binary. The stock release must fail every test and the patched binary must pass every test;
# anything else means the patch did not take effect or the tests do not exercise the bug in this
# release.
set -Eeuo pipefail -o noglob

version=$1
patched=$(realpath "$2")
cd "$(dirname "$0")"/repro
work=$(mktemp -d)
trap 'rm -r -- "$work"' EXIT

expected_stock='{
    "test_memory_aliasing()": {"status": "Failure", "reason": "f(0,1): stale load"},
    "test_storage_g_aliasing()": {"status": "Failure", "reason": "g(0,2): stale load"},
    "test_storage_rmw_aliasing()": {"status": "Failure", "reason": "rmw: stale read-modify-write"}
}'
expected_patched=$(jq 'map_values({status: "Success", reason: null})' <<< "$expected_stock")

verify() {
    local compiler=$1 name=$2 expected_exit=$3 expected=$4
    local status=0
    forge test --json --use "$compiler" --out "$work/$name/out" --cache-path "$work/$name/cache" \
        > "$work/$name.json" || status=$?
    cat "$work/$name.json"
    if [[ $status -ne $expected_exit ]] || ! jq -se --argjson expected "$expected" '
        length == 1 and (.[0] |
            keys == ["test/Repro.t.sol:ReproTest"] and
            (.["test/Repro.t.sol:ReproTest"].test_results | map_values({status, reason})) == $expected
        )
    ' "$work/$name.json" > /dev/null ; then
        echo "$name solc $version: unexpected regression results (exit $status, expected $expected_exit)" >&2
        exit 1
    fi
}

verify "$version" stock 1 "$expected_stock"
verify "$patched" patched 0 "$expected_patched"
echo 'Patched solc '"$version"' fixes the regression tests that stock solc '"$version"' fails'
