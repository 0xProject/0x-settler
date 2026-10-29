#!/bin/bash
# usage: verify-patched-solc.sh <solc version> <patched solc path>
# Runs the upstream regression tests for the bug with the stock release and with the patched
# binary. The stock release must fail every test and the patched binary must pass every test;
# anything else means the patch did not take effect or the tests do not exercise the bug in this
# release.
set -Eeufo pipefail

version=$1
patched=$(realpath "$2")
cd "$(dirname "$0")"/repro

outcomes() {
    rm -rf out cache
    local log
    log=$(mktemp)
    # forge exits non-zero when a test fails, which is the expected outcome for the stock release
    forge test --use "$1" > "$log" 2>&1 || true
    cat "$log" >&2
    # failed tests are listed twice, once in the suite output and once in the closing summary
    sed -nE 's/^\[(PASS|FAIL)[^]]*\] ([A-Za-z0-9_]+)\(\).*/\1 \2/p' "$log" | sort -u
}

tests=(test_memory_aliasing test_storage_g_aliasing test_storage_rmw_aliasing)
expected_stock=$(printf 'FAIL %s\n' "${tests[@]}" | sort)
expected_patched=$(printf 'PASS %s\n' "${tests[@]}" | sort)

actual=$(outcomes "$version")
if [[ $actual != "$expected_stock" ]] ; then
    echo 'Stock solc '"$version"' was expected to fail every regression test but produced:' >&2
    echo "$actual" >&2
    exit 1
fi
actual=$(outcomes "$patched")
if [[ $actual != "$expected_patched" ]] ; then
    echo 'Patched solc '"$version"' was expected to pass every regression test but produced:' >&2
    echo "$actual" >&2
    exit 1
fi
echo 'Patched solc '"$version"' fixes the regression tests that stock solc '"$version"' fails'
