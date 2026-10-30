#!/bin/bash
# usage: build-patched-solc.sh <solc version> <output path>
# Builds the given solc release from source with the KnowledgeBase fix applied and writes the
# binary to the output path. The binary reports a release version string, so sources with an
# exact `pragma solidity =X.Y.Z` accept it.
set -Eeuo pipefail -o noglob

version=$1
out=$(realpath -m "$2")
patches=$(cd "$(dirname "$0")/patches" && pwd)

if [[ -f $patches/v$version.diff ]] ; then
    patch_version=$version
else
    # Fall back to the newest patch for an earlier release. `git apply` demands exact context and
    # verify-patched-solc.sh demands the right behavior, so a patch that does not fit cannot slip
    # through.
    patch_version=$(
        { ls "$patches" | sed -nE 's/^v(.*)\.diff$/\1/p' ; echo "$version" ; } \
            | sort -V | uniq | awk -v v="$version" '$0 == v { print prev ; exit } { prev = $0 }'
    )
    if [[ -z $patch_version ]] ; then
        echo 'No patch for solc '"$version"' or any earlier release in '"$patches" >&2
        exit 1
    fi
    echo 'No patch for solc '"$version"'; trying the patch for '"$patch_version" >&2
fi

work=$(mktemp -d)
git clone --depth 1 --branch v"$version" https://github.com/argotorg/solidity.git "$work"/solidity
cd "$work"/solidity
git submodule update --init --depth 1
git apply --verbose "$patches"/v"$patch_version".diff
# An empty prerelease.txt makes the build report a release version string instead of a nightly one
: > prerelease.txt

mkdir build
cd build
cmake -G 'Unix Makefiles' ..                       \
    -DCMAKE_BUILD_TYPE=Release                      \
    -DTESTS=OFF                                     \
    -DUSE_Z3=OFF                                    \
    -DUSE_CVC5=OFF                                  \
    -DPEDANTIC=OFF                                  \
    -DSOLC_LINK_STATIC=OFF
cmake --build . --target solc --parallel 2

./solc/solc --version
if ! ./solc/solc --version | grep -q '^Version: '"$version"'+' ; then
    echo 'The built solc does not report release version '"$version" >&2
    exit 1
fi
mkdir -p "$(dirname "$out")"
cp solc/solc "$out"
