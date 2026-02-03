#!/usr/bin/env bash

## POSIX Bash implementation of realpath
## Copied and modified from https://github.com/mkropat/sh-realpath and https://github.com/AsymLabs/realpath-lib/
## Copyright (c) 2014 Michael Kropat - MIT License
## Copyright (c) 2013 Asymmetry Laboratories - MIT License

function realpath {
    _resolve_symlinks "$(_canonicalize "$1")"
}

function _directory {
    local out slsh
    slsh=/
    out="$1"
    out="${out//$slsh$slsh/$slsh}"
    if [ "$out" = / ]; then
        echo /
        return
    fi
    out="${out%/}"
    case "$out" in
        */*)
            out="${out%/*}"
        ;;
        *)
            out=.
        ;;
    esac
    if [ "$out" ]; then
        printf '%s\n' "$out"
    else
        echo /
    fi
}

function _file {
    local out slsh
    slsh=/
    out="$1"
    out="${out//$slsh$slsh/$slsh}"
    if [ "$out" = / ]; then
        echo /
        return
    fi
    out="${out%/}"
    out="${out##*/}"
    printf '%s\n' "$out"
}

function _resolve_symlinks {
    local path pattern context
    while [ -L "$1" ]; do
        context="$(_directory "$1")"
        path="$(POSIXLY_CORRECT=y ls -ld -- "$1" 2>/dev/null)"
        pattern='*'"$(_escape "$1")"' -> '
        path="${path#$pattern}"
        set -- "$(_canonicalize "$(_prepend_context "$context" "$path")")" "$@"
        _assert_no_path_cycles "$@" || return 1
    done
    printf '%s\n' "$1"
}

function _escape {
    local out
    out=''
    local -i i
    for ((i=0; i < ${#1}; i+=1)); do
        out+='\'"${1:$i:1}"
    done
    printf '%s\n' "$out"
}

function _prepend_context {
    if [ "$1" = . ]; then
        printf '%s\n' "$2"
    else
        case "$2" in
            /* ) printf '%s\n' "$2" ;;
             * ) printf '%s\n' "$1/$2" ;;
        esac
    fi
}

function _assert_no_path_cycles {
    local target path

    if [ $# -gt 16 ]; then
        return 1
    fi

    target="$1"
    shift

    for path in "$@"; do
        if [ "$path" = "$target" ]; then
            return 1
        fi
    done
}

function _canonicalize {
    local d f
    if [ -d "$1" ]; then
        (CDPATH= cd -P "$1" 2>/dev/null && pwd -P)
    else
        d="$(_directory "$1")"
        f="$(_file "$1")"
        (CDPATH= cd -P "$d" 2>/dev/null && printf '%s/%s\n' "$(pwd -P)" "$f")
    fi
}

## end POSIX Bash implementation of realpath

set -Eeufo pipefail -o posix

declare project_root
project_root="$(_directory "$(_directory "$(realpath "${BASH_SOURCE[0]}")")")"
declare -r project_root
cd "$project_root"

. "$project_root"/sh/common.sh

if [[ $(cast keccak "$(cast code --rpc-url "$rpc_url" 0x4e59b44847b379578588920cA78FbF26c0B4956C)") != 0x2fa86add0aed31f33a762c9d88e807c475bd51d0f52bd0955754b2608f7e4989 ]] ; then
    echo 'The Arachnid deterministic deployment proxy does not exist or is corrupt' >&2
    exit 1
fi

declare signer
IFS='' read -p 'What address will you submit with?: ' -e -r -i 0xEf37aD2BACD70119F141140f7B5E46Cd53a65fc4 signer
declare -r signer

. "$project_root"/sh/common_wallet_type.sh
. "$project_root"/sh/common_gas.sh

export FOUNDRY_OPTIMIZER_RUNS=1000000
export FOUNDRY_EVM_VERSION=london
export FOUNDRY_SOLC_VERSION=0.8.28

forge clean
forge build src/multicall/MultiCall.sol

declare -i gas_estimate
gas_estimate="$(cast estimate --from "$signer" --rpc-url "$rpc_url" --gas-price $gas_price --chain $chainid $(get_config extraFlags) 0x4e59b44847b379578588920cA78FbF26c0B4956C "$(cast concat-hex 0x0000000000000000000000000000000000000031a5e6991d522b26211cf840ce "$(forge inspect src/multicall/MultiCall.sol:MultiCall bytecode)")")"
declare -r -i gas_estimate
declare -i gas_limit
gas_limit="$(apply_gas_multiplier $gas_estimate)"
declare -r -i gas_limit

declare -a maybe_broadcast=()
declare submit_rpc
if [[ ${BROADCAST-no} = [Yy]es ]] ; then
    maybe_broadcast+=(send --chain $chainid)
    if [[ $wallet_type = 'frame' ]] ; then
        submit_rpc='http://127.0.0.1:1248'
        maybe_broadcast+=(--unlocked)
    else
        submit_rpc="$rpc_url"
    fi
else
    maybe_broadcast+=(call --trace -vvvv)
    submit_rpc="$rpc_url"
fi
declare -r -a maybe_broadcast

cast "${maybe_broadcast[@]}" --from "$signer" --rpc-url "$submit_rpc" --gas-price $gas_price --gas-limit $gas_limit $(get_config extraFlags) 0x4e59b44847b379578588920cA78FbF26c0B4956C "$(cast concat-hex 0x0000000000000000000000000000000000000031a5e6991d522b26211cf840ce "$(forge inspect src/multicall/MultiCall.sol:MultiCall bytecode)")"

if [[ ${BROADCAST-no} = [Yy]es ]] ; then
    sleep 60

    verify_contract 0x 0x00000000000000CF9E3c5A26621af382fA17f24f src/multicall/MultiCall.sol:MultiCall

    echo 'Deployment is complete' >&2
    echo 'Add the following to your chain_config.json' >&2
    echo '"deployment": {' >&2
    echo '	"forwardingMultiCall": "0x00000000000000CF9E3c5A26621af382fA17f24f"' >&2
    echo '}' >&2
else
    echo 'Did not broadcast; skipping verification' >&2
fi
