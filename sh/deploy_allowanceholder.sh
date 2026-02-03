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
. "$project_root"/sh/common_secrets.sh

decrypt_secrets

. "$project_root"/sh/common_gas.sh

export FOUNDRY_OPTIMIZER_RUNS=1000000
export FOUNDRY_SOLC_VERSION=0.8.25
export FOUNDRY_EVM_HARDFORK=cancun

forge clean
forge build src/allowanceholder/AllowanceHolder.sol

declare allowanceholder_initcode
allowanceholder_initcode="$(jq -rM '.bytecode.object' < out/AllowanceHolder.sol/AllowanceHolder.json)"
declare -r allowanceholder_initcode

declare -i gas_limit
declare -a maybe_broadcast=()
if [[ ${BROADCAST-no} = [Yy]es ]] ; then
    declare -i gas_estimate
    gas_estimate="$(cast estimate --from "$(get_secret allowanceHolder deployer)" --rpc-url "$rpc_url" --gas-price $gas_price --chain $chainid $(get_config extraFlags) --create "$allowanceholder_initcode")"
    declare -r -i gas_estimate

    gas_limit="$(apply_gas_multiplier $gas_estimate)"

    maybe_broadcast+=(send --chain $chainid --private-key)
    maybe_broadcast+=("$(get_secret allowanceHolder key)")
else
    gas_limit=$eip7825_gas_limit
    maybe_broadcast+=(call --trace -vvvv)
fi
declare -r -i gas_limit
declare -r -a maybe_broadcast

cast "${maybe_broadcast[@]}" --from "$(get_secret allowanceHolder deployer)" --rpc-url "$rpc_url" --gas-price $gas_price --gas-limit $gas_limit $(get_config extraFlags) --create "$allowanceholder_initcode"

if [[ ${BROADCAST-no} = [Yy]es ]] ; then
    sleep 60

    verify_contract 0x "$(get_secret allowanceHolder address)" src/allowanceholder/AllowanceHolder.sol:AllowanceHolder

    echo 'Deployment is complete' >&2
    echo 'Add the following to your chain_config.json' >&2
    echo '"deployment": {' >&2
    echo '	"allowanceHolder": "'"$(get_secret allowanceHolder address)"'"' >&2
    echo '}' >&2
else
    echo 'Did not broadcast; skipping verification' >&2
fi
