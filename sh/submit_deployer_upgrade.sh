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

echo 'Duncan wrote this for his own use' >&2
echo 'If you are not Duncan, you are going to have a bad time' >&2
echo 'If you are not using a frame wallet, doubly so' >&2

declare safe_address
safe_address="$(get_config governance.upgradeSafe)"
declare -r safe_address

. "$project_root"/sh/common_safe.sh
. "$project_root"/sh/common_safe_deployer.sh

if [[ $safe_url != 'NOT SUPPORTED' ]] ; then
    echo 'Just use the safe dApp' >&2
    echo 'Why are you running this script?' >&2
    exit 1
fi

declare new_implementation
new_implementation="$1"
declare -r new_implementation
shift

declare upgrade_calldata
upgrade_calldata="$(cast calldata 'upgradeAndCall(address,bytes)' "$new_implementation" "$(cast calldata 'initialize(address)' "$(cast address-zero)")")"
declare -r upgrade_calldata

declare packed_signatures
packed_signatures="$(retrieve_signatures deployer_upgrade "$upgrade_calldata")"
declare -r packed_signatures

cast send --rpc-url 'http://127.0.0.1:1248' --chain $chainid --confirmations 10 --from 0xEf37aD2BACD70119F141140f7B5E46Cd53a65fc4 --unlocked "${extra_flags[@]}" "$safe_address" \
     "$execTransaction_sig" "$deployer_address" 0 "$upgrade_calldata" 0 0 0 0 "$(cast address-zero)" "$(cast address-zero)" "$packed_signatures"
