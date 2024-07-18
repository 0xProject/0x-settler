#!/bin/bash

## POSIX Bash implementation of realpath
## Copied and modified from https://github.com/mkropat/sh-realpath and https://github.com/AsymLabs/realpath-lib/
## Copyright (c) 2014 Michael Kropat - MIT License
## Copyright (c) 2013 Asymmetry Laboratories - MIT License

realpath() {
    _resolve_symlinks "$(_canonicalize "$1")"
}

_directory() {
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

_file() {
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

_resolve_symlinks() {
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

_escape() {
    local out
    out=''
    local -i i
    for ((i=0; i < ${#1}; i+=1)); do
        out+='\'"${1:$i:1}"
    done
    printf '%s\n' "$out"
}

_prepend_context() {
    if [ "$1" = . ]; then
        printf '%s\n' "$2"
    else
        case "$2" in
            /* ) printf '%s\n' "$2" ;;
             * ) printf '%s\n' "$1/$2" ;;
        esac
    fi
}

_assert_no_path_cycles() {
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

_canonicalize() {
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

# this duplicates `sh/common.sh`, but we don't care about the cancun/not-cancun check
if ! hash cast &>/dev/null ; then
    echo 'foundry is not installed' >&2
    exit 1
fi

if ! hash jq &>/dev/null ; then
    echo 'jq is not installed' >&2
    exit 1
fi

declare -r chain_name="$1"
shift

declare -r -i token_id="$1"
shift

declare -r -i num_addresses="${1-100}"

function get_config {
    jq -Mr ."$chain_name"."$1" < "$project_root"/chain_config.json
}

declare -i chainid
chainid="$(get_config chainId)"
declare -r -i chainid

declare deployer
deployer="$(get_config deployment.deployer)"
declare -r deployer

function create3_salt {
    declare -r -i feature="$1"
    shift

    declare -r -i nonce="$1"
    shift

    bc <<<'obase=16;'"$feature"'*2^128+'"$chainid"'*2^64+'"$nonce"
}

function create3 {
    declare factory="$1"
    shift
    factory="$(cast to-check-sum-address "$factory")"
    declare -r factory

    declare salt="$1"
    shift
    salt="$(cast to-uint256 0x"$salt")"
    declare -r salt

    # this is the "create3" shim inithash
    if [[ $(get_config isShanghai) != [Tt]rue ]] ; then
        declare -r inithash='0x1774bbdc4a308eaf5967722c7a4708ea7a3097859cb8768a10611448c29981c3'
    else
        declare -r inithash='0x3bf3f97f0be1e2c00023033eefeb4fc062ac552ff36778b17060d90b6764902f'
    fi

    declare shim
    shim="$(cast concat-hex 0xff "$factory" "$salt" "$inithash")"
    shim="$(cast keccak "$shim")"
    shim="${shim:26:40}"
    shim="$(cast to-check-sum-address "$shim")"
    declare -r shim

    declare result
    result="$(cast compute-address --nonce 1 "$shim")"
    result="${result##* }"
    declare -r result
    echo "$result"
}

declare -i nonce
for nonce in $(seq 1 $num_addresses) ; do
    create3 "$deployer" "$(create3_salt $token_id $nonce)"
done
