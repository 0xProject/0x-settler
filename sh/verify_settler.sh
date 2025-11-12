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

declare safe_address
safe_address="$(get_config governance.deploymentSafe)"
declare -r safe_address

. "$project_root"/sh/common_safe.sh
. "$project_root"/sh/common_deploy_settler.sh

declare -r erc721_ownerof_sig='ownerOf(uint256)(address)'

if [[ ${deployer_address:-unset} = 'unset' ]] || [[ $deployer_address = 'null' ]] ; then
    echo '`deployment.deployer` is unset in `chain_config.json`' >&2
    echo 'If this is your first time running this script after deploying a new chain,' >&2
    echo 'add the relevant address, but DO NOT commit.' >&2
    exit 1
fi

echo 'Verifying taker-submitted settler...' >&2

declare taker_settler
taker_settler="$(cast call --rpc-url "$rpc_url" "$deployer_address" "$erc721_ownerof_sig" 2)"
declare -r taker_settler

verify_contract "$constructor_args" "$taker_settler" "$flat_taker_source":"$chain_display_name"Settler

echo 'Verified taker-submitted Settler... verifying metatx Settler...' >&2

declare metatx_settler
metatx_settler="$(cast call --rpc-url "$rpc_url" "$deployer_address" "$erc721_ownerof_sig" 3)"
declare -r metatx_settler

verify_contract "$constructor_args" "$metatx_settler" "$flat_metatx_source":"$chain_display_name"SettlerMetaTxn

echo 'Verified metatx Settler... verifying intent Settler...' >&2

declare intent_settler
intent_settler="$(cast call --rpc-url "$rpc_url" "$deployer_address" "$erc721_ownerof_sig" 4)"
declare -r intent_settler

verify_contract "$constructor_args" "$intent_settler" "$flat_intent_source":"$chain_display_name"SettlerIntent

echo 'Verified intent Settler. All done!' >&2
