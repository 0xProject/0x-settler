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

echo "This script is mostly for Duncan's use in generating the file solvers.txt ." >&2
echo "You probably don't need to run this script." >&2
echo "The only reason you'd need to run this script is if the production or staging" >&2
echo 'chain worker mnemonics have been rotated.' >&2
echo '' >&2

. "$project_root"/sh/common.sh
. "$project_root"/sh/common_secrets.sh

decrypt_secrets

declare -i num_production_addresses
num_production_addresses="$(get_secret intentWorkers limit.production)"
declare -r -i num_production_addresses

declare -i num_staging_addresses
num_staging_addresses="$(get_secret intentWorkers limit.staging)"
declare -r -i num_staging_addresses

declare -i num_mnemonics
num_mnemonics="$(get_secret intentWorkers 'mnemonic | length')"
declare -r -i num_mnemonics

declare -a solvers=()
declare privkey
declare solver

for (( i = 0 ; i < num_mnemonics ; i++ )) ; do
    declare production_mnemonic
    production_mnemonic="$(get_secret intentWorkers 'mnemonic['$i'].production')"

    declare staging_mnemonic
    staging_mnemonic="$(get_secret intentWorkers 'mnemonic['$i'].staging')"

    for (( j = 0 ; j < num_production_addresses ; j++ )) ; do
        privkey="$(cast wallet private-key "$production_mnemonic" "m/44'/60'/0'/0/$j")"
        solver="$(cast wallet address "$privkey")"
        solvers+=("$solver")
    done

    for (( j = 0 ; j < num_staging_addresses ; j++ )) ; do
        privkey="$(cast wallet private-key "$staging_mnemonic" "m/44'/60'/0'/0/$j")"
        solver="$(cast wallet address "$privkey")"
        solvers+=("$solver")
    done
done

printf '%s\n' "${solvers[@]}"
