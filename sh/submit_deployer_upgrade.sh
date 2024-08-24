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

. "$project_root"/sh/common.sh

echo 'Duncan wrote this for his own use' >&2
echo 'If you are not Duncan, you are going to have a bad time' >&2
echo 'If you are not using a frame wallet, doubly so' >&2

declare safe_address
safe_address="$(get_config governance.upgradeSafe)"
declare -r safe_address

. "$project_root"/sh/common_safe.sh

if [[ $(get_config safe.apiUrl) != 'NOT SUPPORTED' ]] ; then
    echo 'Just use the safe dApp' >&2
    echo 'Why are you running this script?' >&2
    exit 1
fi

declare new_implementation
new_implementation="$1"
declare -r new_implementation
shift

declare -a signatures=()
set +f
for confirmation in "$project_root"/deployer_upgrade_"$(get_config displayName)"_"$(git rev-parse --short=8 HEAD)"_"$new_implementation"_*_"$(nonce)".txt ; do
    signatures+=("$(<"$confirmation")")
done
set -f
declare -r -a signatures

if (( ${#signatures[@]} != 2 )) ; then
    echo 'Bad number of signatures' >&2
    exit 1
fi

declare packed_signatures
packed_signatures="$(cast concat-hex "${signatures[@]}")"
declare -r packed_signatures

declare upgrade_calldata
upgrade_calldata="$(cast calldata 'upgradeAndCall(address,bytes)' "$new_implementation" "$(cast calldata 'initialize(address)' "$(cast address-zero)")")"
declare -r upgrade_calldata

cast send --rpc-url 'http://127.0.0.1:1248' --chain $chainid --confirmations 10 --from 0xEf37aD2BACD70119F141140f7B5E46Cd53a65fc4 --unlocked $(get_config extraFlags) "$safe_address" \
     "$execTransaction_sig" "$deployer_address" 0 "$upgrade_calldata" 0 0 0 0 "$(cast address-zero)" "$(cast address-zero)" "$packed_signatures"
