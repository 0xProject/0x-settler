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

. "$project_root"/sh/common_bash_version_check.sh

if ! hash jq &>/dev/null ; then
    echo 'jq is not installed' >&2
    exit 1
fi

function get_config {
    declare -r _get_config_chain_name="$1"
    shift
    declare -r _get_config_field="$1"
    shift
    jq -Mr .'"'"$_get_config_chain_name"'"'."$_get_config_field" < "$project_root"/chain_config.json
}

declare -a chains
readarray -t chains < <(jq -rM 'keys_unsorted[]' "$project_root"/chain_config.json)
declare -r -a chains

declare -a skip_chains
readarray -t -d, skip_chains < <(printf "%s" "${SKIP_CHAINS:-}")
declare -r -a skip_chains

contains() {
    declare -r _contains_elem="$1"
    shift

    declare _contains_i
    for _contains_i ; do
        if [[ $_contains_i == "$_contains_elem" ]] ; then
            return 0
        fi
    done

    return 1
}

declare found_skip_chain=no
declare chain_name
for chain_name in "${chains[@]}" ; do
    if [[ ${SKIP_TO_CHAIN:-unset} != 'unset' ]] ; then
        if [[ $chain_name = "$SKIP_TO_CHAIN" ]] ; then
            found_skip_chain=yes
            declare -r found_skip_chain
        elif [[ $found_skip_chain != [Yy]es ]] ; then
            continue
        fi
    fi

    if [[ ${IGNORE_HARDFORK-no} != [Yy]es ]] ; then
        if [[ $(get_config "$chain_name" hardfork.shanghai) != [Tt]rue ]] ; then
            echo 'Skipping chain "'"$(get_config "$chain_name" displayName)"'" because it is not Shanghai' >&2
            continue
        fi

        if [[ $(get_config "$chain_name" hardfork.cancun) != [Ff]alse ]] ; then
            echo 'Skipping chain "'"$(get_config "$chain_name" displayName)"'" because it is Cancun' >&2
            continue
        fi

        if [[ $(get_config "$chain_name" hardfork.osaka) != [Ff]alse ]] ; then
            echo 'Skipping chain "'"$(get_config "$chain_name" displayName)"'" because it is Osaka' >&2
            continue
        fi
    fi

    if contains "$chain_name" "${skip_chains[@]}" ; then
        echo 'Skipping chain "'"$(get_config "$chain_name" displayName)"'" as requested' >&2
        continue
    fi

    echo 'Running script for chain "'"$(get_config "$chain_name" displayName)"'"...' >&2
    echo >&2
    "$1" "$chain_name" "${@:2}"
    echo >&2
    echo 'Done with chain "'"$(get_config "$chain_name" displayName)"'".' >&2
done
