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

if ! hash forge &>/dev/null ; then
    echo 'foundry is not installed' >&2
    exit 1
fi

if ! hash jq &>/dev/null ; then
    echo 'jq is not installed' >&2
    exit 1
fi

if ! hash sha256sum &>/dev/null ; then
    echo 'sha256sum is not installed' >&2
    exit 1
fi

if [ ! -f ./secrets.json ] ; then
    echo 'secrets.json is missing' >&2
    exit 1
fi

if [ ! -f ./api_secrets.json ] ; then
    echo 'api_secrets.json is missing' >&2
    exit 1
fi

if [[ $(stat -L -c '%a' --cached=never secrets.json) != '600' ]] ; then
    echo 'secrets.json permissions too lax' >&2
    echo 'run: chmod 600 secrets.json' >&2
    exit 1
fi

if [[ $(stat -L -c '%a' --cached=never api_secrets.json) != '600' ]] ; then
    echo 'api_secrets.json permissions too lax' >&2
    echo 'run: chmod 600 api_secrets.json' >&2
    exit 1
fi

if ! sha256sum -c <<<'24290900be9575d1fb6349098b1c11615a2eac8091bc486bec6cf67239b7846a  secrets.json' >/dev/null ; then
    echo 'Secrets are wrong' >&2
    exit 1
fi

declare -r chain_name="$1"
shift

if [[ $(jq -r -M ."$chain_name" < api_secrets.json) == 'null' ]] ; then
    echo "$chain_name"' is missing from api_secrets.json' >&2
    exit 1
fi

function get_secret {
    jq -r -M ."$1"."$2" < ./secrets.json
}

function get_api_secret {
    jq -r -M ."$chain_name"."$1" < ./api_secrets.json
}

function get_config {
    jq -r -M ."$chain_name"."$1" < ./chain_config.json
}

if [[ $(get_config isCancun) != [Ff]alse ]] ; then
    echo 'You are on the wrong branch' >&2
    exit 1
fi

forge create --no-cache --private-key "$(get_secret allowanceHolder key)" --chain "$(get_config chainId)" --rpc-url "$(get_api_secret rpcUrl)" --etherscan-api-key "$(get_api_secret etherscanKey)" --verifier-url "$(get_config etherscanApi)" --verify $(get_config extraFlags) src/allowanceholder/AllowanceHolder.sol:AllowanceHolder

echo 'Deployment is complete' >&2
echo 'Add the following to your chain_config.json' >&2
echo '"deployment": {' >&2
echo '	"allowanceHolder": "'"$(get_secret allowanceHolder address)"'"' >&2
echo '}' >&2
