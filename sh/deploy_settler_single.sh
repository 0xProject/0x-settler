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

if [[ ! -f sh/initial_description.md ]] ; then
    echo './sh/initial_description.md is missing' >&2
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

if [[ $(get_config isCancun) != [Tt]rue ]] ; then
    echo 'You are on the wrong branch' >&2
    exit 1
fi

declare deployer_proxy
deployer_proxy="$(get_secret deployer address)"
declare -r deployer_proxy
declare deployment_safe
deployment_safe="$(get_config governance.deploymentSafe)"
declare -r deployment_safe

declare -r -i feature=1

# not quite so secret-s
declare -i chainid
chainid="$(get_config chainId)"
declare -r -i chainid
declare rpc_url
rpc_url="$(get_api_secret rpcUrl)"
declare -r rpc_url

# encode constructor arguments for Settler
declare constructor_args
constructor_args="$(cast abi-encode 'constructor(address,bytes32,address)' "$(get_config uniV3.factory)" "$(get_config uniV3.initHash)" "$(get_config makerPsm.dai)")"
declare -r constructor_args

declare -a maybe_broadcast=()
if [[ ${BROADCAST-no} = [Yy]es ]] ; then
    maybe_broadcast+=(--broadcast)
fi

ICECOLDCOFFEE_DEPLOYER_KEY="$(get_secret iceColdCoffee key)" \
    forge script                                         \
    --slow                                               \
    --no-storage-caching                                 \
    --chain $chainid                                     \
    --rpc-url "$rpc_url"                                 \
    -vvvvv                                               \
    "${maybe_broadcast[@]}"                              \
    --sig 'run(address,address,uint128,bytes)'           \
    $(get_config extraFlags)                             \
    script/DeploySettlerSingle.s.sol:DeploySettlerSingle \
    "$deployer_proxy" "$deployment_safe" "$feature" "$constructor_args"

if [[ ${BROADCAST-no} = [Yy]es ]] ; then
    declare -a common_args=()
    common_args+=(
        --watch --chain $chainid --etherscan-api-key "$(get_api_secret etherscanKey)" --verifier-url "$(get_config etherscanApi)"
    )
    declare -r -a common_args

    declare -r erc721_ownerof_sig='ownerOf(uint256)(address)'
    declare settler
    settler="$(cast abi-decode "$erc721_ownerof_sig" "$(cast call --rpc-url "$rpc_url" "$deployer_proxy" "$(cast calldata "$erc721_ownerof_sig" "$feature")")")"
    declare -r settler

    forge verify-contract "${common_args[@]}" --constructor-args "$constructor_args" "$settler" src/Settler.sol:Settler
fi
