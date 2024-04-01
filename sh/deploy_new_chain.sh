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
    declare instance="$1"
    shift
    declare key="$1"
    shift
    jq -r -M ."$instance"."$key" < ./secrets.json
}

function get_api_secret {
    jq -r -M ."$chain_name"."$1" < ./api_secrets.json
}

function get_chain_config {
    jq -r -M ."$chain_name"."$1" < ./chain_config.json
}

declare -r module_deployer="$(get_secret iceColdCoffee deployer)"
declare -r proxy_deployer="$(get_secret deployer deployer)"
declare -r -i chainid="$(get_chain_config chainId)"
declare -r rpc_url="$(get_api_secret rpcUrl)"

# safe constants
declare -r safe_factory="$(get_chain_config safeFactory)"
declare -r safe_singleton="$(get_chain_config safeSingleton)"
declare -r safe_creation_sig='proxyCreationCode()(bytes)'
declare -r safe_initcode="$(cast abi-decode "$safe_creation_sig" "$(cast call --rpc-url "$rpc_url" "$safe_factory" "$(cast calldata "$safe_creation_sig")")")"
declare -r safe_inithash="$(cast keccak "$(cast concat-hex "$safe_initcode" "$(cast to-uint256 "$safe_singleton")")")"
declare -r safe_fallback="$(get_chain_config safeFallback)"

# compute deployment safe
declare -r deployment_safe_initializer="$(
    cast calldata            \
    'setup(address[] owners,uint256 threshold,address to,bytes data,address fallbackHandler,address paymentToken,uint256 paymentAmount,address paymentReceiver)' \
    '['"$module_deployer"']' \
    1                        \
    $(cast address-zero)     \
    0x                       \
    "$safe_fallback"         \
    $(cast address-zero)     \
    0                        \
    $(cast address-zero)
)"
declare -r deployment_safe_salt="$(cast keccak "$(cast concat-hex "$(cast keccak "$deployment_safe_initializer")" 0x0000000000000000000000000000000000000000000000000000000000000000)")"
declare deployment_safe="$(cast keccak "$(cast concat-hex 0xff "$safe_factory" "$deployment_safe_salt" "$safe_inithash")")"
declare -r deployment_safe="$(cast to-check-sum-address "0x${deployment_safe:26:40}")"

# compute ugprade safe
declare -r upgrade_safe_initializer="$(
    cast calldata           \
    'setup(address[] owners,uint256 threshold,address to,bytes data,address fallbackHandler,address paymentToken,uint256 paymentAmount,address paymentReceiver)' \
    '['"$proxy_deployer"']' \
    1                       \
    $(cast address-zero)    \
    0x                      \
    "$safe_fallback"        \
    $(cast address-zero)    \
    0                       \
    $(cast address-zero)
)"
declare -r upgrade_safe_salt="$(cast keccak "$(cast concat-hex "$(cast keccak "$upgrade_safe_initializer")" 0x0000000000000000000000000000000000000000000000000000000000000000)")"
declare upgrade_safe="$(cast keccak "$(cast concat-hex 0xff "$safe_factory" "$upgrade_safe_salt" "$safe_inithash")")"
declare -r upgrade_safe="$(cast to-check-sum-address "0x${upgrade_safe:26:40}")"

declare -a maybe_broadcast=()
if [[ "${BROADCAST-no}" = [Yy]es ]] ; then
    maybe_broadcast+=(--broadcast)
fi

ICECOLDCOFFEE_DEPLOYER_KEY="$(get_secret iceColdCoffee key)" DEPLOYER_PROXY_DEPLOYER_KEY="$(get_secret deployer key)" forge script --slow --no-storage-caching --chain $chainid --rpc-url "$rpc_url" -vvvvv "${maybe_broadcast[@]}" --sig 'run(address,address,address,address,address)' script/DeploySafes.s.sol:DeploySafes "$deployment_safe" "$upgrade_safe" "$safe_factory" "$safe_singleton" "$safe_fallback"

if [[ "${BROADCAST-no}" = [Yy]es ]] ; then
    forge verify-contract --watch --chain $chainid --etherscan-api-key "$(get_api_secret etherscanKey)" --verifier-url "$(get_chain_config etherscanApi)" --constructor-args "$(cast abi-encode 'constructor(address)' "$safe")" "$(get_secret iceColdCoffee address)" src/deployer/SafeModule.sol:ZeroExSettlerDeployerSafeModule
fi
