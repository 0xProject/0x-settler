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

declare module_deployer
module_deployer="$(get_secret iceColdCoffee deployer)"
declare -r module_deployer
declare proxy_deployer
proxy_deployer="$(get_secret deployer deployer)"
declare -r proxy_deployer
# we can't do key derivation in Bash, so we rely on the Foundry script to check that these are correct
declare deployer_proxy
deployer_proxy="$(get_secret deployer address)"
declare -r deployer_proxy
declare ice_cold_coffee
ice_cold_coffee="$(get_secret iceColdCoffee address)"
declare -r ice_cold_coffee
declare deployer_impl
deployer_impl="$(cast keccak "$(cast to-rlp '["0x6d4197897b4e776C96c04309cF1CA47179C2B543", "0x01"]')")"
deployer_impl="$(cast to-check-sum-address "0x${deployer_impl:26:40}")"
declare -r deployer_impl

declare -r -i feature=1
declare description
description="$(jq -MRs < ./sh/initial_description.md)"
description="${description:1:$((${#description} - 2))}"
declare -r description

# not quite so secret-s
declare -i chainid
chainid="$(get_config chainId)"
declare -r -i chainid
declare rpc_url
rpc_url="$(get_api_secret rpcUrl)"
declare -r rpc_url

# safe constants
declare safe_factory
safe_factory="$(get_config safe.factory)"
declare -r safe_factory
declare safe_singleton
safe_singleton="$(get_config safe.singleton)"
declare -r safe_singleton
declare safe_creation_sig
safe_creation_sig='proxyCreationCode()(bytes)'
declare -r safe_creation_sig
declare safe_initcode
safe_initcode="$(cast abi-decode "$safe_creation_sig" "$(cast call --rpc-url "$rpc_url" "$safe_factory" "$(cast calldata "$safe_creation_sig")")")"
declare -r safe_initcode
declare safe_inithash
safe_inithash="$(cast keccak "$(cast concat-hex "$safe_initcode" "$(cast to-uint256 "$safe_singleton")")")"
declare -r safe_inithash
declare safe_fallback
safe_fallback="$(get_config safe.fallback)"
declare -r safe_fallback
declare safe_multicall
safe_multicall="$(get_config safe.multiCall)"
declare -r safe_multicall

# compute deployment safe
declare -r setup_signature='setup(address[] owners,uint256 threshold,address to,bytes data,address fallbackHandler,address paymentToken,uint256 paymentAmount,address paymentReceiver)'
declare deployment_safe_initializer
deployment_safe_initializer="$(
    cast calldata            \
    "$setup_signature"       \
    '['"$module_deployer"']' \
    1                        \
    $(cast address-zero)     \
    0x                       \
    "$safe_fallback"         \
    $(cast address-zero)     \
    0                        \
    $(cast address-zero)
)"
declare -r deployment_safe_initializer
declare deployment_safe_salt
deployment_safe_salt="$(cast keccak "$(cast concat-hex "$(cast keccak "$deployment_safe_initializer")" "$(cast hash-zero)")")"
declare -r deployment_safe_salt
declare deployment_safe
deployment_safe="$(cast keccak "$(cast concat-hex 0xff "$safe_factory" "$deployment_safe_salt" "$safe_inithash")")"
deployment_safe="$(cast to-check-sum-address "0x${deployment_safe:26:40}")"
declare -r deployment_safe

# compute ugprade safe
declare upgrade_safe_initializer
upgrade_safe_initializer="$(
    cast calldata           \
    "$setup_signature"      \
    '['"$proxy_deployer"']' \
    1                       \
    $(cast address-zero)    \
    0x                      \
    "$safe_fallback"        \
    $(cast address-zero)    \
    0                       \
    $(cast address-zero)
)"
declare -r upgrade_safe_initializer
declare upgrade_safe_salt
upgrade_safe_salt="$(cast keccak "$(cast concat-hex "$(cast keccak "$upgrade_safe_initializer")" "$(cast hash-zero)")")"
declare -r upgrade_safe_salt
declare upgrade_safe
upgrade_safe="$(cast keccak "$(cast concat-hex 0xff "$safe_factory" "$upgrade_safe_salt" "$safe_inithash")")"
upgrade_safe="$(cast to-check-sum-address "0x${upgrade_safe:26:40}")"
declare -r upgrade_safe

# encode constructor arguments for Settler
declare constructor_args
constructor_args="$(cast abi-encode 'constructor(address,bytes32,address)' "$(get_config uniV3.factory)" "$(get_config uniV3.initHash)" "$(get_config makerPsm.dai)")"
declare -r constructor_args

# set minimum gas price to 10gwei (Arbitrum gets weird if you go lower)
declare -i gas_price
gas_price="$(cast gas-price --rpc-url "$rpc_url")"
if (( gas_price < 10000000000 )) ; then
    echo 'Setting gas price to minimum of 10 gwei' >&2
    gas_price=10000000000
fi
declare -r -i gas_price

declare -a maybe_broadcast=()
if [[ ${BROADCAST-no} = [Yy]es ]] ; then
    maybe_broadcast+=(--broadcast)
fi

ICECOLDCOFFEE_DEPLOYER_KEY="$(get_secret iceColdCoffee key)" DEPLOYER_PROXY_DEPLOYER_KEY="$(get_secret deployer key)" \
    forge script                                         \
    --slow                                               \
    --no-storage-caching                                 \
    --chain $chainid                                     \
    --rpc-url "$rpc_url"                                 \
    -vvvvv                                               \
    "${maybe_broadcast[@]}"                              \
    --sig 'run(address,address,address,address,address,address,address,address,address,address,uint128,string,bytes)' \
    $(get_config extraFlags)                             \
    script/DeploySafes.s.sol:DeploySafes                 \
    "$module_deployer" "$proxy_deployer" "$ice_cold_coffee" "$deployer_proxy" "$deployment_safe" "$upgrade_safe" "$safe_factory" "$safe_singleton" "$safe_fallback" "$safe_multicall" "$feature" "$description" "$constructor_args"

if [[ ${BROADCAST-no} = [Yy]es ]] ; then
    declare -a common_args=()
    common_args+=(
        --watch --chain $chainid --etherscan-api-key "$(get_api_secret etherscanKey)" --verifier-url "$(get_config etherscanApi)"
    )
    declare -r -a common_args
    forge verify-contract "${common_args[@]}" --constructor-args "$(cast abi-encode 'constructor(address)' "$deployment_safe")" "$ice_cold_coffee" src/deployer/SafeModule.sol:ZeroExSettlerDeployerSafeModule

    forge verify-contract "${common_args[@]}" "$deployer_impl" src/deployer/Deployer.sol:Deployer

    declare -r erc721_ownerof_sig='ownerOf(uint256)(address)'
    declare settler
    settler="$(cast abi-decode "$erc721_ownerof_sig" "$(cast call --rpc-url "$rpc_url" "$deployer_proxy" "$(cast calldata "$erc721_ownerof_sig" "$feature")")")"
    declare -r settler
    forge verify-contract "${common_args[@]}" --constructor-args "$constructor_args" "$settler" src/Settler.sol:Settler
fi

echo 'Deployment is complete' >&2
echo 'Add the following to your chain_config.json' >&2
echo '"governance": {' >&2
echo '	"upgradeSafe": "'"$upgrade_safe"'",' >&2
echo '	"deploymentSafe": "'"$deployment_safe"'",' >&2
echo '	"pause": "'"$ice_cold_coffee"'",' >&2
echo '},' >&2
echo '"deployment": {' >&2
echo '	"deployer": "'"$deployer_proxy"'",' >&2
echo '}' >&2
