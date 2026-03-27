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
safe_address="$(get_config governance.upgradeSafe)"
declare -r safe_address

. "$project_root"/sh/common_safe.sh

forge build

declare version
version="$(cast call --rpc-url "$rpc_url" "$deployer_address" 'version()(string)')"
version="$(xargs -n1 echo <<<"$version")" # remove embedded quotes
declare -i version
version+=1
declare -r -i version

declare constructor_args
constructor_args="$(cast abi-encode 'constructor(uint256)' "$version")"
declare -r constructor_args

if [[ ${1:-unset} = 'deploy' ]] ; then
    shift

    declare impl_deployer
    impl_deployer="$1"
    declare -r impl_deployer
    shift

    . "$project_root"/sh/common_gas.sh

    declare initcode
    initcode="$(jq -Mr .bytecode.object < out/Deployer.sol/Deployer.json)"
    initcode="$(cast concat-hex "$initcode" "$constructor_args")"
    declare -r initcode
    declare -i gas_estimate
    gas_estimate="$(cast estimate --gas-price "$gas_price" --rpc-url "$rpc_url" --chain $chainid --from "$impl_deployer" "${extra_flags[@]}" --create "$initcode")"
    declare -r -i gas_estimate
    declare -i gas_limit
    gas_limit="$(apply_gas_multiplier $gas_estimate)"
    declare -r -i gas_limit

    declare deployed_address
    deployed_address="$(cast compute-address --rpc-url "$rpc_url" "$impl_deployer")"
    deployed_address="${deployed_address##* }"
    declare -r deployed_address

    echo '' >&2
    echo 'Duncan wrote this for his own use; if you are not using a Frame wallet, it probably will break' >&2
    echo '' >&2

    declare -a gas_price_args
    if (( chainid != 56 )) && (( chainid != 534352 )) ; then
        gas_price_args=(
            --gas-price $gas_price --priority-gas-price $gas_price
        )
    else
        gas_price_args=(--gas-price $gas_price)
    fi
    declare -r -a gas_price_args

    cast send --unlocked --from "$impl_deployer" --confirmations 10 "${gas_price_args[@]}" --gas-limit $gas_limit --rpc-url 'http://127.0.0.1:1248/' --chain $chainid "${extra_flags[@]}" --create "$initcode"

    echo 'Waiting for 1 minute for Etherscan to pick up the deployment' >&2
    sleep 60

    verify_contract "$constructor_args" "$deployed_address" src/deployer/Deployer.sol:Deployer
fi

if [[ ${1:-unset} = 'confirm' ]] ; then
    shift

    . "$project_root"/sh/common_safe_owner.sh
    . "$project_root"/sh/common_wallet_type.sh

    if [[ ${deployed_address-unset} = 'unset' ]] ; then
        declare deployed_address
        deployed_address="$1"
        declare -r deployed_address
        shift
    fi

    declare upgrade_calldata
    upgrade_calldata="$(cast calldata 'initialize(address)' "$(cast address-zero)")"
    upgrade_calldata="$(cast calldata 'upgradeAndCall(address,bytes)(bool)' "$deployed_address" "$upgrade_calldata")"
    declare -r upgrade_calldata

    declare struct_json
    struct_json="$(eip712_json "$upgrade_calldata")"
    declare -r struct_json

    declare signature
    signature="$(sign_call "$struct_json")"
    declare -r signature

    save_signature deployer_upgrade "$upgrade_calldata" "$signature"
fi
