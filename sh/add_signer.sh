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
if [[ ${@: -1} = [Uu]pgrade ]] ; then
    safe_address="$(get_config governance.upgradeSafe)"
else
    safe_address="$(get_config governance.deploymentSafe)"
fi
declare -r safe_address

. "$project_root"/sh/common_safe.sh

declare signer
IFS='' read -p 'What address will you submit with?: ' -e -r -i 0xEf37aD2BACD70119F141140f7B5E46Cd53a65fc4 signer
declare -r signer

. "$project_root"/sh/common_safe_deployer.sh
. "$project_root"/sh/common_wallet_type.sh

declare new_owner
new_owner="$1"
shift
new_owner="$(cast to-checksum "$new_owner")"
declare -r new_owner

declare -r getThreshold_sig='getThreshold()(uint256)'
declare -i threshold
threshold="$(cast call --rpc-url "$rpc_url" "$safe_address" "$getThreshold_sig")"
declare -r -i threshold

declare -r addOwner_sig='addOwnerWithThreshold(address,uint256)'
declare addOwner_call
addOwner_call="$(cast calldata "$addOwner_sig" "$new_owner" $threshold)"
declare -r addOwner_call

# set minimum gas price to (mostly for Arbitrum and BNB)
declare -i min_gas_price
min_gas_price="$(get_config minGasPriceGwei)"
min_gas_price=$((min_gas_price * 1000000000))
declare -r -i min_gas_price
declare -i gas_price
gas_price="$(cast gas-price --rpc-url "$rpc_url")"
if (( gas_price < min_gas_price )) ; then
    echo 'Setting gas price to minimum of '$((min_gas_price / 1000000000))' gwei' >&2
    gas_price=$min_gas_price
fi
declare -r -i gas_price
declare -i gas_estimate_multiplier
gas_estimate_multiplier="$(get_config gasMultiplierPercent)"
declare -r -i gas_estimate_multiplier

declare packed_signatures
packed_signatures="$(retrieve_signatures add_signer "$addOwner_call" 0 "$safe_address")"
declare -r packed_signatures

# configure gas limit
declare -r -a args=(
    "$safe_address" "$execTransaction_sig"
    # to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver, signatures
    "$safe_address" 0 "$addOwner_call" 0 0 0 0 "$(cast address-zero)" "$(cast address-zero)" "$packed_signatures"
)

# set gas limit and add multiplier/headroom (again mostly for Arbitrum)
declare -i gas_limit
gas_limit="$(cast estimate --from "$signer" --rpc-url "$rpc_url" --gas-price $gas_price --chain $chainid "${args[@]}")"
gas_limit=$((gas_limit * gas_estimate_multiplier / 100))
declare -r -i gas_limit

if [[ $wallet_type = 'frame' ]] ; then
    cast send --confirmations 10 --from "$signer" --rpc-url 'http://127.0.0.1:1248/' --chain $chainid --gas-price $gas_price --gas-limit $gas_limit "${wallet_args[@]}" $(get_config extraFlags) "${args[@]}"
else
    cast send --confirmations 10 --from "$signer" --rpc-url "$rpc_url" --chain $chainid --gas-price $gas_price --gas-limit $gas_limit "${wallet_args[@]}" $(get_config extraFlags) "${args[@]}"
fi
