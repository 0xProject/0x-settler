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
. "$project_root"/sh/common_deploy_settler.sh

declare signatures
signatures="$(curl -s "$(get_config safe.apiUrl)"'/api/v1/multisig-transactions/'"$eip712_hash"'/confirmations/?executed=false' -X GET)"
declare -r signatures

if (( $(jq -r -M .count <<<"$signatures") != 1 )) ; then
    echo 'Bad number of signatures' >&2
    exit 1
fi

declare other_signer
other_signer="$(jq -r -M '.results[0].owner' <<<"$signatures")"
declare -r other_signer
declare other_signature
other_signature="$(jq -r -M '.results[0].signature' <<<"$signatures")"
declare -r other_signature

declare signer_lower
signer_lower="$(tr '[:upper:]' '[:lower:]' <<<"$signer")"
declare -r signer_lower
declare other_signer_lower
other_signer_lower="$(tr '[:upper:]' '[:lower:]' <<<"$other_signer")"
declare -r other_signer_lower

declare signature
signature="$(cast concat-hex "$(cast to-uint256 "$signer")" "$(cast hash-zero)" 0x01)"
declare -r signature

declare packed_signatures
if [ "$other_signer_lower" \< "$signer_lower" ] ; then
    packed_signatures="$(cast concat-hex "$other_signature" "$signature")"
else
    packed_signatures="$(cast concat-hex "$signature" "$other_signature")"
fi

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


# configure gas limit
declare -r exec_sig='execTransaction(address,uint256,bytes,uint8,uint256,uint256,uint256,address,address,bytes)(bool)'
declare -r -a args=(
    "$safe_address" "$exec_sig"
    # to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver, signatures
    "$deployer_address" 0 "$deploy_calldata" 0 0 0 0 "$(cast address-zero)" "$(cast address-zero)" "$packed_signatures"
)

# set gas limit and add multiplier/headroom (again mostly for Arbitrum)
declare -i gas_estimate_multiplier
gas_estimate_multiplier="$(get_config gasMultiplierPercent)"
declare -r -i gas_estimate_multiplier
declare -i gas_limit
gas_limit="$(cast estimate --from "$signer" --rpc-url "$rpc_url" --chain $chainid "${args[@]}")"
gas_limit=$((gas_limit * gas_estimate_multiplier / 100))
declare -r -i gas_limit

if [[ $wallet_type = 'unlocked' ]] ; then
    cast send --from "$signer" --rpc-url 'http://127.0.0.1:1248/' --chain $chainid --gas-price $gas_price --gas-limit $gas_limit "${wallet_args[@]}" $(get_config extraFlags) "${args[@]}"
else
    cast send --from "$signer" --rpc-url "$rpc_url" --chain $chainid --gas-price $gas_price --gas-limit $gas_limit "${wallet_args[@]}" $(get_config extraFlags) "${args[@]}"
fi

declare -r erc721_ownerof_sig='ownerOf(uint256)(address)'
declare settler
settler="$(cast abi-decode "$erc721_ownerof_sig" "$(cast call --rpc-url "$rpc_url" "$deployer_address" "$(cast calldata "$erc721_ownerof_sig" "$feature")")")"
declare -r settler
forge verify-contract --watch --chain $chainid --etherscan-api-key "$(get_api_secret etherscanKey)" --verifier-url "$(get_config etherscanApi)" --constructor-args "$constructor_args" "$settler" src/Settler.sol:Settler
