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
. "$project_root"/sh/common_safe_deployer.sh

. "$project_root"/sh/common_submitter.sh

. "$project_root"/sh/common_wallet_type.sh
. "$project_root"/sh/common_gas.sh

declare -i feature="$1"
shift
if (( $# > 0 )) && [[ $1 =~ ^[0-9]+$ ]] ; then
    declare -a feature=( $feature )
    while (( $# > 0 )) && [[ $1 =~ ^[0-9]+$ ]] ; do
        feature+=( $1 )
        shift
    done
    declare -r -a feature
else
    declare -r -i feature
fi

declare deployment_safe_address
if [[ ${@: -1} = [Dd][Aa][Oo] ]] ; then
    deployment_safe_address="$(get_config governance.daoSafe)"
    if [[ $deployment_safe_address = [Nn][Uu][Ll][Ll] ]] ; then
        echo 'DAO Safe{Wallet} not configured for '"$chain_display_name" >&2
        echo 'Exiting...' >&2
        exit 0
    fi
else
    deployment_safe_address="$(get_config governance.deploymentSafe)"
fi
declare -r deployment_safe_address

declare use_sts_transactions=No
if sts_safe_transactions_enabled ; then
    use_sts_transactions=Yes
    declare executable_transactions
    executable_transactions="$(load_executable_sts_safe_transactions)"
    declare -r executable_transactions
else
    declare -i default_auth_deadline
    default_auth_deadline="$(utc_month_start_after 12)"
    declare -r -i default_auth_deadline
fi
declare -r use_sts_transactions
declare -r safe_signature_executor="$multicall_address"
declare -r authorize_sig='authorize(uint128,address,uint40)(bool)'

declare multisend_data=''
declare -i tokenid
for tokenid in "${feature[@]}" ; do
    declare renew_authority_calldata
    declare packed_signatures
    declare -a exec_args
    declare exec_call

    if [[ $use_sts_transactions = Yes ]] ; then
        declare selected_transaction
        selected_transaction="$(
            select_sts_safe_transaction \
                "$executable_transactions" "$(cast sig "$authorize_sig")"
        )"
        declare selected_deadline
        selected_deadline="$(
            extract_authorize_deadline \
                "$(jq -Mr .data <<<"$selected_transaction")" \
                "$tokenid" "$deployment_safe_address"
        )"
        renew_authority_calldata="$(
            cast calldata "$authorize_sig" \
                $tokenid "$deployment_safe_address" "$selected_deadline"
        )"
        validate_sts_safe_transaction \
            "$selected_transaction" "$authorize_sig" 0 "$renew_authority_calldata"
        packed_signatures="$(pack_sts_transaction_signatures "$selected_transaction")"
        unset -v selected_deadline
        unset -v selected_transaction
    else
        renew_authority_calldata="$(
            cast calldata "$authorize_sig" \
                $tokenid "$deployment_safe_address" $default_auth_deadline
        )"
        packed_signatures="$(retrieve_signatures renew_authority "$renew_authority_calldata")"
    fi
    exec_args=(
        # to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver, signatures
        "$(target 0)" 0 "$renew_authority_calldata" 0 0 0 0 "$(cast address-zero)" "$(cast address-zero)" "$packed_signatures"
    )
    exec_call="$(cast calldata "$execTransaction_sig" "${exec_args[@]}")"

    multisend_data="$(cast concat-hex "$multisend_data" 0x00 "$safe_address" "$(cast to-uint256 0)" "$(cast to-uint256 $(( (${#exec_call} - 2) / 2 )))" "$exec_call")"

    SAFE_NONCE_INCREMENT=$((${SAFE_NONCE_INCREMENT:-0} + 1))

    unset -v exec_call
    unset -v exec_args
    unset -v packed_signatures
    unset -v renew_authority_calldata
done
unset -v tokenid
declare -r multisend_data

declare -i gas_estimate
gas_estimate="$(cast estimate --from "$signer" --rpc-url "$rpc_url" --gas-price $gas_price --chain $chainid "${extra_flags[@]}" "$multicall_address" "$multisend_sig" "$multisend_data")"
declare -r -i gas_estimate
declare -i gas_limit
gas_limit="$(apply_gas_multiplier $gas_estimate)"
declare -r -i gas_limit

if [[ $wallet_type = 'frame' ]] ; then
    cast send --timeout 300 --rpc-timeout 300 --confirmations 10 --from "$signer" --rpc-url 'http://127.0.0.1:1248/' --chain $chainid --gas-price $gas_price --gas-limit $gas_limit "${wallet_args[@]}" "${extra_flags[@]}" "$multicall_address" "$multisend_sig" "$multisend_data"
else
    cast send --confirmations 10 --from "$signer" --rpc-url "$rpc_url" --chain $chainid --gas-price $gas_price --gas-limit $gas_limit "${wallet_args[@]}" "${extra_flags[@]}" "$multicall_address" "$multisend_sig" "$multisend_data"
fi
