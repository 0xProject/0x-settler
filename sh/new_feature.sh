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

declare deployment_safe_address
if [[ ${@: -1} = [Dd][Aa][Oo] ]] ; then
    deployment_safe_address="$(get_config governance.daoSafe)"
else
    deployment_safe_address="$(get_config governance.deploymentSafe)"
fi
declare -r deployment_safe_address

. "$project_root"/sh/common_submitter.sh

. "$project_root"/sh/common_wallet_type.sh
. "$project_root"/sh/common_gas.sh

declare -r -i feature="$1"
shift

declare -r description_file="$1"
shift

declare description
description="$(jq -MRs < "$description_file")"
description="${description:1:$((${#description} - 2))}"
declare -r description

declare -r setDescription_sig='setDescription(uint128,string)(string)'
declare -r authorize_sig='authorize(uint128,address,uint40)(bool)'

function _compat_date {
    declare -r datestring="$1"
    shift

    declare -r datefmt="$1"
    shift

    if date -d '1 second' &>/dev/null ; then
        date -u -d "${datestring:8:4}-${datestring:0:2}-${datestring:2:2}T${datestring:4:2}:${datestring:6:2}:00-00:00" "$datefmt"
    else
        date -u -j "$datestring" "$datefmt"
    fi
}

declare setDescription_call
setDescription_call="$(cast calldata "$setDescription_sig" $feature "$description")"
declare -r setDescription_call

declare new_feature_calldata
declare packed_signatures
if [[ $safe_url != 'NOT SUPPORTED' ]] && [[ ${FORCE_IGNORE_STS-No} != [Yy]es ]] ; then
    declare pending_transactions
    pending_transactions="$(load_pending_sts_safe_transactions)"
    declare -r pending_transactions
    declare ready_transactions
    ready_transactions="$(filter_sts_safe_transactions_with_threshold "$pending_transactions")"
    declare -r ready_transactions
    declare executable_transactions
    executable_transactions="$(
        filter_sts_safe_transactions_by_timelock executable "$ready_transactions"
    )"
    declare -r executable_transactions

    declare matching_transactions='[]'
    declare candidate_transaction
    declare candidate_hash
    declare candidate_last_call
    declare candidate_deadline
    declare candidate_authorize_call
    declare candidate_calldata
    while IFS= read -r candidate_transaction ; do
        candidate_hash="$(jq -Mr '.safeTxHash | ascii_downcase' <<<"$candidate_transaction")"
        if ! candidate_transaction="$(_load_sts_safe_transaction "$candidate_hash")" 2>/dev/null ; then
            continue
        fi
        if ! candidate_last_call="$(
            extract_last_multisend_call_data "$(jq -Mr .data <<<"$candidate_transaction")"
        )" 2>/dev/null ; then
            continue
        fi
        if ! candidate_deadline="$(
            extract_authorize_deadline \
                "$candidate_last_call" "$feature" "$deployment_safe_address"
        )" 2>/dev/null ; then
            continue
        fi
        candidate_authorize_call="$(
            cast calldata "$authorize_sig" $feature "$deployment_safe_address" "$candidate_deadline"
        )"
        candidate_calldata="$(
            build_multisend_calldata \
                "$deployer_address" "$setDescription_call" \
                "$deployer_address" "$candidate_authorize_call"
        )"
        if ! _require_expected_sts_safe_transaction \
            "$candidate_transaction" \
            "$multicall_address" 0 "$candidate_calldata" 1 \
            0 0 0 "$(cast address-zero)" "$(cast address-zero)" "$(nonce)" \
            2>/dev/null
        then
            continue
        fi
        matching_transactions="$(
            jq -Mc \
                --argjson transaction "$candidate_transaction" \
                '. + [$transaction]' \
                <<<"$matching_transactions"
        )"
    done < <(jq -Mc '.[]' <<<"$executable_transactions")

    declare selected_transaction_hash
    selected_transaction_hash="$(select_sts_safe_transaction_hash "$matching_transactions")"
    declare -r selected_transaction_hash
    declare selected_transaction
    selected_transaction="$(
        jq -Mce --arg hash "$selected_transaction_hash" \
            'first(.[] | select(.safeTxHash == $hash))' \
            <<<"$matching_transactions"
    )"
    declare -r selected_transaction

    new_feature_calldata="$(jq -Mr .data <<<"$selected_transaction")"
    packed_signatures="$(pack_sts_transaction_signatures "$selected_transaction")"
else
    declare auth_deadline_datestring
    # one year from the start of this month
    # MMDDhhmmCCYY
    auth_deadline_datestring="$(date -u '+%m')010000$(($(date -u '+%Y') + 1))"
    declare -r auth_deadline_datestring
    declare -i auth_deadline
    # convert to UNIX timestamp
    auth_deadline="$(_compat_date "$auth_deadline_datestring" +%s)"
    declare -r -i auth_deadline

    declare authorize_call
    authorize_call="$(cast calldata "$authorize_sig" $feature "$deployment_safe_address" "$auth_deadline")"
    declare -r authorize_call
    new_feature_calldata="$(
        build_multisend_calldata \
            "$deployer_address" "$setDescription_call" \
            "$deployer_address" "$authorize_call"
    )"
    packed_signatures="$(retrieve_signatures new_feature "$new_feature_calldata" 1)"
fi
declare -r new_feature_calldata
declare -r packed_signatures

declare -r -a args=(
    "$safe_address" "$execTransaction_sig"
    # to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver, signatures
    "$multicall_address" 0 "$new_feature_calldata" 1 0 0 0 "$(cast address-zero)" "$(cast address-zero)" "$packed_signatures"
)

declare -i gas_estimate
gas_estimate="$(cast estimate --from "$signer" --rpc-url "$rpc_url" --gas-price $gas_price --chain $chainid "${extra_flags[@]}" "${args[@]}")"
declare -r -i gas_estimate
declare -i gas_limit
gas_limit="$(apply_gas_multiplier $gas_estimate)"
declare -r -i gas_limit

if [[ $wallet_type = 'frame' ]] ; then
    cast send --timeout 300 --rpc-timeout 300 --confirmations 10 --from "$signer" --rpc-url 'http://127.0.0.1:1248/' --chain $chainid --gas-price $gas_price --gas-limit $gas_limit "${wallet_args[@]}" "${extra_flags[@]}" "${args[@]}"
else
    cast send --confirmations 10 --from "$signer" --rpc-url "$rpc_url" --chain $chainid --gas-price $gas_price --gas-limit $gas_limit "${wallet_args[@]}" "${extra_flags[@]}" "${args[@]}"
fi
