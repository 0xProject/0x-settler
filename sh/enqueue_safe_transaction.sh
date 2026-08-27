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

if (( $# > 1 )) ; then
    die 'Usage: ./sh/enqueue_safe_transaction.sh <chain> [safeTxHash]'
fi
declare safe_transaction_hash="${1:-}"
safe_transaction_hash="${safe_transaction_hash,,}"
shift $(( $# > 0 ? 1 : 0 ))
if [[ -n $safe_transaction_hash && ! $safe_transaction_hash =~ ^0x[0-9a-f]{64}$ ]] ; then
    die 'Malformed Safe transaction hash: '"$safe_transaction_hash"
fi

declare safe_address
safe_address="$(get_config_strict governance.upgradeSafe)"
declare -r safe_address

. "$project_root"/sh/common_safe.sh
. "$project_root"/sh/common_safe_deployer.sh

if [[ $safe_version != 1.4.1 ]] ; then
    die 'The timelock enqueue flow requires a Safe v1.4.1 singleton'
fi

declare configured_safe_singleton
configured_safe_singleton="$(
    jq -Mr --arg chain "$chain_name" 'getpath([$chain, "safe", "v1.4.1", "singleton"])' \
        < "$project_root"/chain_config.json
)"
if [[ ${configured_safe_singleton:-null} = [nN][uU][lL][lL] ]] ; then
    die 'The v1.4.1 Safe singleton is not configured for this chain'
fi
configured_safe_singleton="$(cast to-checksum "$configured_safe_singleton")"
declare -r configured_safe_singleton

declare installed_safe_singleton
installed_safe_singleton="$(cast call --rpc-url "$rpc_url" "$safe_address" 'masterCopy()(address)')"
installed_safe_singleton="$(cast to-checksum "$installed_safe_singleton")"
declare -r installed_safe_singleton
if [[ $installed_safe_singleton != "$configured_safe_singleton" ]] ; then
    die 'The upgrade Safe does not use the configured v1.4.1 singleton'
fi

declare timelock_address
timelock_address="$(get_config_strict governance.timelock)"
timelock_address="$(cast to-checksum "$timelock_address")"
declare -r timelock_address
if [[ ${SAFE_GUARD_OVERRIDE:-${safe_guard:-null}} = [nN][uU][lL][lL] ]] ; then
    die 'The configured Guard is not installed on the upgrade Safe'
fi
if [[ $(cast to-checksum "${SAFE_GUARD_OVERRIDE:-$safe_guard}") != "$(cast to-checksum "$timelock_address")" ]] ; then
    die 'The installed Guard does not match governance.timelock'
fi
if [[ $(cast code --rpc-url "$rpc_url" "$timelock_address") = 0x ]] ; then
    die 'No contract is deployed at governance.timelock'
fi

declare guard_safe
guard_safe="$(cast call --rpc-url "$rpc_url" "$timelock_address" 'safe()(address)')"
guard_safe="$(cast to-checksum "$guard_safe")"
declare -r guard_safe
if [[ $guard_safe != "$(cast to-checksum "$safe_address")" ]] ; then
    die 'The configured Guard belongs to a different Safe'
fi

declare timelock_delay
timelock_delay="$(cast call --rpc-url "$rpc_url" "$timelock_address" 'delay()(uint24)')"
timelock_delay="$(_normalize_safe_uint "${timelock_delay%% *}")"
declare -r timelock_delay
if [[ $timelock_delay != 432000 ]] ; then
    die 'The configured Guard does not have the required 432000-second delay'
fi

if [[ -z $safe_transaction_hash ]] ; then
    declare pending_transactions
    pending_transactions="$(load_pending_sts_safe_transactions)"
    declare -r pending_transactions

    declare ready_transactions
    ready_transactions="$(filter_sts_safe_transactions_with_threshold "$pending_transactions")"
    declare -r ready_transactions

    declare unqueued_transactions
    unqueued_transactions="$(
        filter_sts_safe_transactions_by_timelock unqueued "$ready_transactions"
    )"
    declare -r unqueued_transactions

    safe_transaction_hash="$(select_sts_safe_transaction_hash "$unqueued_transactions")"
fi
declare -r safe_transaction_hash

declare safe_transaction
safe_transaction="$(_load_sts_safe_transaction "$safe_transaction_hash")"
declare -r safe_transaction

declare -a safe_transaction_fields
mapfile -t safe_transaction_fields < <(
    jq -Mr \
        '.to, .value, .data, .operation, .safeTxGas, .baseGas, .gasPrice, .gasToken, .refundReceiver, .nonce' \
        <<<"$safe_transaction"
)
declare -r -a safe_transaction_fields

declare packed_signatures
packed_signatures="$(pack_sts_transaction_signatures "$safe_transaction")"
declare -r packed_signatures

. "$project_root"/sh/common_submitter.sh
. "$project_root"/sh/common_wallet_type.sh
. "$project_root"/sh/common_gas.sh

declare -r enqueue_sig='enqueue(address,uint256,bytes,uint8,uint256,uint256,uint256,address,address,uint256,bytes)'
declare -r -a enqueue_args=(
    "$timelock_address" "$enqueue_sig"
    "${safe_transaction_fields[@]}" "$packed_signatures"
)

declare -i gas_estimate
gas_estimate="$(
    cast estimate --from "$signer" --rpc-url "$rpc_url" --gas-price $gas_price --chain $chainid \
        "${extra_flags[@]}" "${enqueue_args[@]}"
)"
declare -r -i gas_estimate
declare -i gas_limit
gas_limit="$(apply_gas_multiplier $gas_estimate)"
declare -r -i gas_limit

declare receipt
if [[ $wallet_type = 'frame' ]] ; then
    receipt="$(
        cast send --json --confirmations 10 --timeout 300 --rpc-timeout 300 --from "$signer" \
            --rpc-url 'http://127.0.0.1:1248/' --chain $chainid --gas-price $gas_price --gas-limit $gas_limit \
            "${wallet_args[@]}" "${extra_flags[@]}" "${enqueue_args[@]}"
    )"
else
    receipt="$(
        cast send --json --confirmations 10 --from "$signer" --rpc-url "$rpc_url" --chain $chainid \
            --gas-price $gas_price --gas-limit $gas_limit \
            "${wallet_args[@]}" "${extra_flags[@]}" "${enqueue_args[@]}"
    )"
fi
declare -r receipt

declare transaction_hash
transaction_hash="$(jq -Mr '.transactionHash | ascii_downcase' <<<"$receipt")"
declare -r transaction_hash
if (( $(cast to-dec "$(jq -Mr .status <<<"$receipt")") != 1 )) ; then
    die 'The enqueue transaction reverted: '"$transaction_hash"
fi

declare -r enqueued_event=0xcc7ee3ff499ff947616b6c933f01cb0c639ecfc75d7025e92c9c1cbd362383c1
declare enqueued_log
enqueued_log="$(
    jq -Mce \
        --arg guard "${timelock_address,,}" \
        --arg event "$enqueued_event" \
        --arg safeTxHash "$safe_transaction_hash" \
        '
        [
            .logs[]
            | select(
                (.address | ascii_downcase) == $guard
                and (.topics[0] | ascii_downcase) == $event
                and (.topics[1] | ascii_downcase) == $safeTxHash
            )
        ]
        | if length == 1 then .[0] else error("expected exactly one enqueue event") end
        ' \
        <<<"$receipt"
)" || die 'The receipt does not contain the expected SafeTransactionEnqueued event'
declare -r enqueued_log

declare enqueued_data
enqueued_data="$(jq -Mr .data <<<"$enqueued_log")"
declare -r enqueued_data
if [[ ! $enqueued_data =~ ^0x[0-9a-fA-F]{64} ]] ; then
    die 'The SafeTransactionEnqueued event data is malformed'
fi
declare -i timelock_end
timelock_end="$(cast to-dec "0x${enqueued_data:2:64}")"
declare -r -i timelock_end

echo 'Enqueue transaction: '"$transaction_hash"
echo 'Safe transaction:    '"$safe_transaction_hash"
echo 'timelockEnd:         '"$timelock_end"
echo 'Execution is permitted only when the block timestamp is greater than timelockEnd.'
echo 'Do not execute another Safe transaction with this nonce while this transaction waits.'
