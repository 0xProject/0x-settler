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

declare safe_address
safe_address="$(get_config governance.deploymentSafe)"
declare -r safe_address

. "$project_root"/sh/common_safe.sh

declare signer
IFS='' read -p 'What address will you submit with?: ' -e -r -i 0xEf37aD2BACD70119F141140f7B5E46Cd53a65fc4 signer
declare -r signer

. "$project_root"/sh/common_wallet_type.sh
. "$project_root"/sh/common_deploy_settler.sh

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

while (( ${#deploy_calldatas[@]} >= 2 )) ; do
    declare -i operation="${deploy_calldatas[0]}"
    declare deploy_calldata="${deploy_calldatas[1]}"
    deploy_calldatas=( "${deploy_calldatas[@]:2:$((${#deploy_calldatas[@]}-2))}" )

    declare signing_hash
    signing_hash="$(eip712_hash "$deploy_calldata" $operation)"

    declare -a signatures=()
    if [[ $safe_url = 'NOT SUPPORTED' ]] ; then
        set +f
        for confirmation in "$project_root"/settler_confirmation_"$chain_display_name"_"$(git rev-parse --short=8 HEAD)"_*_$(nonce).txt ; do
            signatures+=("$(<"$confirmation")")
        done
        set -f

        if (( ${#signatures[@]} != 2 )) ; then
            echo 'Bad number of signatures' >&2
            exit 1
        fi
    else
        declare signatures_json
        signatures_json="$(curl --fail -s "$safe_url"'/v1/multisig-transactions/'"$signing_hash"'/confirmations/?executed=false' -X GET)"

        if (( $(jq -Mr .count <<<"$signatures_json") != 2 )) ; then
            echo 'Bad number of signatures' >&2
            exit 1
        fi

        if [ "$(jq -Mr '.results[1].owner' <<<"$signatures_json" | tr '[:upper:]' '[:lower:]')" \< "$(jq -Mr '.results[0].owner' <<<"$signatures_json" | tr '[:upper:]' '[:lower:]')" ] ; then
            signatures+=( "$(jq -Mr '.results[1].signature' <<<"$signatures_json")" )
            signatures+=( "$(jq -Mr '.results[0].signature' <<<"$signatures_json")" )
        else
            signatures+=( "$(jq -Mr '.results[0].signature' <<<"$signatures_json")" )
            signatures+=( "$(jq -Mr '.results[1].signature' <<<"$signatures_json")" )
        fi
    fi

    declare packed_signatures
    packed_signatures="$(cast concat-hex "${signatures[@]}")"

    # configure gas limit
    declare -a args=(
        "$safe_address" "$execTransaction_sig"
        # to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver, signatures
        "$(target $operation)" 0 "$deploy_calldata" $operation 0 0 0 "$(cast address-zero)" "$(cast address-zero)" "$packed_signatures"
    )

    # set gas limit and add multiplier/headroom (again mostly for Arbitrum)
    declare -i gas_limit
    gas_limit="$(cast estimate --from "$signer" --rpc-url "$rpc_url" --gas-price $gas_price --chain $chainid "${args[@]}")"
    gas_limit=$((gas_limit * gas_estimate_multiplier / 100))

    if [[ $wallet_type = 'frame' ]] ; then
        cast send --confirmations 10 --from "$signer" --rpc-url 'http://127.0.0.1:1248/' --chain $chainid --gas-price $gas_price --gas-limit $gas_limit "${wallet_args[@]}" $(get_config extraFlags) "${args[@]}"
    else
        cast send --confirmations 10 --from "$signer" --rpc-url "$rpc_url" --chain $chainid --gas-price $gas_price --gas-limit $gas_limit "${wallet_args[@]}" $(get_config extraFlags) "${args[@]}"
    fi

    SAFE_NONCE_INCREMENT=$((${SAFE_NONCE_INCREMENT:-0} + 1))
done

echo 'Contracts deployed. Run `sh/verify_settler.sh '"$chain_name"'` to verify on Etherscan.' >&2
