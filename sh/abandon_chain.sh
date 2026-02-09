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
. "$project_root"/sh/common_secrets.sh

decrypt_secrets

# Determine which safe to abandon based on last argument
declare safe_address
declare initial_owner
if [[ ${@: -1} = [Uu]pgrade ]] ; then
    safe_address="$(get_config governance.upgradeSafe)"
    # Upgrade safe goes back to deployer.deployer (the deployer proxy deployer)
    initial_owner="$(get_secret deployer deployer)"
else
    safe_address="$(get_config governance.deploymentSafe)"
    # Deployment safe goes back to iceColdCoffee.deployer
    initial_owner="$(get_secret iceColdCoffee deployer)"
fi
declare -r safe_address
declare -r initial_owner

echo "Abandoning Safe: $safe_address" >&2
echo "Will set sole owner to: $initial_owner" >&2

. "$project_root"/sh/common_safe.sh

declare signer
IFS='' read -p 'What address will you submit with?: ' -e -r -i 0xEf37aD2BACD70119F141140f7B5E46Cd53a65fc4 signer
declare -r signer

. "$project_root"/sh/common_safe_deployer.sh
. "$project_root"/sh/common_wallet_type.sh
. "$project_root"/sh/common_gas.sh

# Verify the initial owner is not already the only owner
if (( ${#owners_array[@]} == 1 )) && [[ $(cast to-checksum "${owners_array[0]}") = $(cast to-checksum "$initial_owner") ]] ; then
    echo 'Safe is already abandoned (initial owner is the only owner)' >&2
    exit 0
fi

declare -r removeOwner_sig='removeOwner(address,address,uint256)'
declare -r swapOwner_sig='swapOwner(address,address,address)'
declare -r sentinel='0x0000000000000000000000000000000000000001'

declare -a calls=()

# Remove owners until only one remains
declare -a current_owners=("${owners_array[@]}")

while (( ${#current_owners[@]} > 1 )) ; do
    declare owner_to_remove="${current_owners[0]}"

    declare removeOwner_call
    removeOwner_call="$(cast calldata "$removeOwner_sig" "$sentinel" "$owner_to_remove" 1)"

    calls+=(
        "$(
            cast concat-hex                                              \
            0x00                                                         \
            "$safe_address"                                              \
            "$(cast to-uint256 0)"                                       \
            "$(cast to-uint256 "$(((${#removeOwner_call} - 2) / 2))")"   \
            "$removeOwner_call"
        )"
    )

    # Update working state
    current_owners=("${current_owners[@]:1}")
done

# Swap the last remaining owner with initial_owner
declare last_owner="${current_owners[0]}"

declare swapOwner_call
swapOwner_call="$(cast calldata "$swapOwner_sig" "$sentinel" "$last_owner" "$initial_owner")"
declare -r swapOwner_call

calls+=(
    "$(
        cast concat-hex                                            \
        0x00                                                       \
        "$safe_address"                                            \
        "$(cast to-uint256 0)"                                     \
        "$(cast to-uint256 "$(((${#swapOwner_call} - 2) / 2))")"   \
        "$swapOwner_call"
    )"
)

# Wrap in multiSend call
declare multisend_calldata
multisend_calldata="$(cast calldata "$multisend_sig" "$(cast concat-hex "${calls[@]}")")"
declare -r multisend_calldata

declare packed_signatures
packed_signatures="$(retrieve_signatures abandon_chain "$multisend_calldata" 1)"
declare -r packed_signatures

declare -r -a args=(
    "$safe_address" "$execTransaction_sig"
    # to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver, signatures
    "$multicall_address" 0 "$multisend_calldata" 1 0 0 0 "$(cast address-zero)" "$(cast address-zero)" "$packed_signatures"
)

declare -i gas_estimate
gas_estimate="$(cast estimate --from "$signer" --rpc-url "$rpc_url" --gas-price $gas_price --chain $chainid "${extra_flags[@]}" "${args[@]}")"
declare -r -i gas_estimate
declare -i gas_limit
gas_limit="$(apply_gas_multiplier $gas_estimate)"
declare -r -i gas_limit

if [[ $wallet_type = 'frame' ]] ; then
    cast send --confirmations 10 --from "$signer" --rpc-url 'http://127.0.0.1:1248/' --chain $chainid --gas-price $gas_price --gas-limit $gas_limit "${wallet_args[@]}" "${extra_flags[@]}" "${args[@]}"
else
    cast send --confirmations 10 --from "$signer" --rpc-url "$rpc_url" --chain $chainid --gas-price $gas_price --gas-limit $gas_limit "${wallet_args[@]}" "${extra_flags[@]}" "${args[@]}"
fi

echo "Safe abandoned successfully!" >&2
