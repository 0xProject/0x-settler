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
. "$project_root"/sh/common_safe_owner.sh
. "$project_root"/sh/common_wallet_type.sh

declare safe_url
safe_url="$(get_config safe.apiUrl)"
declare -r safe_url

declare old_owner
old_owner="$1"
shift
old_owner="$(cast to-checksum "$old_owner")"
declare -r old_owner

declare new_owner
new_owner="$1"
shift
new_owner="$(cast to-checksum "$new_owner")"
declare -r new_owner

declare prev_owner=0x0000000000000000000000000000000000000001
for i in "${!owners_array[@]}" ; do
    if [[ "$(cast to-checksum "${owners_array[$i]}")" = "$old_owner" ]] ; then
        break
    fi
    prev_owner="$(cast to-checksum "${owners_array[$i]}")"
done
declare -r prev_owner

if [[ "$prev_owner" = "$(cast to-checksum "${owners_array[$((${#owners_array[@]} - 1))]}")" ]] ; then
    echo 'Old owner "'"$old_owner"'" not found' >&2
    exit 1
fi

declare -r swapOwner_sig='swapOwner(address,address,address)'
declare swapOwner_call
swapOwner_call="$(cast calldata "$swapOwner_sig" "$prev_owner" "$old_owner" "$new_owner")"
declare -r swapOwner_call

# declare -a calls=()

# calls+=(
#     "$(
#         cast concat-hex                                             \
#         0x00                                                        \
#         "$safe_address"                                             \
#         "$(cast to-uint256 0)"                                      \
#         "$(cast to-uint256 $(( (${#swapOwner_call} - 2) / 2 )) )"   \
#         "$swapOwner_call"
#     )"
# )

declare struct_json
struct_json="$(eip712_json "$swapOwner_call" 0 "$safe_address")"
declare -r struct_json

# sign the message
declare signature
if [[ $wallet_type = 'frame' ]] ; then
    declare typedDataRPC
    typedDataRPC="$(
        jq -Mc                 \
        '
        {
            "jsonrpc": "2.0",
            "method": "eth_signTypedData",
            "params": [
                $signer,
                .
            ],
            "id": 1
        }
        '                      \
        --arg signer "$signer" \
        <<<"$struct_json"
    )"
    declare -r typedDataRPC
    signature="$(curl --fail -s -X POST --url 'http://127.0.0.1:1248' --data "$typedDataRPC")"
    if [[ $signature = *error* ]] ; then
        echo "$signature" >&2
        exit 1
    fi
    signature="$(jq -Mr .result <<<"$signature")"
else
    signature="$(cast wallet sign "${wallet_args[@]}" --from "$signer" --data "$struct_json")"
fi
declare -r signature

# save/submit the signature
if [[ $safe_url = 'NOT SUPPORTED' ]] ; then
    declare signature_file
    signature_file="$project_root"/settler_confirmation_"$chain_display_name"_"$(git rev-parse --short=8 HEAD)"_"$(tr '[:upper:]' '[:lower:]' <<<"$signer")"_$(nonce).txt
    echo "$signature" >"$signature_file"

    echo "Signature saved to '$signature_file'" >&2
else
    declare signing_hash
    signing_hash="$(eip712_hash "$swapOwner_call" 0 "$safe_address")"
    declare -r signing_hash

    # encode the Safe Transaction Service API call
    declare safe_multisig_transaction
    safe_multisig_transaction="$(
        jq -Mc \
        "$eip712_message_json_template"',
            "contractTransactionHash": $signing_hash,
            "sender": $sender,
            "signature": $signature,
            "origin": "0xSettlerCLI"
        }
        '                                  \
        --arg to "$safe_address"           \
        --arg data "$swapOwner_call"       \
        --arg operation 0                  \
        --arg nonce $(nonce)               \
        --arg signing_hash "$signing_hash" \
        --arg sender "$signer"             \
        --arg signature "$signature"       \
        --arg safe_address "$safe_address" \
        <<<'{}'
    )"

    # call the API
    curl --fail "$safe_url"'/v1/safes/'"$safe_address"'/multisig-transactions/' -X POST -H 'Content-Type: application/json' --data "$safe_multisig_transaction"

    echo 'Signature submitted' >&2
fi
