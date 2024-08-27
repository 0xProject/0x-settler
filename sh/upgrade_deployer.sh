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

    # set gas limit and add multiplier/headroom (again mostly for Arbitrum)
    declare -i gas_estimate_multiplier
    gas_estimate_multiplier="$(get_config gasMultiplierPercent)"
    declare -r -i gas_estimate_multiplier
    declare initcode
    initcode="$(jq -Mr .bytecode.object < out/Deployer.sol/Deployer.json)"
    initcode="$(cast concat-hex "$initcode" "$constructor_args")"
    declare -r initcode
    declare -i gas_limit
    gas_limit="$(cast estimate --gas-price "$gas_price" --rpc-url "$rpc_url" --chain $chainid --from "$impl_deployer" --create "$initcode")"
    gas_limit=$((gas_limit * gas_estimate_multiplier / 100))
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

    cast send --unlocked --from "$impl_deployer" --confirmations 10 "${gas_price_args[@]}" --gas-limit $gas_limit --rpc-url 'http://127.0.0.1:1248/' --chain $chainid $(get_config extraFlags) --create "$initcode"

    echo 'Waiting for 1 minute for Etherscan to pick up the deployment' >&2
    sleep 60

    forge verify-contract --watch --chain $chainid --etherscan-api-key "$(get_api_secret etherscanKey)" --verifier-url "$(get_config etherscanApi)" --constructor-args "$constructor_args" "$deployed_address" src/deployer/Deployer.sol:Deployer
    if (( chainid != 81457 )) && (( chainid != 59144 )); then # sourcify doesn't support Blast or Linea
        forge verify-contract --watch --chain $chainid --verifier sourcify --constructor-args "$constructor_args" "$deployed_address" src/deployer/Deployer.sol:Deployer
    fi
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

    declare safe_url
    safe_url="$(get_config safe.apiUrl)"
    declare -r safe_url

    if [[ $safe_url = 'NOT SUPPORTED' ]] ; then
        declare signature_file
        signature_file="$project_root"/deployer_upgrade_"$(get_config displayName)"_"$(git rev-parse --short=8 HEAD)"_"$deployed_address"_"$(tr '[:upper:]' '[:lower:]' <<<"$signer")"_"$(nonce)".txt
        declare -r signature_file
        echo "$signature" >"$signature_file"
        echo "Signature saved to '$signature_file'" >&2
        exit 0
    fi

    declare signing_hash
    signing_hash="$(eip712_hash "$upgrade_calldata")"
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
        --arg to "$deployer_address"       \
        --arg data "$upgrade_calldata"     \
        --arg operation 0                  \
        --arg nonce "$(nonce)"             \
        --arg signing_hash "$signing_hash" \
        --arg sender "$signer"             \
        --arg signature "$signature"       \
        --arg safe_address "$safe_address" \
        <<<'{}'
    )"
    declare -r safe_multisig_transaction

    # call the API
    curl --fail -s "$safe_url"'/v1/safes/'"$safe_address"'/multisig-transactions/' -X POST -H 'Content-Type: application/json' --data "$safe_multisig_transaction"

    echo 'Signature submitted' >&2
fi
