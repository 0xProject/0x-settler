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

forge build

if [ ! -f out/Settler.sol/Settler.json ] ; then
    echo 'Cannot find Settler.json' >&2
    exit 1
fi

declare -i chainid
chainid="$(get_config chainId)"
declare -r -i chainid
declare rpc_url
rpc_url="$(get_api_secret rpcUrl)"
declare -r rpc_url
declare -r -i feature=1

declare safe_address
safe_address="$(get_config governance.deploymentSafe)"
declare -r safe_address
declare deployer_address
deployer_address="$(get_config deployment.deployer)"
declare -r deployer_address

declare -r get_owners_sig='getOwners()(address[])'
declare owners
owners="$(cast abi-decode "$get_owners_sig" "$(cast call --rpc-url "$rpc_url" "$safe_address" "$(cast calldata "$get_owners_sig")")")"
owners="${owners:1:$((${#owners} - 2))}"
owners="${owners//, /;}"
declare -r owners

declare -r nonce_sig='nonce()(uint256)'
declare -i nonce
nonce="$(cast abi-decode "$nonce_sig" "$(cast call --rpc-url "$rpc_url" "$safe_address" "$(cast calldata "$nonce_sig")")")"
declare -r -i nonce

declare constructor_args
constructor_args="$(cast abi-encode 'constructor(address,bytes32,address)' "$(get_config uniV3.factory)" "$(get_config uniV3.initHash)" "$(get_config makerPsm.dai)")"
declare -r constructor_args

declare initcode
initcode="$(cast concat-hex "$(jq -r -M .bytecode.object < out/Settler.sol/Settler.json)" "$constructor_args")"
declare -r initcode

declare -r deploy_sig='deploy(uint128,bytes)(address,uint32)'
declare deploy_calldata
deploy_calldata="$(cast calldata "$deploy_sig" $feature "$initcode")"
declare -r deploy_calldata

declare -a owners_array
IFS=';' read -r -a owners_array <<<"$owners"
declare -r -a owners_array

PS3='Who are you?: '
declare signer
select signer in "${owners_array[@]}" ; do break ; done
declare -r signer

if [[ ${signer:-unset} = 'unset' ]] ; then
    echo 'I do not know who that is' >&2
    exit 1
fi

PS3='What kind of wallet are you using? '
declare wallet_type
select wallet_type in ledger trezor hot ; do break ; done
declare -r wallet_Type

if [[ ${wallet_type:-unset} = 'unset' ]] ; then
    exit 1
fi

declare -a wallet_args
case $wallet_type in
    'ledger')
        wallet_args=(--ledger)
        ;;
    'trezor')
        wallet_args=(--trezor)
        ;;
    'hot')
        wallet_args=(--interactive)
        ;;
    *)
        echo 'Unrecognized wallet type: '"$wallet_type" >&2
        exit 1
        ;;
esac

declare -r eip712_message_json_template='{
    "to": $to,
    "value": 0,
    "data": $data,
    "operation": 0,
    "safeTxGas": 0,
    "baseGas": 0,
    "gasPrice": 0,
    "gasToken": "0x0000000000000000000000000000000000000000",
    "refundReceiver": "0x0000000000000000000000000000000000000000",
    "nonce": $nonce | tonumber'

declare eip712_data
eip712_data="$(
    jq -c \
    '
    {
      "primaryType": "SafeTx",
      "types": {
        "EIP712Domain": [
          {
            "name": "chainId",
            "type": "uint256"
          },
          {
            "name": "verifyingContract",
            "type": "address"
          }
        ],
        "SafeTx": [
          {
            "name": "to",
            "type": "address"
          },
          {
            "name": "value",
            "type": "uint256"
          },
          {
            "name": "data",
            "type": "bytes"
          },
          {
            "name": "operation",
            "type": "uint8"
          },
          {
            "name": "safeTxGas",
            "type": "uint256"
          },
          {
            "name": "baseGas",
            "type": "uint256"
          },
          {
            "name": "gasPrice",
            "type": "uint256"
          },
          {
            "name": "gasToken",
            "type": "address"
          },
          {
            "name": "refundReceiver",
            "type": "address"
          },
          {
            "name": "nonce",
            "type": "uint256"
          }
        ]
      },
      "domain": {
        "verifyingContract": $verifyingContract,
        "chainId": $chainId | tonumber
      },
      "message": '"$eip712_message_json_template"'
      }
    }
    ' \
    --arg verifyingContract "$safe_address" \
    --arg chainId "$chainid" \
    --arg to "$deployer_address" \
    --arg data "$deploy_calldata" \
    --arg nonce "$nonce" \
    <<<'{}'
)"
declare -r eip712_data

# for some dumb reason, the Safe Transaction Service API requires us to compute
# this ourselves instead of computing it automatically from the other arguments
# >:(
declare -r type_hash="$(cast keccak 'SafeTx(address to,uint256 value,bytes data,uint8 operation,uint256 safeTxGas,uint256 baseGas,uint256 gasPrice,address gasToken,address refundReceiver,uint256 nonce)')"
declare -r domain_type_hash="$(cast keccak 'EIP712Domain(uint256 chainId,address verifyingContract)')"
declare -r domain_separator="$(cast keccak "$(cast abi-encode 'foo(bytes32,uint256,address)' "$domain_type_hash" $chainid "$safe_address")")"
declare eip712_struct_hash
eip712_struct_hash="$(cast keccak "$(cast abi-encode 'foo(bytes32,address,uint256,bytes32,uint8,uint256,uint256,uint256,address,address,uint256)' "$type_hash" "$deployer_address" 0 "$(cast keccak "$deploy_calldata")" 0 0 0 0 "$(cast address-zero)" "$(cast address-zero)" $nonce)")"
declare -r eip712_struct_hash
declare eip712_hash
eip712_hash="$(cast keccak "$(cast concat-hex '0x1901' "$domain_separator" "$eip712_struct_hash")")"
declare -r eip712_hash

# sign the message
declare signature
signature="$(cast wallet sign "${wallet_args[@]}" --from "$signer" --data "$eip712_data")"
declare -r signature

# encode the Safe Transaction Service API call
declare safe_multisig_transaction
safe_multisig_transaction="$(
    jq -c \
    "$eip712_message_json_template"',
        "contractTransactionHash": $eip712Hash,
        "sender": $sender,
        "signature": $signature,
        "origin": "0xSettlerCLI"
    }
    ' \
    --arg to "$deployer_address" \
    --arg data "$deploy_calldata" \
    --arg nonce "$nonce" \
    --arg eip712Hash "$eip712_hash" \
    --arg sender "$signer" \
    --arg signature "$signature" \
    --arg safe_address "$safe_address" \
    <<<'{}'
)"
declare -r safe_multisig_transaction

# call the API
curl "$(get_config safe.apiUrl)"'/api/v1/safes/'"$safe_address"'/multisig-transactions/' -X POST -H 'Content-Type: application/json' --data "$safe_multisig_transaction"


#GET /v1/multisig-transactions/{safe_tx_hash}/?executed=false
