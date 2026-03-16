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
safe_address="$(get_config governance.deploymentSafe)"
declare -r safe_address

. "$project_root"/sh/common_safe.sh

declare signer
IFS='' read -p 'What address will you submit with?: ' -e -r -i 0xEf37aD2BACD70119F141140f7B5E46Cd53a65fc4 signer
declare -r signer

. "$project_root"/sh/common_wallet_type.sh

if [[ $wallet_type != 'frame' ]] ; then
    echo 'This script only works with Frame.sh wallets due to the overly long calldata' >&2
    exit 1
fi

. "$project_root"/sh/common_safe_deployer.sh
. "$project_root"/sh/common_deploy_settler.sh
. "$project_root"/sh/common_gas.sh

while (( ${#deploy_calldatas[@]} >= 3 )) ; do
    declare -i operation="${deploy_calldatas[0]}"
    declare deploy_calldata="${deploy_calldatas[1]}"
    declare target="${deploy_calldatas[2]}"
    deploy_calldatas=( "${deploy_calldatas[@]:3:$((${#deploy_calldatas[@]}-3))}" )

    declare packed_signatures
    packed_signatures="$(retrieve_signatures settler_confirmation "$deploy_calldata" $operation "$target")"
    packed_signatures="${packed_signatures:2}"
    declare packed_signatures_length="${#packed_signatures}"
    packed_signatures_length=$(( packed_signatures_length / 2 ))
    packed_signatures_length="$(cast to-uint256 $packed_signatures_length)"
    packed_signatures_length="${packed_signatures_length:2}"

    # pad the deployment call
    deploy_calldata="${deploy_calldata:2}"
    declare deploy_calldata_length="${#deploy_calldata}"
    declare -i deploy_calldata_padding_length=$((deploy_calldata_length % 64))
    if (( deploy_calldata_padding_length )) ; then
        deploy_calldata_padding_length=$((64 - deploy_calldata_padding_length))
        deploy_calldata="$deploy_calldata""$(seq 1 $deploy_calldata_padding_length | xargs printf '0%.0s')"
    fi
    deploy_calldata_length=$(( deploy_calldata_length / 2 ))
    deploy_calldata_length="$(cast to-uint256 $deploy_calldata_length)"
    deploy_calldata_length="${deploy_calldata_length:2}"

    ## assemble the call to `execTransaction`
    # we have to do it this awkward way instead of using `cast calldata` because
    # `$deploy_calldata` is longer than allowed for a command-line argument
    declare packed_calldata
    packed_calldata="$(cast concat-hex "$execTransaction_selector" "$(cast to-uint256 "$target")" "$(cast to-uint256 0)" "$(cast to-uint256 320)" "$(cast to-uint256 $operation)" "$(cast to-uint256 0)" "$(cast to-uint256 0)" "$(cast to-uint256 0)" "$(cast to-uint256 "$(cast address-zero)")" "$(cast to-uint256 "$(cast address-zero)")" "$(cast to-uint256 $((320 + 32 + ${#deploy_calldata} / 2)))")""$deploy_calldata_length""$deploy_calldata""$packed_signatures_length""$packed_signatures"

    # again, we have to do this in an awkward fashion to avoid the command-line
    # argument length limit
    declare -i gas_estimate_retries=0
    declare gas_estimate=null
    while [[ $gas_estimate = [Nn][Uu][Ll][Ll] ]] ; do
        if (( gas_estimate_retries )) ; then
            echo 'Retrying gas estimate - attempt '"$gas_estimate_retries" >&2
            sleep 1
        fi
        gas_estimate="$(
            jq -Mc \
            '
            {
                "id": 1,
                "jsonrpc": "2.0",
                "method": "eth_estimateGas",
                "params": [
                    {
                        "from": $from,
                        "to": $to,
                        "gasPrice": $gasprice,
                        "chainId": $chainId,
                        "value": "0x0",
                        "data": $data[0]
                    }
                ]
            }
            '                                                   \
            --arg from "$signer"                                \
            --arg to "$safe_address"                            \
            --arg gasprice "0x$(bc <<<'obase=16;'"$gas_price")" \
            --arg chainId "0x$(bc <<<'obase=16;'"$chainid")"    \
            --slurpfile data <(jq -R . <<<"$packed_calldata")   \
            <<<'{}'                                             \
            |                                                   \
            curl --fail -s -X POST                              \
            -H 'Accept: application/json'                       \
            -H 'Content-Type: application/json'                 \
            --url "$rpc_url"                                    \
            --data '@-'                                         \
        )"
        gas_estimate="$(jq -rM '.result' <<<"$gas_estimate")"
        gas_estimate_retries+=1
    done
    declare -i gas_limit
    gas_limit="$(apply_gas_multiplier $gas_estimate)"

    # switch the wallet to the correct chain
    jq -Mc \
    '
    {
        "id": 1,
        "jsonrpc": "2.0",
        "method": "wallet_switchEthereumChain",
        "params": [
            {
                "chainId": $chainid,
            }
        ]
    }
    '                                                \
    --arg chainid "0x$(bc <<<'obase=16;'"$chainid")" \
    <<<'{}'                                          \
    |                                                \
    curl --fail -s -X POST                           \
    --url 'http://127.0.0.1:1248/'                   \
    --data '@-'                                      \
    &>/dev/null

    # submit the transaction
    declare txid
    txid=$(
        jq -Mc \
        '
        {
            "id": 1,
            "jsonrpc": "2.0",
            "method": "eth_sendTransaction",
            "params": [
                {
                    "from": $from,
                    "to": $to,
                    "gas": $gaslimit,
                    "gasPrice": $gasprice,
                    "value": "0x0",
                    "data": $data[0]
                }
            ]
        }
        '                                                   \
        --arg from "$signer"                                \
        --arg to "$safe_address"                            \
        --arg gaslimit "0x$(bc <<<'obase=16;'"$gas_limit")" \
        --arg gasprice "0x$(bc <<<'obase=16;'"$gas_price")" \
        --slurpfile data <(jq -R . <<<"$packed_calldata")   \
        <<<'{}'                                             \
        |                                                   \
        curl --fail -s -X POST                              \
        --url 'http://127.0.0.1:1248/'                      \
        --data '@-'                                         \
        |                                                   \
        jq -rM .result
    )
    if [[ $txid == [Nn][Uu][Ll][Ll] ]] ; then
        echo 'Transaction submission failed' >&2
        exit 1
    fi

    if [[ $(cast receipt --rpc-url "$rpc_url" --confirmations 10 "$txid" status) != '1 (success)' ]] ; then
        echo 'Transaction '"$txid"' failed' >&2
        exit 1
    fi

    SAFE_NONCE_INCREMENT=$((${SAFE_NONCE_INCREMENT:-0} + 1))
done

echo 'Contracts deployed. Run `sh/verify_settler.sh '"$chain_name"'` to verify on Etherscan.' >&2
