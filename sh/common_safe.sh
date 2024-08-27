if [[ ${chainid:-unset} = 'unset' ]] ; then
    declare -i chainid
    chainid="$(get_config chainId)"
    declare -r -i chainid
fi

if [[ ${rpc_url:-unset} = 'unset' ]] ; then
    declare rpc_url
    rpc_url="$(get_api_secret rpcUrl)"
    declare -r rpc_url
fi
if [[ ${rpc_url:-unset} = 'unset' ]] ; then
    echo '`rpcUrl` is unset in `api_secrets.json` for chain "'"$chain_name"'"' >&2
    exit 1
fi

declare multicall_address
multicall_address="$(get_config safe.multiCall)"
declare -r multicall_address

declare deployer_address
deployer_address="$(get_config deployment.deployer)"
declare -r deployer_address

declare -i current_safe_nonce
current_safe_nonce="$(cast call --rpc-url "$rpc_url" "$safe_address" 'nonce()(uint256)')"
declare -r -i current_safe_nonce
nonce() {
    echo $((${SAFE_NONCE_INCREMENT:-0} + current_safe_nonce))
}

target() {
    declare -i operation
    if (( $# > 0 )) ; then
        operation="$1"
        shift
    else
        operation=0
    fi
    declare -r -i operation

    if [[ $operation == 1 ]] ; then
        echo "$multicall_address"
    else
        echo "$deployer_address"
    fi
}

# calls encoded as operation (always zero) 1 byte
#                  target address          20 bytes
#                  value                   32 bytes
#                  data length             32 bytes
#                  data                    variable
declare -r multisend_sig='multiSend(bytes)'

declare -r execTransaction_sig='execTransaction(address,uint256,bytes,uint8,uint256,uint256,uint256,address,address,bytes)(bool)'

declare -r eip712_message_json_template='{
    "to": $to,
    "value": 0,
    "data": $data,
    "operation": $operation,
    "safeTxGas": 0,
    "baseGas": 0,
    "gasPrice": 0,
    "gasToken": "0x0000000000000000000000000000000000000000",
    "refundReceiver": "0x0000000000000000000000000000000000000000",
    "nonce": $nonce | tonumber'

eip712_json() {
    declare -r calldata="$1"
    shift

    declare -i operation
    if (( $# > 0 )) ; then
        operation="$1"
        shift
    else
        operation=0
    fi
    declare -r -i operation

    jq -Mc \
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
    '                                       \
    --arg verifyingContract "$safe_address" \
    --arg chainId "$chainid"                \
    --arg to "$(target $operation)"         \
    --arg data "$calldata"                  \
    --arg operation $operation              \
    --arg nonce $(nonce)                    \
    <<<'{}'
}

eip712_struct_hash() {
    declare -r calldata="$1"
    shift

    declare -i operation
    if (( $# > 0 )) ; then
        operation="$1"
        shift
    else
        operation=0
    fi
    declare -r -i operation

    cast keccak "$(cast abi-encode 'foo(bytes32,address,uint256,bytes32,uint8,uint256,uint256,uint256,address,address,uint256)' "$type_hash" "$(target $operation)" 0 "$(cast keccak "$calldata")" $operation 0 0 0 "$(cast address-zero)" "$(cast address-zero)" $(nonce))"
}

eip712_hash() {
    declare -r calldata="$1"
    shift

    declare -i operation
    if (( $# > 0 )) ; then
        operation="$1"
        shift
    else
        operation=0
    fi
    declare -r -i operation

    declare struct_hash
    struct_hash="$(eip712_struct_hash "$calldata" $operation)"

    cast keccak "$(cast concat-hex '0x1901' "$domain_separator" "$struct_hash")"
}

# for some dumb reason, the Safe Transaction Service API requires us to compute
# this ourselves instead of computing it automatically from the other arguments
# >:(
declare -r type_hash="$(cast keccak 'SafeTx(address to,uint256 value,bytes data,uint8 operation,uint256 safeTxGas,uint256 baseGas,uint256 gasPrice,address gasToken,address refundReceiver,uint256 nonce)')"
declare -r domain_type_hash="$(cast keccak 'EIP712Domain(uint256 chainId,address verifyingContract)')"
declare -r domain_separator="$(cast keccak "$(cast abi-encode 'foo(bytes32,uint256,address)' "$domain_type_hash" $chainid "$safe_address")")"
