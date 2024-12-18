declare safe_url
safe_url="$(get_config safe.apiUrl)"
declare -r safe_url

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

declare -r get_owners_sig='getOwners()(address[])'
declare owners
owners="$(cast call --rpc-url "$rpc_url" "$safe_address" "$get_owners_sig")"
owners="${owners:1:$((${#owners} - 2))}"
owners="${owners//, /;}"
declare -r owners

declare -a owners_array
IFS=';' read -r -a owners_array <<<"$owners"
declare -r -a owners_array

prev_owner() {
    declare inp="$1"
    shift
    inp="$(cast to-checksum "$inp")"
    declare -r inp

    declare result=0x0000000000000000000000000000000000000001
    declare owner_i
    for i in ${!owners_array[@]} ; do
        owner_i="$(cast to-checksum "${owners_array[$i]}")"
        if [[ $owner_i = "$inp" ]] ; then
            break
        fi
        result="$owner_i"
    done
    declare -r result

    if [[ $result = "$(cast to-checksum "${owners_array[$((${#owners_array} - 1))]}")" ]] ; then
        echo 'Old owner "'"$inp"'" not found' >&2
        return 1
    fi

    echo "$result"
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

    declare to
    if (( $# > 0 )) ; then
        to="$1"
        shift
    else
        to="$(target $operation)"
    fi
    declare -r to

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
    --arg to "$to"                          \
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

    declare to
    if (( $# > 0 )) ; then
        to="$1"
        shift
    else
        to="$(target $operation)"
    fi
    declare -r to

    cast keccak "$(cast abi-encode 'foo(bytes32,address,uint256,bytes32,uint8,uint256,uint256,uint256,address,address,uint256)' "$type_hash" "$to" 0 "$(cast keccak "$calldata")" $operation 0 0 0 "$(cast address-zero)" "$(cast address-zero)" $(nonce))"
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

    declare to
    if (( $# > 0 )) ; then
        to="$1"
        shift
    else
        to="$(target $operation)"
    fi
    declare -r to

    declare struct_hash
    struct_hash="$(eip712_struct_hash "$calldata" $operation "$to")"

    cast keccak "$(cast concat-hex '0x1901' "$domain_separator" "$struct_hash")"
}

# for some dumb reason, the Safe Transaction Service API requires us to compute
# this ourselves instead of computing it automatically from the other arguments
# >:(
declare -r type_hash="$(cast keccak 'SafeTx(address to,uint256 value,bytes data,uint8 operation,uint256 safeTxGas,uint256 baseGas,uint256 gasPrice,address gasToken,address refundReceiver,uint256 nonce)')"
declare -r domain_type_hash="$(cast keccak 'EIP712Domain(uint256 chainId,address verifyingContract)')"
declare -r domain_separator="$(cast keccak "$(cast abi-encode 'foo(bytes32,uint256,address)' "$domain_type_hash" $chainid "$safe_address")")"
