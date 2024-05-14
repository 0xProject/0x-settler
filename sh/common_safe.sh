declare -i chainid
chainid="$(get_config chainId)"
declare -r -i chainid
declare rpc_url
rpc_url="$(get_api_secret rpcUrl)"
declare -r rpc_url
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
nonce=$((${SAFE_NONCE_INCREMENT:-0} + nonce))
declare -r -i nonce

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
select wallet_type in ledger trezor hot frame ; do break ; done
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
    'frame')
        wallet_args=(--unlocked)
        ;;
    *)
        echo 'Unrecognized wallet type: '"$wallet_type" >&2
        exit 1
        ;;
esac

if [[ $wallet_type = 'ledger' ]] ; then
    IFS='' read -r -e -i "44'/60'/0'/0" -p 'Ledger wallet HD path (BIP32) [default '"44'/60'/0'/0"']: '
    wallet_args+=(
        --mnemonic-derivation-path "$REPLY"
    )
fi

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
    "operation": $call_type,
    "safeTxGas": 0,
    "baseGas": 0,
    "gasPrice": 0,
    "gasToken": "0x0000000000000000000000000000000000000000",
    "refundReceiver": "0x0000000000000000000000000000000000000000",
    "nonce": $nonce | tonumber'

eip712_json() {
    declare -r calldata="$1"
    shift

    declare -i call_type
    if (( $# > 0 )) ; then
        call_type="$1"
        shift
    else
        call_type=0
    fi
    declare -r -i call_type

    declare to
    if [[ $call_type == 1 ]] ; then
        to="$(get_config safe.multiCall)"
    else
        to="$deployer_address"
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
    --arg call_type "$call_type"            \
    --arg nonce "$nonce"                    \
    <<<'{}'
}

eip712_struct_hash() {
    declare -r calldata="$1"
    shift

    declare -i call_type
    if (( $# > 0 )) ; then
        call_type="$1"
        shift
    else
        call_type=0
    fi
    declare -r -i call_type

    declare to
    if [[ $call_type == 1 ]] ; then
        to="$(get_config safe.multiCall)"
    else
        to="$deployer_address"
    fi
    declare -r to

    cast keccak "$(cast abi-encode 'foo(bytes32,address,uint256,bytes32,uint8,uint256,uint256,uint256,address,address,uint256)' "$type_hash" "$to" 0 "$(cast keccak "$calldata")" "$call_type" 0 0 0 "$(cast address-zero)" "$(cast address-zero)" $nonce)"
}

eip712_hash() {
    declare -r calldata="$1"
    shift

    declare -i call_type
    if (( $# > 0 )) ; then
        call_type="$1"
        shift
    else
        call_type=0
    fi
    declare -r -i call_type

    declare struct_hash
    struct_hash="$(eip712_struct_hash "$calldata" "$call_type")"

    cast keccak "$(cast concat-hex '0x1901' "$domain_separator" "$struct_hash")"
}

# for some dumb reason, the Safe Transaction Service API requires us to compute
# this ourselves instead of computing it automatically from the other arguments
# >:(
declare -r type_hash="$(cast keccak 'SafeTx(address to,uint256 value,bytes data,uint8 operation,uint256 safeTxGas,uint256 baseGas,uint256 gasPrice,address gasToken,address refundReceiver,uint256 nonce)')"
declare -r domain_type_hash="$(cast keccak 'EIP712Domain(uint256 chainId,address verifyingContract)')"
declare -r domain_separator="$(cast keccak "$(cast abi-encode 'foo(bytes32,uint256,address)' "$domain_type_hash" $chainid "$safe_address")")"
