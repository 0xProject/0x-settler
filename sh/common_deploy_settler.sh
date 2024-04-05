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
select wallet_type in ledger trezor hot unlocked ; do break ; done
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
    'unlocked')
        wallet_args=(--unlocked)
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
