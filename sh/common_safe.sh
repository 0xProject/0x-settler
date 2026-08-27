declare safe_url
safe_url="$(get_config safe.apiUrl)"
declare -r safe_url

declare safe_version
safe_version="$(cast call --rpc-url "$rpc_url" "$safe_address" 'VERSION()(string)')"
if [[ $safe_version =~ ^\"([0-9]+\.[0-9]+\.[0-9]+)\"$ ]] ; then
    safe_version="${BASH_REMATCH[1]}"
else
    die 'Safe '"$safe_address"' returned an unrecognized `VERSION()`: '"$safe_version"
fi
declare -r safe_version

declare multicall_address
multicall_address="$(jq -Mr --arg chain "$chain_name" --arg version "v$safe_version" 'getpath([$chain, "safe", $version, "multiCall"])' < "$project_root"/chain_config.json)"
declare -r multicall_address
if [[ ${multicall_address:-null} = [nN][uU][lL][lL] ]] ; then
    die 'Config key safe["v'"$safe_version"'"].multiCall is missing for chain '"$chain_name"
fi

declare deployer_address
deployer_address="$(get_config deployment.deployer)"
declare -r deployer_address

declare -i current_safe_nonce
current_safe_nonce="$(cast call --rpc-url "$rpc_url" "$safe_address" 'nonce()(uint256)')"
declare -r -i current_safe_nonce
function nonce {
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

declare upgrade_safe_address
upgrade_safe_address="$(get_config governance.upgradeSafe)"
if [[ ${upgrade_safe_address:-null} != [nN][uU][lL][lL] ]] ; then
    upgrade_safe_address="$(cast to-checksum "$upgrade_safe_address")"
fi
declare -r upgrade_safe_address

declare installed_safe_guard
installed_safe_guard="$(cast call --rpc-url "$rpc_url" "$safe_address" 'getStorageAt(uint256,uint256)(bytes)' "$(cast keccak 'guard_manager.guard.address')" 1)"
installed_safe_guard="$(cast parse-bytes32-address "$installed_safe_guard")"
declare -r installed_safe_guard

if [[ $(cast to-checksum "$safe_address") = "${upgrade_safe_address:-null}" ]] ; then
    declare configured_safe_guard
    configured_safe_guard="$(get_config governance.timelock)"
    if [[ ${configured_safe_guard:-null} != [nN][uU][lL][lL] ]] ; then
        configured_safe_guard="$(cast to-checksum "$configured_safe_guard")"
    fi
    declare -r configured_safe_guard

    declare safe_guard
    if [[ $installed_safe_guard = "$(cast address-zero)" ]] ; then
        if [[ ${configured_safe_guard:-null} != [nN][uU][lL][lL] ]] ; then
            die 'Safe '"$safe_address"' has no Guard installed, but governance.timelock says it has '"$configured_safe_guard"' for '"$chain_name"
        fi
    elif [[ ${configured_safe_guard:-null} != [nN][uU][lL][lL] ]] ; then
        die 'Safe '"$safe_address"' has an installed Guard, but governance.timelock is missing for chain '"$chain_name"
    elif [[ $installed_safe_guard != "$configured_safe_guard" ]] ; then
        die 'Safe '"$safe_address"' has unexpected Guard '"$installed_safe_guard" \
            'Expected governance.timelock '"$configured_safe_guard"
    else
        safe_guard="$configured_safe_guard"
    fi
    declare -r safe_guard
elif [[ $installed_safe_guard != "$(cast address-zero)" ]] ; then
    die 'Safe '"$safe_address"' is not the upgrade Safe, but has an installed Guard '"$installed_safe_guard"
fi

function prev_owner {
    declare _prev_owner_inp="$1"
    shift
    _prev_owner_inp="$(cast to-checksum "$_prev_owner_inp")"
    declare -r _prev_owner_inp

    declare result=0x0000000000000000000000000000000000000001
    declare _prev_owner_i
    for i in ${!owners_array[@]} ; do
        _prev_owner_i="$(cast to-checksum "${owners_array[$i]}")"
        if [[ $_prev_owner_i = "$_prev_owner_inp" ]] ; then
            break
        fi
        result="$_prev_owner_i"
    done
    declare -r result

    if [[ $result = "$(cast to-checksum "${owners_array[$((${#owners_array[@]} - 1))]}")" ]] ; then
        die 'Previous owner for "'"$_prev_owner_inp"'" not found'
    fi

    echo "$result"
}

function target {
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
declare -r multisend_selector="$(cast sig "$multisend_sig")"

function _encode_multisend_call {
    declare -r _encode_multisend_call_target="$1"
    shift

    declare -r _encode_multisend_call_data="$1"
    shift

    cast concat-hex                                                           \
        0x00                                                                  \
        "$_encode_multisend_call_target"                                      \
        "$(cast to-uint256 0)"                                                \
        "$(cast to-uint256 $(( (${#_encode_multisend_call_data} - 2) / 2 )))" \
        "$_encode_multisend_call_data"
}

function build_multisend_calldata {
    if (( $# == 0 || $# % 2 != 0 )) ; then
        die 'build_multisend_calldata expects one or more target/calldata pairs'
    fi

    declare _build_multisend_calldata_guard
    if [[ ${SAFE_GUARD_OVERRIDE:-${safe_guard:-null}} != [nN][uU][lL][lL] ]] ; then
        _build_multisend_calldata_guard="$(cast to-checksum "${SAFE_GUARD_OVERRIDE:-$safe_guard}")"
    fi
    declare -r _build_multisend_calldata_guard

    declare _build_multisend_calldata_data=0x
    declare _build_multisend_calldata_target
    declare _build_multisend_calldata_call
    while (( $# > 0 )) ; do
        _build_multisend_calldata_target="$1"
        shift
        _build_multisend_calldata_call="$1"
        shift

        _build_multisend_calldata_data="$(
            cast concat-hex \
                "$_build_multisend_calldata_data" \
                "$(_encode_multisend_call "$_build_multisend_calldata_target" "$_build_multisend_calldata_call")"
        )"

        if (( $# > 0 )) && [[ ${_build_multisend_calldata_guard:-null} != [nN][uU][lL][lL] ]] ; then
            _build_multisend_calldata_data="$(
                cast concat-hex \
                    "$_build_multisend_calldata_data" \
                    "$(_encode_multisend_call "$_build_multisend_calldata_guard" "$(cast calldata 'check()')")"
            )"
        fi
    done

    cast calldata "$multisend_sig" "$_build_multisend_calldata_data"
}

declare -r execTransaction_sig='execTransaction(address,uint256,bytes,uint8,uint256,uint256,uint256,address,address,bytes)(bool)'
declare -r execTransaction_selector="$(cast sig "$execTransaction_sig")"

declare -r eip712_message_json_template='{
    "to": $to,
    "value": 0,
    "data": $data[0],
    "operation": $operation,
    "safeTxGas": 0,
    "baseGas": 0,
    "gasPrice": 0,
    "gasToken": "0x0000000000000000000000000000000000000000",
    "refundReceiver": "0x0000000000000000000000000000000000000000",
    "nonce": $nonce | tonumber'

function eip712_json {
    declare -r _eip712_json_calldata="$1"
    shift

    declare -i _eip712_json_operation
    if (( $# > 0 )) ; then
        _eip712_json_operation="$1"
        shift
    else
        _eip712_json_operation=0
    fi
    declare -r -i _eip712_json_operation

    declare _eip712_json_to
    if (( $# > 0 )) ; then
        _eip712_json_to="$1"
        shift
    else
        _eip712_json_to="$(target $_eip712_json_operation)"
    fi
    declare -r _eip712_json_to

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
    --arg to "$_eip712_json_to"             \
    --slurpfile data <(jq -R . <<<"$_eip712_json_calldata") \
    --arg operation $_eip712_json_operation \
    --arg nonce $(nonce)                    \
    <<<'{}'
}

function eip712_struct_hash {
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

    declare calldatahash
    calldatahash="$(xxd -r -p <<<"$calldata" | cast keccak)"
    declare -r calldatahash
    cast keccak "$(cast abi-encode 'foo(bytes32,address,uint256,bytes32,uint8,uint256,uint256,uint256,address,address,uint256)' "$type_hash" "$to" 0 "$calldatahash" $operation 0 0 0 "$(cast address-zero)" "$(cast address-zero)" $(nonce))"
}

function eip712_hash {
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
