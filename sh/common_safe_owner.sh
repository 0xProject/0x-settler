declare signer

declare -r saved_safe_owner="$project_root"/config/safe_owner.txt
if [[ -f "$saved_safe_owner" && -r "$saved_safe_owner" ]] ; then
    signer="$(<"$saved_safe_owner")"
fi

function contains {
    declare -r elem="$1"
    shift

    declare i
    for i ; do
        if [[ $i == "$elem" ]] ; then
            return 0
        fi
    done

    return 1
}

if ! contains "${signer-unset}" "${owners_array[@]}" ; then
    PS3='Who are you?: '
    select signer in "${owners_array[@]}" ; do break ; done

    if [[ ${signer:-unset} = 'unset' ]] ; then
        echo 'I do not know who that is' >&2
        exit 1
    fi

    echo "$signer" >"$saved_safe_owner"
fi

declare -r signer

function sign_call {
    declare -r _sign_call_struct_json="$1"
    shift

    declare _sign_call_result
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
            <<<"$_sign_call_struct_json"
        )"
        declare -r typedDataRPC
        _sign_call_result="$(curl --fail -s -X POST --url 'http://127.0.0.1:1248' --data '@-' <<<"$typedDataRPC")"
        if [[ $_sign_call_result = *error* ]] ; then
            echo "$_sign_call_result" >&2
            return 1
        fi
        _sign_call_result="$(jq -Mr .result <<<"$_sign_call_result")"
    else
        _sign_call_result="$(cast wallet sign "${wallet_args[@]}" --from "$signer" --data "$_sign_call_struct_json")"
    fi
    declare -r _sign_call_result

    echo "$_sign_call_result"
}

function save_signature {
    declare -r _save_signature_prefix="$1"
    shift

    declare -r _save_signature_call="$1"
    shift

    declare _save_signature_signature="$1"
    shift
    if [[ ${_save_signature_signature: -2} = '00' ]] ; then
        _save_signature_signature="${_save_signature_signature:: -2}"'1b'
    elif [[ ${_save_signature_signature: -2} = '01' ]] ; then
        _save_signature_signature="${_save_signature_signature:: -2}"'1c'
    fi
    declare -r _save_signature_signature

    declare -i _save_signature_operation
    if (( $# > 0 )) ; then
        _save_signature_operation="$1"
        shift
    else
        _save_signature_operation=0
    fi
    declare -r -i _save_signature_operation

    declare _save_signature_to
    if (( $# > 0 )) ; then
        _save_signature_to="$1"
        shift
    else
        _save_signature_to="$(target $_save_signature_operation)"
    fi
    declare -r _save_signature_to

    if [[ $safe_url = 'NOT SUPPORTED' ]] || [[ ${FORCE_IGNORE_STS-No} = [Yy]es ]] ; then
        declare signature_file
        signature_file="$project_root"/"$_save_signature_prefix"_"$chain_display_name"_"$(git rev-parse --short=8 HEAD)"_"$(tr '[:upper:]' '[:lower:]' <<<"$signer")"_$(nonce).txt
        echo "$_save_signature_signature" >"$signature_file"

        echo "Signature saved to '$signature_file'" >&2
    else
        declare signing_hash
        signing_hash="$(eip712_hash "$_save_signature_call" $_save_signature_operation "$_save_signature_to")"
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
            '                                            \
            --arg to "$_save_signature_to"               \
            --slurpfile data <(jq -R . <<<"$_save_signature_call") \
            --arg operation $_save_signature_operation   \
            --arg nonce $(nonce)                         \
            --arg signing_hash "$signing_hash"           \
            --arg sender "$signer"                       \
            --arg signature "$_save_signature_signature" \
            --arg safe_address "$safe_address"           \
            <<<'{}'
        )"

        # call the API
        curl --fail --retry 5 "$safe_url"'/v1/safes/'"$safe_address"'/multisig-transactions/' -X POST -H 'Content-Type: application/json' --data '@-' <<<"$safe_multisig_transaction"

        echo 'Signature submitted' >&2
    fi
}
