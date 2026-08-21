function _normalize_safe_uint {
    declare _normalize_safe_uint_value="$1"
    shift

    if [[ ! $_normalize_safe_uint_value =~ ^[0-9]+$ ]] ; then
        die 'Invalid Safe transaction integer: '"$_normalize_safe_uint_value"
    fi
    # The inner expansion is the leading run of zeros; the outer strips it.
    _normalize_safe_uint_value="${_normalize_safe_uint_value#"${_normalize_safe_uint_value%%[!0]*}"}"
    echo "${_normalize_safe_uint_value:-0}"
}

function _normalize_safe_address {
    declare _normalize_safe_address_value="$1"
    shift

    if [[ ! $_normalize_safe_address_value =~ ^0[xX][0-9a-fA-F]{40}$ ]] ; then
        die 'Invalid Safe transaction address: '"$_normalize_safe_address_value"
    fi
    cast to-checksum "0x${_normalize_safe_address_value:2}"
}

function _normalize_safe_bytes {
    echo "${1,,}"
}

function _require_same {
    declare -r _require_same_normalize="$1"
    shift
    declare -r _require_same_field="$1"
    shift
    declare _require_same_actual
    _require_same_actual="$("$_require_same_normalize" "$1")"
    shift
    declare -r _require_same_actual
    declare _require_same_expected
    _require_same_expected="$("$_require_same_normalize" "$1")"
    shift
    declare -r _require_same_expected

    if [[ $_require_same_actual != "$_require_same_expected" ]] ; then
        die 'STS '"$_require_same_field"' does not match the locally generated transaction'
    fi
}

function _require_same_safe_address {
    _require_same _normalize_safe_address "$@"
}

function _require_same_safe_uint {
    _require_same _normalize_safe_uint "$@"
}

function _require_same_safe_bytes {
    _require_same _normalize_safe_bytes "$@"
}

function _require_precise_jq_integers {
    if [[ $(jq -nr '9007199254740993') != 9007199254740993 ]] ; then
        die 'jq must preserve arbitrary-precision JSON integers for Safe transaction validation'
    fi
}

function _load_sts_safe_transaction {
    declare -r _load_sts_safe_transaction_hash="${1,,}"
    shift

    if [[ $safe_url = 'NOT SUPPORTED' ]] ; then
        die 'The Safe Transaction Service is required for this operation'
    fi
    _require_precise_jq_integers
    if [[ ! $_load_sts_safe_transaction_hash =~ ^0x[0-9a-f]{64}$ ]] ; then
        die 'Malformed Safe transaction hash: '"$_load_sts_safe_transaction_hash"
    fi

    declare _load_sts_safe_transaction_json
    _load_sts_safe_transaction_json="$(
        curl --show-error --fail-with-body --retry 5 -s \
            "$safe_url/v1/multisig-transactions/$_load_sts_safe_transaction_hash/"
    )"

    jq -Me \
        '
        def address: type == "string" and test("^0[xX][0-9a-fA-F]{40}$");
        def bytes: type == "string" and test("^0[xX]([0-9a-fA-F]{2})*$");
        def uint:
            (type == "string" or type == "number")
            and (tostring | test("^[0-9]+$"));
        (.safe | address)
        and (.safeTxHash | type == "string" and test("^0[xX][0-9a-fA-F]{64}$"))
        and (.to | address)
        and (.value | uint)
        and (.data | bytes)
        and (.operation | uint)
        and (.safeTxGas | uint)
        and (.baseGas | uint)
        and (.gasPrice | uint)
        and (.gasToken | address)
        and (.refundReceiver | address)
        and (.nonce | uint)
        and (.confirmations | type == "array")
        '
        <<<"$_load_sts_safe_transaction_json" >/dev/null \
    || {
        die 'STS returned a malformed or null Safe transaction field'
    }

    _load_sts_safe_transaction_json="$(
        jq -Mc \
            '
            .safe |= ascii_downcase
            | .safeTxHash |= ascii_downcase
            | .to |= ascii_downcase
            | .data |= ascii_downcase
            | .gasToken |= ascii_downcase
            | .refundReceiver |= ascii_downcase
            ' \
            <<<"$_load_sts_safe_transaction_json"
    )"
    declare -r _load_sts_safe_transaction_json

    declare -a _load_sts_safe_transaction_fields
    mapfile -t _load_sts_safe_transaction_fields < <(
        jq -Mr \
            '.safe, .safeTxHash, .to, .value, .data, .operation, .safeTxGas, .baseGas, .gasPrice, .gasToken, .refundReceiver, .nonce' \
            <<<"$_load_sts_safe_transaction_json"
    )
    declare -r -a _load_sts_safe_transaction_fields

    _require_same_safe_address \
        safe "${_load_sts_safe_transaction_fields[0]}" "$safe_address"
    _require_same_safe_bytes \
        safeTxHash "${_load_sts_safe_transaction_fields[1]}" "$_load_sts_safe_transaction_hash"

    declare _load_sts_safe_transaction_computed_hash
    _load_sts_safe_transaction_computed_hash="$(
        cast call --rpc-url "$rpc_url" "$safe_address" \
            'getTransactionHash(address,uint256,bytes,uint8,uint256,uint256,uint256,address,address,uint256)(bytes32)' \
            "${_load_sts_safe_transaction_fields[@]:2}"
    )"
    declare -r _load_sts_safe_transaction_computed_hash
    _require_same_safe_bytes \
        safeTxHash "$_load_sts_safe_transaction_computed_hash" "$_load_sts_safe_transaction_hash"

    echo "$_load_sts_safe_transaction_json"
}

function load_pending_sts_safe_transactions {
    if [[ $safe_url = 'NOT SUPPORTED' ]] ; then
        die 'The Safe Transaction Service is required for this operation'
    fi
    _require_precise_jq_integers

    declare _load_pending_sts_safe_transactions_page
    _load_pending_sts_safe_transactions_page="$(
        curl --show-error --fail-with-body --retry 5 -s \
            "$safe_url/v1/safes/$safe_address/multisig-transactions/?executed=false&nonce__gte=$current_safe_nonce&ordering=nonce%2Ccreated%2Cmodified&limit=100"
    )"
    declare -r _load_pending_sts_safe_transactions_page

    # load only a single page; die instead of paginating past 100 pending txs
    jq -Me \
        '
        (.next == null)
        and (.results | type == "array")
        and all(.results[];
            .safeTxHash | type == "string" and test("^0[xX][0-9a-fA-F]{64}$")
        )
        and ((.results | map(.safeTxHash | ascii_downcase) | unique | length) == (.results | length))
        ' \
        <<<"$_load_pending_sts_safe_transactions_page" >/dev/null \
    || {
        die 'STS returned a malformed, truncated, or duplicate pending-transaction list'
    }

    jq -Mc .results <<<"$_load_pending_sts_safe_transactions_page"
}

function sts_safe_transactions_enabled {
    [[ $safe_url != 'NOT SUPPORTED' && ${FORCE_IGNORE_STS-No} != [Yy]es ]]
}

function _require_expected_sts_safe_transaction {
    declare -r _require_expected_sts_safe_transaction_json="$1"
    shift

    declare -a _require_expected_sts_safe_transaction_fields
    mapfile -t _require_expected_sts_safe_transaction_fields < <(
        jq -Mr '.to, .value, .data, .operation, .safeTxGas, .baseGas, .gasPrice, .gasToken, .refundReceiver, .nonce' \
            <<<"$_require_expected_sts_safe_transaction_json"
    )
    declare -r -a _require_expected_sts_safe_transaction_fields

    declare -i _require_expected_sts_safe_transaction_index=0
    declare _require_expected_sts_safe_transaction_spec
    for _require_expected_sts_safe_transaction_spec in \
        to:address value:uint data:bytes operation:uint safeTxGas:uint \
        baseGas:uint gasPrice:uint gasToken:address refundReceiver:address nonce:uint
    do
        "_require_same_safe_${_require_expected_sts_safe_transaction_spec#*:}" \
            "${_require_expected_sts_safe_transaction_spec%%:*}" \
            "${_require_expected_sts_safe_transaction_fields[$_require_expected_sts_safe_transaction_index]}" \
            "$1"
        shift
        _require_expected_sts_safe_transaction_index+=1
    done
}

function _safe_transaction_data {
    cast call --rpc-url "$rpc_url" "$safe_address" \
        'encodeTransactionData(address,uint256,bytes,uint8,uint256,uint256,uint256,address,address,uint256)(bytes)' \
        "$@"
}

function _is_current_safe_owner {
    declare -r _is_current_safe_owner_candidate="${1,,}"
    shift

    declare _is_current_safe_owner_owner
    for _is_current_safe_owner_owner in "${owners_array[@]}" ; do
        if [[ ${_is_current_safe_owner_owner,,} = "$_is_current_safe_owner_candidate" ]] ; then
            return 0
        fi
    done
    return 1
}

function _normalize_safe_confirmations {
    declare -r _normalize_safe_confirmations_signing_hash="$1"
    shift
    declare -r _normalize_safe_confirmations_json="$1"
    shift

    jq -Me \
        '
        type == "array"
        and all(.[];
            (.owner | type == "string" and test("^0[xX][0-9a-fA-F]{40}$"))
            and (.signature | type == "string" and test("^0[xX]([0-9a-fA-F]{2}){65,}$"))
        )
        ' \
        <<<"$_normalize_safe_confirmations_json" >/dev/null \
    || {
        die 'STS returned a malformed Safe confirmation'
    }

    declare _normalize_safe_confirmations_result='[]'
    declare _normalize_safe_confirmations_owner
    declare _normalize_safe_confirmations_signature
    declare _normalize_safe_confirmations_body
    declare _normalize_safe_confirmations_v
    declare -i _normalize_safe_confirmations_length
    declare _normalize_safe_confirmations_derived_owner
    declare _normalize_safe_confirmations_source_offset
    declare _normalize_safe_confirmations_contract_length
    declare _normalize_safe_confirmations_contract_signature
    declare _normalize_safe_confirmations_recovery_signature
    while IFS=$'\t' read -r _normalize_safe_confirmations_owner _normalize_safe_confirmations_signature ; do
        _normalize_safe_confirmations_contract_signature=''
        _normalize_safe_confirmations_owner="$(
            _normalize_safe_address "$_normalize_safe_confirmations_owner"
        )"
        if ! _is_current_safe_owner "$_normalize_safe_confirmations_owner" ; then
            die 'Confirmation signer is not a current Safe owner: '"$_normalize_safe_confirmations_owner"
        fi

        _normalize_safe_confirmations_signature="${_normalize_safe_confirmations_signature,,}"
        _normalize_safe_confirmations_body="${_normalize_safe_confirmations_signature:2}"
        _normalize_safe_confirmations_length=$((${#_normalize_safe_confirmations_body} / 2))
        _normalize_safe_confirmations_v="${_normalize_safe_confirmations_body:128:2}"

        case $_normalize_safe_confirmations_v in
            00)
                _normalize_safe_confirmations_derived_owner="$(
                    cast to-checksum "0x${_normalize_safe_confirmations_body:24:40}"
                )"
                _require_same_safe_address \
                    owner \
                    "$_normalize_safe_confirmations_derived_owner" \
                    "$_normalize_safe_confirmations_owner"

                _normalize_safe_confirmations_source_offset="$(
                    cast to-dec "0x${_normalize_safe_confirmations_body:64:64}"
                )"
                if [[ ! $_normalize_safe_confirmations_source_offset =~ ^[0-9]{1,9}$ ]] \
                    || (( _normalize_safe_confirmations_source_offset < 65 )) \
                    || (( _normalize_safe_confirmations_source_offset + 32 > _normalize_safe_confirmations_length ))
                then
                    die 'Malformed contract-owner signature offset'
                fi

                _normalize_safe_confirmations_contract_length="$(
                    cast to-dec \
                        "0x${_normalize_safe_confirmations_body:$((_normalize_safe_confirmations_source_offset * 2)):64}"
                )"
                if [[ ! $_normalize_safe_confirmations_contract_length =~ ^[0-9]{1,9}$ ]] \
                    || (( _normalize_safe_confirmations_source_offset + 32 + _normalize_safe_confirmations_contract_length > _normalize_safe_confirmations_length ))
                then
                    die 'Malformed contract-owner signature length'
                fi

                _normalize_safe_confirmations_contract_signature="0x${_normalize_safe_confirmations_body:$(((_normalize_safe_confirmations_source_offset + 32) * 2)):$((_normalize_safe_confirmations_contract_length * 2))}"
                ;;
            01)
                if (( _normalize_safe_confirmations_length != 65 )) \
                    || [[ ${_normalize_safe_confirmations_body:0:24} != 000000000000000000000000 ]] \
                    || [[ ${_normalize_safe_confirmations_body:64:64} != 0000000000000000000000000000000000000000000000000000000000000000 ]]
                then
                    die 'Malformed approved-hash confirmation'
                fi
                _normalize_safe_confirmations_derived_owner="$(
                    cast to-checksum "0x${_normalize_safe_confirmations_body:24:40}"
                )"
                _require_same_safe_address \
                    owner \
                    "$_normalize_safe_confirmations_derived_owner" \
                    "$_normalize_safe_confirmations_owner"
                ;;
            1b|1c)
                if (( _normalize_safe_confirmations_length != 65 )) \
                    || ! cast wallet verify --no-hash \
                        --address "$_normalize_safe_confirmations_owner" \
                        "$_normalize_safe_confirmations_signing_hash" \
                        "$_normalize_safe_confirmations_signature" >/dev/null
                then
                    die 'Invalid EIP-712 Safe confirmation from '"$_normalize_safe_confirmations_owner"
                fi
                ;;
            1f|20)
                if (( _normalize_safe_confirmations_length != 65 )) ; then
                    die 'Malformed eth_sign Safe confirmation'
                fi
                _normalize_safe_confirmations_recovery_signature="${_normalize_safe_confirmations_signature:: -2}"
                if [[ $_normalize_safe_confirmations_v = 1f ]] ; then
                    _normalize_safe_confirmations_recovery_signature+='1b'
                else
                    _normalize_safe_confirmations_recovery_signature+='1c'
                fi
                if ! cast wallet verify \
                    --address "$_normalize_safe_confirmations_owner" \
                    "$_normalize_safe_confirmations_signing_hash" \
                    "$_normalize_safe_confirmations_recovery_signature" >/dev/null
                then
                    die 'Invalid eth_sign Safe confirmation from '"$_normalize_safe_confirmations_owner"
                fi
                ;;
            *)
                die 'Unsupported Safe confirmation type: 0x'"$_normalize_safe_confirmations_v"
                ;;
        esac

        _normalize_safe_confirmations_result="$(
            jq -Mc \
                --arg owner "$_normalize_safe_confirmations_owner" \
                --arg signature "$_normalize_safe_confirmations_signature" \
                --arg contractSignature "$_normalize_safe_confirmations_contract_signature" \
                '. + [{owner: $owner, signature: $signature, contractSignature: $contractSignature}]' \
                <<<"$_normalize_safe_confirmations_result"
        )"
    done < <(jq -Mr '.[] | [.owner, .signature] | @tsv' <<<"$_normalize_safe_confirmations_json")

    jq -Mce \
        '
        sort_by(.owner | ascii_downcase)
        | if (map(.owner | ascii_downcase) | unique | length) == length
            then . else error("duplicate confirmation owner") end
        ' \
        <<<"$_normalize_safe_confirmations_result"
}

function _pack_safe_confirmations {
    declare -r -i _pack_safe_confirmations_required="$1"
    shift
    declare -r _pack_safe_confirmations_normalized="$1"
    shift

    declare _pack_safe_confirmations_selected
    _pack_safe_confirmations_selected="$(
        jq -Mce --argjson required "$_pack_safe_confirmations_required" \
            '
            if length >= $required then .[0:$required]
                else error("not enough confirmations") end
            ' \
            <<<"$_pack_safe_confirmations_normalized"
    )"
    declare -r _pack_safe_confirmations_selected

    declare _pack_safe_confirmations_static=0x
    declare _pack_safe_confirmations_dynamic=0x
    declare -i _pack_safe_confirmations_dynamic_offset=$((_pack_safe_confirmations_required * 65))
    declare _pack_safe_confirmations_owner
    declare _pack_safe_confirmations_signature
    declare _pack_safe_confirmations_body
    declare _pack_safe_confirmations_v
    declare -i _pack_safe_confirmations_contract_length
    declare _pack_safe_confirmations_contract_signature
    while IFS=$'\t' read -r _pack_safe_confirmations_owner _pack_safe_confirmations_signature _pack_safe_confirmations_contract_signature ; do
        _pack_safe_confirmations_body="${_pack_safe_confirmations_signature:2}"
        _pack_safe_confirmations_v="${_pack_safe_confirmations_body:128:2}"

        if [[ $_pack_safe_confirmations_v = 00 ]] ; then
            _pack_safe_confirmations_contract_length=$(( (${#_pack_safe_confirmations_contract_signature} - 2) / 2 ))

            _pack_safe_confirmations_static="$(
                cast concat-hex \
                    "$_pack_safe_confirmations_static" \
                    "0x${_pack_safe_confirmations_body:0:64}" \
                    "$(cast to-uint256 $_pack_safe_confirmations_dynamic_offset)" \
                    0x00
            )"
            _pack_safe_confirmations_dynamic="$(
                cast concat-hex \
                    "$_pack_safe_confirmations_dynamic" \
                    "$(cast to-uint256 $_pack_safe_confirmations_contract_length)" \
                    "$_pack_safe_confirmations_contract_signature"
            )"
            _pack_safe_confirmations_dynamic_offset=$((
                _pack_safe_confirmations_dynamic_offset + 32 + _pack_safe_confirmations_contract_length
            ))
        else
            _pack_safe_confirmations_static="$(
                cast concat-hex "$_pack_safe_confirmations_static" "0x${_pack_safe_confirmations_body:0:130}"
            )"
        fi
    done < <(jq -Mr '.[] | [.owner, .signature, .contractSignature] | @tsv' <<<"$_pack_safe_confirmations_selected")

    cast concat-hex "$_pack_safe_confirmations_static" "$_pack_safe_confirmations_dynamic"
}

function _safe_confirmation_caller {
    if [[ ${SAFE_GUARD_OVERRIDE:-${safe_guard:-null}} != [nN][uU][lL][lL] ]] ; then
        cast to-checksum "$safe_guard"
    elif [[ ${safe_signature_executor:-null} != [nN][uU][lL][lL] ]] ; then
        cast to-checksum "$safe_signature_executor"
    elif [[ ${signer:-null} != [nN][uU][lL][lL] ]] ; then
        cast to-checksum "$signer"
    else
        cast address-zero
    fi
}

function _validate_single_safe_confirmation {
    declare -r _validate_single_safe_confirmation_signing_hash="$1"
    shift
    declare -r _validate_single_safe_confirmation_transaction_data="$1"
    shift
    declare -r _validate_single_safe_confirmation_owner="$1"
    shift
    declare -r _validate_single_safe_confirmation_signature="$1"
    shift

    declare _validate_single_safe_confirmation_json
    _validate_single_safe_confirmation_json="$(
        jq -Mnc \
            --arg owner "$_validate_single_safe_confirmation_owner" \
            --arg signature "$_validate_single_safe_confirmation_signature" \
            '[{owner: $owner, signature: $signature}]'
    )"
    declare -r _validate_single_safe_confirmation_json
    declare _validate_single_safe_confirmation_normalized
    _validate_single_safe_confirmation_normalized="$(
        _normalize_safe_confirmations \
            "$_validate_single_safe_confirmation_signing_hash" \
            "$_validate_single_safe_confirmation_json"
    )"
    declare -r _validate_single_safe_confirmation_normalized
    declare _validate_single_safe_confirmation_packed
    _validate_single_safe_confirmation_packed="$(
        _pack_safe_confirmations 1 "$_validate_single_safe_confirmation_normalized"
    )"
    declare -r _validate_single_safe_confirmation_packed

    cast call --from "$(_safe_confirmation_caller)" \
        --rpc-url "$rpc_url" "$safe_address" \
        'checkNSignatures(bytes32,bytes,bytes,uint256)' \
        "$_validate_single_safe_confirmation_signing_hash" \
        "$_validate_single_safe_confirmation_transaction_data" \
        "$_validate_single_safe_confirmation_packed" \
        1 >/dev/null

    echo "$_validate_single_safe_confirmation_normalized"
}

function filter_sts_safe_transactions_with_threshold {
    declare -r _filter_sts_safe_transactions_with_threshold_json="$1"
    shift

    declare -i _filter_sts_safe_transactions_with_threshold_threshold
    _filter_sts_safe_transactions_with_threshold_threshold="$(
        cast call --rpc-url "$rpc_url" "$safe_address" 'getThreshold()(uint256)'
    )"
    declare -r -i _filter_sts_safe_transactions_with_threshold_threshold

    declare _filter_sts_safe_transactions_with_threshold_result='[]'
    declare _filter_sts_safe_transactions_with_threshold_transaction
    declare _filter_sts_safe_transactions_with_threshold_hash
    declare _filter_sts_safe_transactions_with_threshold_confirmations
    declare _filter_sts_safe_transactions_with_threshold_normalized
    declare -i _filter_sts_safe_transactions_with_threshold_count
    while IFS= read -r _filter_sts_safe_transactions_with_threshold_transaction ; do
        if ! jq -Me \
            '
            (.safeTxHash | type == "string" and test("^0[xX][0-9a-fA-F]{64}$"))
            and (.confirmations | type == "array")
            ' \
            <<<"$_filter_sts_safe_transactions_with_threshold_transaction" >/dev/null
        then
            continue
        fi
        _filter_sts_safe_transactions_with_threshold_hash="$(
            jq -Mr '.safeTxHash | ascii_downcase' \
                <<<"$_filter_sts_safe_transactions_with_threshold_transaction"
        )"
        _filter_sts_safe_transactions_with_threshold_confirmations="$(
            jq -Mc .confirmations <<<"$_filter_sts_safe_transactions_with_threshold_transaction"
        )"
        if ! _filter_sts_safe_transactions_with_threshold_normalized="$(
            _normalize_safe_confirmations \
                "$_filter_sts_safe_transactions_with_threshold_hash" \
                "$_filter_sts_safe_transactions_with_threshold_confirmations"
        )" 2>/dev/null
        then
            continue
        fi
        _filter_sts_safe_transactions_with_threshold_count="$(
            jq -Mr length <<<"$_filter_sts_safe_transactions_with_threshold_normalized"
        )"
        if (( _filter_sts_safe_transactions_with_threshold_count < _filter_sts_safe_transactions_with_threshold_threshold )) ; then
            continue
        fi

        _filter_sts_safe_transactions_with_threshold_result="$(
            jq -Mc \
                --argjson transaction "$_filter_sts_safe_transactions_with_threshold_transaction" \
                '. + [$transaction]' \
                <<<"$_filter_sts_safe_transactions_with_threshold_result"
        )"
    done < <(jq -Mc '.[]' <<<"$_filter_sts_safe_transactions_with_threshold_json")

    echo "$_filter_sts_safe_transactions_with_threshold_result"
}

function filter_sts_safe_transactions_by_timelock {
    declare -r _filter_sts_safe_transactions_by_timelock_state="$1"
    shift
    declare -r _filter_sts_safe_transactions_by_timelock_json="$1"
    shift

    if [[ $_filter_sts_safe_transactions_by_timelock_state != unqueued \
        && $_filter_sts_safe_transactions_by_timelock_state != executable ]]
    then
        die 'Unrecognized timelock transaction state'
    fi
    if [[ ${SAFE_GUARD_OVERRIDE:-${safe_guard:-null}} = [nN][uU][lL][lL] ]] ; then
        if [[ $_filter_sts_safe_transactions_by_timelock_state = executable ]] ; then
            echo "$_filter_sts_safe_transactions_by_timelock_json"
            return 0
        fi
        die 'The upgrade Safe does not have an installed Guard'
    fi

    declare _filter_sts_safe_transactions_by_timelock_timestamp=0
    if [[ $_filter_sts_safe_transactions_by_timelock_state = executable ]] ; then
        _filter_sts_safe_transactions_by_timelock_timestamp="$(
            cast block latest --rpc-url "$rpc_url" --field timestamp
        )"
        _filter_sts_safe_transactions_by_timelock_timestamp="$(
            _normalize_safe_uint "$_filter_sts_safe_transactions_by_timelock_timestamp"
        )"
    fi

    declare _filter_sts_safe_transactions_by_timelock_result='[]'
    declare _filter_sts_safe_transactions_by_timelock_transaction
    declare _filter_sts_safe_transactions_by_timelock_hash
    declare _filter_sts_safe_transactions_by_timelock_info_output
    declare _filter_sts_safe_transactions_by_timelock_end
    while IFS= read -r _filter_sts_safe_transactions_by_timelock_transaction ; do
        _filter_sts_safe_transactions_by_timelock_hash="$(
            jq -Mr '.safeTxHash | ascii_downcase' \
                <<<"$_filter_sts_safe_transactions_by_timelock_transaction"
        )"
        _filter_sts_safe_transactions_by_timelock_info_output="$(
            cast call --json --rpc-url "$rpc_url" "$safe_guard" \
                'txInfo(bytes32)(uint256,address)' \
                "$_filter_sts_safe_transactions_by_timelock_hash"
        )"
        if ! jq -Me \
            '
            type == "array"
            and length == 2
            and (.[0] | type == "number" or type == "string")
            and (.[1] | type == "string" and test("^0[xX][0-9a-fA-F]{40}$"))
            ' \
            <<<"$_filter_sts_safe_transactions_by_timelock_info_output" >/dev/null
        then
            die
        fi
        _filter_sts_safe_transactions_by_timelock_end="$(
            _normalize_safe_uint "$(
                jq -Mr '.[0] | tostring' <<<"$_filter_sts_safe_transactions_by_timelock_info_output"
            )"
        )"
        if [[ $_filter_sts_safe_transactions_by_timelock_state = unqueued ]] ; then
            if [[ $_filter_sts_safe_transactions_by_timelock_end != 0 ]] ; then
                continue
            fi
        elif [[ $_filter_sts_safe_transactions_by_timelock_end = 0 ]] \
            || [[ $(
                jq -Mrn \
                    --arg timestamp "$_filter_sts_safe_transactions_by_timelock_timestamp" \
                    --arg timelockEnd "$_filter_sts_safe_transactions_by_timelock_end" \
                    '($timestamp | tonumber) > ($timelockEnd | tonumber)'
            ) != true ]]
        then
            continue
        fi

        _filter_sts_safe_transactions_by_timelock_result="$(
            jq -Mc \
                --argjson transaction "$_filter_sts_safe_transactions_by_timelock_transaction" \
                '. + [$transaction]' \
                <<<"$_filter_sts_safe_transactions_by_timelock_result"
        )"
    done < <(jq -Mc '.[]' <<<"$_filter_sts_safe_transactions_by_timelock_json")

    echo "$_filter_sts_safe_transactions_by_timelock_result"
}

function load_executable_sts_safe_transactions {
    declare _load_executable_sts_safe_transactions_pending
    _load_executable_sts_safe_transactions_pending="$(load_pending_sts_safe_transactions)"
    declare -r _load_executable_sts_safe_transactions_pending

    declare _load_executable_sts_safe_transactions_ready
    _load_executable_sts_safe_transactions_ready="$(
        filter_sts_safe_transactions_with_threshold \
            "$_load_executable_sts_safe_transactions_pending"
    )"
    declare -r _load_executable_sts_safe_transactions_ready

    filter_sts_safe_transactions_by_timelock \
        executable "$_load_executable_sts_safe_transactions_ready"
}

function select_sts_safe_transaction {
    declare -r _select_sts_safe_transaction_json="$1"
    shift
    declare -r _select_sts_safe_transaction_selector="${1,,}"
    shift

    if [[ ! $_select_sts_safe_transaction_selector =~ ^0x[0-9a-f]{8}$ ]] ; then
        die 'Malformed Safe transaction selector: '"$_select_sts_safe_transaction_selector"
    fi

    declare _select_sts_safe_transaction_matches='[]'
    declare _select_sts_safe_transaction_candidate
    declare _select_sts_safe_transaction_hash
    while IFS= read -r _select_sts_safe_transaction_candidate ; do
        _select_sts_safe_transaction_hash="$(
            jq -Mr \
                '.safeTxHash | ascii_downcase' \
                <<<"$_select_sts_safe_transaction_candidate"
        )"
        if ! _select_sts_safe_transaction_candidate="$(
            _load_sts_safe_transaction "$_select_sts_safe_transaction_hash"
        )" 2>/dev/null ; then
            continue
        fi
        if [[ $(jq -Mr '.data[0:10]' <<<"$_select_sts_safe_transaction_candidate") \
            != "$_select_sts_safe_transaction_selector" ]]
        then
            continue
        fi

        _select_sts_safe_transaction_matches="$(
            jq -Mc \
                --argjson transaction "$_select_sts_safe_transaction_candidate" \
                '. + [$transaction]' \
                <<<"$_select_sts_safe_transaction_matches"
        )"
    done < <(jq -Mc '.[]' <<<"$_select_sts_safe_transaction_json")

    declare _select_sts_safe_transaction_selected_hash
    _select_sts_safe_transaction_selected_hash="$(
        select_sts_safe_transaction_hash "$_select_sts_safe_transaction_matches"
    )"
    declare -r _select_sts_safe_transaction_selected_hash
    jq -Mce \
        --arg hash "$_select_sts_safe_transaction_selected_hash" \
        'first(.[] | select(.safeTxHash == $hash))' \
        <<<"$_select_sts_safe_transaction_matches"
}

function select_sts_safe_transaction_hash {
    declare -r _select_sts_safe_transaction_hash_json="$1"
    shift

    declare -a _select_sts_safe_transaction_hash_hashes
    mapfile -t _select_sts_safe_transaction_hash_hashes < <(
        jq -Mr '.[] | .safeTxHash | ascii_downcase' <<<"$_select_sts_safe_transaction_hash_json"
    )
    declare -r -a _select_sts_safe_transaction_hash_hashes
    if (( ${#_select_sts_safe_transaction_hash_hashes[@]} == 0 )) ; then
        die 'No pending Safe transactions match this operation and have enough valid confirmations'
    fi

    declare -a _select_sts_safe_transaction_hash_labels
    mapfile -t _select_sts_safe_transaction_hash_labels < <(
        jq -Mr \
            '
            .[]
            | ([.. | objects | .method? | select(type == "string")] | unique | join(", ") | @json) as $methods
            | (if (.data | type) == "string" then .data[0:10] else null end | tojson) as $selector
            | "nonce \(.nonce | tojson) | \(.safeTxHash) | to \(.to | tojson) | selector \($selector) | confirmations \(.confirmations | length) | \($methods)"
            ' \
            <<<"$_select_sts_safe_transaction_hash_json"
    )
    _select_sts_safe_transaction_hash_labels+=('Cancel')
    declare -r -a _select_sts_safe_transaction_hash_labels

    declare _select_sts_safe_transaction_hash_label
    declare -i _select_sts_safe_transaction_hash_index
    PS3='Which Safe transaction? '
    select _select_sts_safe_transaction_hash_label in "${_select_sts_safe_transaction_hash_labels[@]}" ; do
        if [[ -z ${_select_sts_safe_transaction_hash_label:-} ]] ; then
            echo 'Invalid selection' >&2
            continue
        fi
        _select_sts_safe_transaction_hash_index=$((10#${REPLY#+} - 1))
        if (( _select_sts_safe_transaction_hash_index == ${#_select_sts_safe_transaction_hash_hashes[@]} )) ; then
            die 'No transaction selected'
        fi
        echo "${_select_sts_safe_transaction_hash_hashes[$_select_sts_safe_transaction_hash_index]}"
        return 0
    done
    die
}

function validate_sts_safe_transaction {
    declare -r _validate_sts_safe_transaction_json="$1"
    shift
    declare -r _validate_sts_safe_transaction_signature="$1"
    shift
    declare -r -i _validate_sts_safe_transaction_operation="$1"
    shift
    declare -r _validate_sts_safe_transaction_expected_calldata="$1"
    shift

    if (( _validate_sts_safe_transaction_operation != 0 \
        && _validate_sts_safe_transaction_operation != 1 ))
    then
        die 'Unsupported Safe transaction operation: '"$_validate_sts_safe_transaction_operation"
    fi

    declare _validate_sts_safe_transaction_calldata
    _validate_sts_safe_transaction_calldata="$(
        jq -Mr .data <<<"$_validate_sts_safe_transaction_json"
    )"
    declare -r _validate_sts_safe_transaction_calldata

    declare _validate_sts_safe_transaction_selector
    _validate_sts_safe_transaction_selector="$(
        cast sig "$_validate_sts_safe_transaction_signature"
    )"
    declare -r _validate_sts_safe_transaction_selector
    _require_same_safe_bytes \
        selector \
        "${_validate_sts_safe_transaction_calldata:0:10}" \
        "$_validate_sts_safe_transaction_selector"

    if ! cast decode-calldata \
        "$_validate_sts_safe_transaction_signature" \
        "$_validate_sts_safe_transaction_calldata" \
        >/dev/null
    then
        die 'Malformed calldata for signature: '"$_validate_sts_safe_transaction_signature"
    fi

    _require_expected_sts_safe_transaction \
        "$_validate_sts_safe_transaction_json" \
        "$(target $_validate_sts_safe_transaction_operation)" 0 \
        "$_validate_sts_safe_transaction_expected_calldata" \
        $_validate_sts_safe_transaction_operation \
        0 0 0 "$(cast address-zero)" "$(cast address-zero)" "$(nonce)"
}

function extract_authorize_deadline {
    declare -r _extract_authorize_deadline_data="${1,,}"
    shift
    declare -r _extract_authorize_deadline_feature="$1"
    shift
    declare -r _extract_authorize_deadline_authority="$1"
    shift

    if [[ ! $_extract_authorize_deadline_data =~ ^0x[0-9a-f]{200}$ ]] ; then
        die
    fi
    declare _extract_authorize_deadline_deadline
    _extract_authorize_deadline_deadline="$(
        cast to-dec "0x${_extract_authorize_deadline_data:138:64}"
    )"
    declare -r _extract_authorize_deadline_deadline

    declare _extract_authorize_deadline_expected
    _extract_authorize_deadline_expected="$(
        cast calldata 'authorize(uint128,address,uint40)(bool)' \
            "$_extract_authorize_deadline_feature" \
            "$_extract_authorize_deadline_authority" \
            "$_extract_authorize_deadline_deadline"
    )"
    declare -r _extract_authorize_deadline_expected
    _require_same_safe_bytes \
        data "$_extract_authorize_deadline_data" "$_extract_authorize_deadline_expected" \
        2>/dev/null

    echo "$_extract_authorize_deadline_deadline"
}

function extract_last_multisend_call_data {
    declare -r _extract_last_multisend_call_data_calldata="$1"
    shift

    declare _extract_last_multisend_call_data_calls
    _extract_last_multisend_call_data_calls="$(
        cast decode-calldata "$multisend_sig" "$_extract_last_multisend_call_data_calldata"
    )"
    _extract_last_multisend_call_data_calls="${_extract_last_multisend_call_data_calls:2}"

    declare _extract_last_multisend_call_data_length
    declare -i _extract_last_multisend_call_data_record_length
    declare _extract_last_multisend_call_data_result
    while (( ${#_extract_last_multisend_call_data_calls} > 0 )) ; do
        if (( ${#_extract_last_multisend_call_data_calls} < 170 )) ; then
            die
        fi
        _extract_last_multisend_call_data_length="$(
            cast to-dec "0x${_extract_last_multisend_call_data_calls:106:64}"
        )"
        if [[ ! $_extract_last_multisend_call_data_length =~ ^[0-9]{1,9}$ ]] ; then
            die
        fi
        _extract_last_multisend_call_data_record_length=$((
            170 + _extract_last_multisend_call_data_length * 2
        ))
        if (( _extract_last_multisend_call_data_record_length > ${#_extract_last_multisend_call_data_calls} )) ; then
            die
        fi
        _extract_last_multisend_call_data_result="0x${_extract_last_multisend_call_data_calls:170:$((_extract_last_multisend_call_data_length * 2))}"
        _extract_last_multisend_call_data_calls="${_extract_last_multisend_call_data_calls:$_extract_last_multisend_call_data_record_length}"
    done
    if [[ -z ${_extract_last_multisend_call_data_result:-} ]] ; then
        die
    fi
    echo "$_extract_last_multisend_call_data_result"
}

function _validate_safe_confirmations {
    declare -r _validate_safe_confirmations_signing_hash="$1"
    shift
    declare -r _validate_safe_confirmations_transaction_data="$1"
    shift
    declare -r _validate_safe_confirmations_packed="$1"
    shift

    declare _validate_safe_confirmations_computed_hash
    _validate_safe_confirmations_computed_hash="$(cast keccak "$_validate_safe_confirmations_transaction_data")"
    declare -r _validate_safe_confirmations_computed_hash
    _require_same_safe_bytes \
        safeTxHash \
        "$_validate_safe_confirmations_computed_hash" \
        "$_validate_safe_confirmations_signing_hash"

    declare _validate_safe_confirmations_caller
    _validate_safe_confirmations_caller="$(_safe_confirmation_caller)"
    declare -r _validate_safe_confirmations_caller

    cast call --from "$_validate_safe_confirmations_caller" \
        --rpc-url "$rpc_url" "$safe_address" 'checkSignatures(bytes32,bytes,bytes)' \
        "$_validate_safe_confirmations_signing_hash" \
        "$_validate_safe_confirmations_transaction_data" \
        "$_validate_safe_confirmations_packed" >/dev/null
}

function pack_sts_signatures {
    declare -r _pack_sts_signatures_signing_hash="$1"
    shift
    declare -r _pack_sts_signatures_transaction_data="$1"
    shift
    declare -r _pack_sts_signatures_confirmations="$1"
    shift

    declare -i _pack_sts_signatures_threshold
    _pack_sts_signatures_threshold="$(cast call --rpc-url "$rpc_url" "$safe_address" 'getThreshold()(uint256)')"
    declare -r -i _pack_sts_signatures_threshold

    declare _pack_sts_signatures_normalized
    _pack_sts_signatures_normalized="$(
        _normalize_safe_confirmations \
            "$_pack_sts_signatures_signing_hash" \
            "$_pack_sts_signatures_confirmations"
    )"
    declare -r _pack_sts_signatures_normalized

    declare _pack_sts_signatures_result
    _pack_sts_signatures_result="$(
        _pack_safe_confirmations "$_pack_sts_signatures_threshold" "$_pack_sts_signatures_normalized"
    )"
    declare -r _pack_sts_signatures_result
    _validate_safe_confirmations \
        "$_pack_sts_signatures_signing_hash" \
        "$_pack_sts_signatures_transaction_data" \
        "$_pack_sts_signatures_result"

    echo "$_pack_sts_signatures_result"
}

function pack_sts_transaction_signatures {
    declare -r _pack_sts_transaction_signatures_json="$1"
    shift

    declare -a _pack_sts_transaction_signatures_fields
    mapfile -t _pack_sts_transaction_signatures_fields < <(
        jq -Mr \
            '.to, .value, .data, .operation, .safeTxGas, .baseGas, .gasPrice, .gasToken, .refundReceiver, .nonce' \
            <<<"$_pack_sts_transaction_signatures_json"
    )
    declare -r -a _pack_sts_transaction_signatures_fields

    declare _pack_sts_transaction_signatures_data
    _pack_sts_transaction_signatures_data="$(
        _safe_transaction_data "${_pack_sts_transaction_signatures_fields[@]}"
    )"
    declare -r _pack_sts_transaction_signatures_data

    declare _pack_sts_transaction_signatures_hash
    _pack_sts_transaction_signatures_hash="$(
        jq -Mr .safeTxHash <<<"$_pack_sts_transaction_signatures_json"
    )"
    declare -r _pack_sts_transaction_signatures_hash
    declare _pack_sts_transaction_signatures_confirmations
    _pack_sts_transaction_signatures_confirmations="$(
        jq -Mc .confirmations <<<"$_pack_sts_transaction_signatures_json"
    )"
    declare -r _pack_sts_transaction_signatures_confirmations

    pack_sts_signatures \
        "$_pack_sts_transaction_signatures_hash" \
        "$_pack_sts_transaction_signatures_data" \
        "$_pack_sts_transaction_signatures_confirmations"
}

function retrieve_signatures {
    declare -r _retrieve_signatures_prefix="$1"
    shift

    declare -r _retrieve_signatures_call="$1"
    shift

    declare -i _retrieve_signatures_operation
    if (( $# > 0 )) ; then
        _retrieve_signatures_operation="$1"
        shift
    else
        _retrieve_signatures_operation=0
    fi
    declare -r -i _retrieve_signatures_operation

    declare _retrieve_signatures_to
    if (( $# > 0 )) ; then
        _retrieve_signatures_to="$1"
        shift
    else
        _retrieve_signatures_to="$(target $_retrieve_signatures_operation)"
    fi
    declare -r _retrieve_signatures_to

    declare _retrieve_signatures_signing_hash
    _retrieve_signatures_signing_hash="$(
        eip712_hash "$_retrieve_signatures_call" $_retrieve_signatures_operation "$_retrieve_signatures_to"
    )"
    declare -r _retrieve_signatures_signing_hash

    declare _retrieve_signatures_transaction_data
    _retrieve_signatures_transaction_data="$(
        _safe_transaction_data \
            "$_retrieve_signatures_to" 0 "$_retrieve_signatures_call" $_retrieve_signatures_operation \
            0 0 0 "$(cast address-zero)" "$(cast address-zero)" "$(nonce)"
    )"
    declare -r _retrieve_signatures_transaction_data
    _require_same_safe_bytes \
        safeTxHash \
        "$(cast keccak "$_retrieve_signatures_transaction_data")" \
        "$_retrieve_signatures_signing_hash"

    declare _retrieve_signatures_confirmations
    if ! sts_safe_transactions_enabled ; then
        _retrieve_signatures_confirmations='[]'
        declare -a _retrieve_signatures_files
        mapfile -t _retrieve_signatures_files < <(
            compgen -G "$project_root/$_retrieve_signatures_prefix"_"$chain_display_name"_"$(git rev-parse --short=8 HEAD)"_'*'_"$(nonce)".txt || true
        )
        declare -r -a _retrieve_signatures_files

        declare _retrieve_signatures_file
        declare _retrieve_signatures_confirmation
        declare _retrieve_signatures_confirmation_json
        declare _retrieve_signatures_signer
        for _retrieve_signatures_file in "${_retrieve_signatures_files[@]}" ; do
            _retrieve_signatures_signer="${_retrieve_signatures_file%%_$(nonce).txt}"
            _retrieve_signatures_signer="${_retrieve_signatures_signer##*_}"
            _retrieve_signatures_signer="$(cast to-checksum "$_retrieve_signatures_signer")"
            _retrieve_signatures_confirmation="$(<"$_retrieve_signatures_file")"
            if _is_current_safe_owner "$_retrieve_signatures_signer" ; then
                if ! _retrieve_signatures_confirmation_json="$(
                    _validate_single_safe_confirmation \
                        "$_retrieve_signatures_signing_hash" \
                        "$_retrieve_signatures_transaction_data" \
                        "$_retrieve_signatures_signer" \
                        "$_retrieve_signatures_confirmation"
                )"
                then
                    echo 'Ignoring invalid Safe confirmation file: '"$_retrieve_signatures_file" >&2
                    continue
                fi
                _retrieve_signatures_confirmations="$(
                    jq -Mc \
                        --argjson confirmation "$_retrieve_signatures_confirmation_json" \
                        '. + $confirmation' \
                        <<<"$_retrieve_signatures_confirmations"
                )"
            fi
        done
    else
        declare _retrieve_signatures_transaction
        _retrieve_signatures_transaction="$(_load_sts_safe_transaction "$_retrieve_signatures_signing_hash")"
        declare -r _retrieve_signatures_transaction
        _require_expected_sts_safe_transaction \
            "$_retrieve_signatures_transaction" \
            "$_retrieve_signatures_to" 0 "$_retrieve_signatures_call" $_retrieve_signatures_operation \
            0 0 0 "$(cast address-zero)" "$(cast address-zero)" "$(nonce)"
        _retrieve_signatures_confirmations="$(jq -Mc .confirmations <<<"$_retrieve_signatures_transaction")"
    fi
    declare -r _retrieve_signatures_confirmations

    pack_sts_signatures \
        "$_retrieve_signatures_signing_hash" \
        "$_retrieve_signatures_transaction_data" \
        "$_retrieve_signatures_confirmations"
}
