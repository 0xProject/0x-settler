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
    _retrieve_signatures_signing_hash="$(eip712_hash "$_retrieve_signatures_call" $_retrieve_signatures_operation "$_retrieve_signatures_to")"
    declare -r _retrieve_signatures_signing_hash

    declare -a _retrieve_signatures_result
    if [[ $safe_url = 'NOT SUPPORTED' ]] || [[ ${FORCE_IGNORE_STS-No} = [Yy]es ]] ; then
        set +f
        declare confirmation
        for confirmation in "$project_root"/"$_retrieve_signatures_prefix"_"$chain_display_name"_"$(git rev-parse --short=8 HEAD)"_*_$(nonce).txt ; do
            signatures+=("$(<"$confirmation")")
            if (( ${#signatures[@]} == 2 )) ; then
                break
            fi
        done
        set -f

        if (( ${#signatures[@]} < 2 )) ; then
            echo 'Bad number of signatures' >&2
            return 1
        fi
    else
        declare signatures_json
        signatures_json="$(curl --fail --retry 5 -s "$safe_url"'/v1/multisig-transactions/'"$_retrieve_signatures_signing_hash"'/confirmations/?executed=false' -X GET)"
        declare -r signatures_json

        if (( $(jq -Mr .count <<<"$signatures_json") < 2 )) ; then
            echo 'Bad number of signatures' >&2
            return 1
        fi

        if [ "$(jq -Mr '.results[1].owner' <<<"$signatures_json" | tr '[:upper:]' '[:lower:]')" \< "$(jq -Mr '.results[0].owner' <<<"$signatures_json" | tr '[:upper:]' '[:lower:]')" ] ; then
            signatures+=( "$(jq -Mr '.results[1].signature' <<<"$signatures_json")" )
            signatures+=( "$(jq -Mr '.results[0].signature' <<<"$signatures_json")" )
        else
            signatures+=( "$(jq -Mr '.results[0].signature' <<<"$signatures_json")" )
            signatures+=( "$(jq -Mr '.results[1].signature' <<<"$signatures_json")" )
        fi
    fi

    cast concat-hex "${signatures[@]}"
}
