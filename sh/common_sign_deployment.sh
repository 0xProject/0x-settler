function sign_deployment_transaction {
    declare -r _secret_section="$1"
    declare -r _signer="$2"
    declare -r _unsigned_tx="$3"

    declare _prefix
    declare _fields
    if [[ $_unsigned_tx = 0x02* ]] ; then
        _prefix=0x02
        _fields="$(cast from-rlp "0x${_unsigned_tx:4}")"
    elif [[ $_unsigned_tx = 0x[c-f]* ]] ; then
        _prefix=0x
        _fields="$(cast from-rlp "$_unsigned_tx")"
    else
        die 'Unsupported deployment transaction type'
    fi
    declare -r _prefix

    declare _signature
    _signature="$(
        DEPLOYMENT_PRIVATE_KEY="$(get_secret "$_secret_section" key)" FOUNDRY_VERBOSITY=0 \
            forge script --json --use 0.8.25 --evm-version london --optimizer-runs 200 \
            --sig 'run(address,bytes32)' \
            --skip 'src/*' --skip 'test/*' --skip DeploySafes.s.sol \
            -- script/SignDeployment.s.sol "$_signer" "$(cast keccak "$_unsigned_tx")" \
            | jq -ce 'select(.success) | .returns | [.yParity.value, .r.value, .s.value]'
    )"
    declare -r _signature

    declare _v
    _v="$(jq -r '.[0]' <<<"$_signature")"
    if [[ $_prefix = 0x ]] ; then
        declare _chain_id
        _chain_id="$(jq -r '.[6]' <<<"$_fields")"
        _chain_id="$(cast to-dec "0x0${_chain_id#0x}")"
        # Legacy signatures must include the chain ID to prevent replay on another chain.
        _v="$(BC_LINE_LENGTH=0 bc <<<"2 * $_chain_id + 35 + $_v")"
        _fields="$(jq -c '.[0:6]' <<<"$_fields")"
    fi

    # Transaction integers must not contain leading zero bytes.
    _fields="$(
        jq -c --arg v "$(cast to-uint256 "$_v")" --argjson signature "$_signature" \
            '. + ([$v, $signature[1], $signature[2]] | map(sub("^0x(00)*"; "0x")))' <<<"$_fields"
    )"
    declare _signed_tx
    _signed_tx="$(cast to-rlp "$_fields")"
    printf '%s%s\n' "$_prefix" "${_signed_tx#0x}"
}
