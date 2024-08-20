declare chain_display_name
chain_display_name="$(get_config displayName)"
declare -r chain_display_name

forge clean
declare flat_source
flat_source="$project_root"/src/flat/"$chain_display_name"Flat.sol
declare -r flat_source
trap 'trap - EXIT; set +e; rm -f '"$(_escape "$flat_source")" EXIT
forge flatten -o "$flat_source" src/chains/"$chain_display_name".sol >/dev/null
forge build "$flat_source"

declare artifact_prefix
artifact_prefix="$project_root"/out/"$chain_display_name"Flat.sol/"$chain_display_name"Settler
declare -r artifact_prefix

declare taker_artifact
taker_artifact="$artifact_prefix".json
declare -r taker_artifact

declare metatx_artifact
metatx_artifact="$artifact_prefix"MetaTxn.json
declare -r metatx_artifact

if [ ! -f "$taker_artifact" ] || [ ! -f "$metatx_artifact" ] ; then
    echo 'Cannot find '"$chain_display_name"'Settler.json' >&2
    exit 1
fi

declare constructor_args
constructor_args="$(cast abi-encode 'constructor(bytes20)' 0x"$(git rev-parse HEAD)")"
declare -r constructor_args

declare taker_initcode
taker_initcode="$(cast concat-hex "$(jq -Mr .bytecode.object < "$taker_artifact")" "$constructor_args")"
declare -r taker_initcode

declare metatx_initcode
metatx_initcode="$(cast concat-hex "$(jq -Mr .bytecode.object < "$metatx_artifact")" "$constructor_args")"
declare -r metatx_initcode

declare -r deploy_sig='deploy(uint128,bytes)(address,uint32)'

declare deploy_taker_calldata
deploy_taker_calldata="$(cast calldata "$deploy_sig" 2 "$taker_initcode")"
declare -r deploy_taker_calldata

declare deploy_metatx_calldata
deploy_metatx_calldata="$(cast calldata "$deploy_sig" 3 "$metatx_initcode")"
declare -r deploy_metatx_calldata

declare -a deploy_calldatas
if (( chainid == 534352 )) ; then
    deploy_calldatas=(
        0 "$deploy_taker_calldata"
        0 "$deploy_metatx_calldata"
    )
else
    deploy_calldatas=(
        "$(
            cast concat-hex                                                   \
            0x00                                                              \
            "$deployer_address"                                               \
            "$(cast to-uint256 0)"                                            \
            "$(cast to-uint256 $(( (${#deploy_taker_calldata} - 2) / 2 )) )"  \
            "$deploy_taker_calldata"
        )"

        "$(
            cast concat-hex                                                   \
            0x00                                                              \
            "$deployer_address"                                               \
            "$(cast to-uint256 0)"                                            \
            "$(cast to-uint256 $(( (${#deploy_metatx_calldata} - 2) / 2 )) )" \
            "$deploy_metatx_calldata"
        )"
    )
    deploy_calldatas=(
        1 "$(cast calldata "$multisend_sig" "$(cast concat-hex "${deploy_calldatas[@]}")")"
    )
fi

declare safe_url
safe_url="$(get_config safe.apiUrl)"
declare -r safe_url
