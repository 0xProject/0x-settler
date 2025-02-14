forge clean
declare flat_taker_source
flat_taker_source="$project_root"/src/flat/"$chain_display_name"TakerSubmittedFlat.sol
declare -r flat_taker_source
trap 'trap - EXIT; set +e; rm -f '"$(_escape "$flat_taker_source")" EXIT
forge flatten -o "$flat_taker_source" src/chains/"$chain_display_name"/TakerSubmitted.sol >/dev/null
forge build "$flat_taker_source"

declare flat_metatx_source
flat_metatx_source="$project_root"/src/flat/"$chain_display_name"MetaTxnFlat.sol
declare -r flat_metatx_source
trap 'trap - EXIT; set +e; rm -f '"$(_escape "$flat_taker_source")"' '"$(_escape "$flat_metatx_source")" EXIT
forge flatten -o "$flat_metatx_source" src/chains/"$chain_display_name"/MetaTxn.sol >/dev/null
forge build "$flat_metatx_source"

declare taker_artifact
taker_artifact="$project_root"/out/"$chain_display_name"TakerSubmittedFlat.sol/"$chain_display_name"Settler.json
declare -r taker_artifact

declare metatx_artifact
metatx_artifact="$project_root"/out/"$chain_display_name"MetaTxnFlat.sol/"$chain_display_name"SettlerMetaTxn.json
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

if [[ -n "${deployer_address-}" ]] ; then
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
fi
