forge build

declare chain_display_name
chain_display_name="$(get_config displayName)"
declare -r chain_display_name

declare taker_artifact
taker_artifact="$project_root"/out/"$chain_display_name".sol/"$chain_display_name"Settler.json
declare -r taker_artifact

declare metatx_artifact
metatx_artifact="$project_root"/out/"$chain_display_name".sol/"$chain_display_name"SettlerMetaTxn.json
declare -r metatx_artifact

if [ ! -f "$taker_artifact" ] || [ ! -f "$metatx_artifact" ] ; then
    echo 'Cannot find '"$chain_display_name"'Settler.json' >&2
    exit 1
fi

declare constructor_args
constructor_args="$(cast abi-encode 'constructor()')"
declare -r constructor_args

declare taker_initcode
taker_initcode="$(cast concat-hex "$(jq -Mr .bytecode.object < "$taker_artifact")" "$constructor_args")"
declare -r taker_initcode

declare metatx_initcode
metatx_initcode="$(cast concat-hex "$(jq -Mr .bytecode.object < "$metatx_artifact")" "$constructor_args")"
declare -r taker_initcode

declare -r deploy_sig='deploy(uint128,bytes)(address,uint32)'

declare deploy_taker_calldata
deploy_taker_calldata="$(cast calldata "$deploy_sig" 2 "$taker_initcode")"
declare -r deploy_taker_calldata

declare deploy_metatx_calldata
deploy_metatx_calldata="$(cast calldata "$deploy_sig" 3 "$metatx_initcode")"
declare -r deploy_metatx_calldata

declare -a deploy_calls=(
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

declare deploy_calldata
deploy_calldata="$(cast calldata "$multisend_sig" "$(cast concat-hex "${deploy_calls[@]}")")"
declare -r deploy_calldata
