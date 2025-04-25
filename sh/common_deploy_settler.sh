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

declare flat_intent_source
flat_intent_source="$project_root"/src/flat/"$chain_display_name"IntentFlat.sol
declare -r flat_intent_source
trap 'trap - EXIT; set +e; rm -f '"$(_escape "$flat_taker_source")"' '"$(_escape "$flat_metatx_source")"' '"$(_escape "$flat_intent_source")" EXIT
forge flatten -o "$flat_intent_source" src/chains/"$chain_display_name"/Intent.sol >/dev/null
forge build "$flat_intent_source"

declare taker_artifact
taker_artifact="$project_root"/out/"$chain_display_name"TakerSubmittedFlat.sol/"$chain_display_name"Settler.json
declare -r taker_artifact

declare metatx_artifact
metatx_artifact="$project_root"/out/"$chain_display_name"MetaTxnFlat.sol/"$chain_display_name"SettlerMetaTxn.json
declare -r metatx_artifact

declare intent_artifact
intent_artifact="$project_root"/out/"$chain_display_name"IntentFlat.sol/"$chain_display_name"SettlerIntent.json
declare -r intent_artifact

if [ ! -f "$taker_artifact" ] || [ ! -f "$metatx_artifact" ] || [ ! -f "$intent_artifact" ] ; then
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

declare intent_initcode
intent_initcode="$(cast concat-hex "$(jq -Mr .bytecode.object < "$intent_artifact")" "$constructor_args")"
declare -r intent_initcode

declare -r deploy_sig='deploy(uint128,bytes)(address,uint32)'

declare deploy_taker_calldata
deploy_taker_calldata="$(cast calldata "$deploy_sig" 2 "$taker_initcode")"
declare -r deploy_taker_calldata

declare deploy_metatx_calldata
deploy_metatx_calldata="$(cast calldata "$deploy_sig" 3 "$metatx_initcode")"
declare -r deploy_metatx_calldata

declare deploy_intent_calldata
deploy_intent_calldata="$(cast calldata "$deploy_sig" 4 "$intent_initcode")"
declare -r deploy_intent_calldata

declare next_intent_settler_address
next_intent_settler_address="$(cast call --rpc-url "$rpc_url" "$deployer_address" 'next(uint128)(address)' 4)"
declare -r next_intent_settler_address

declare -a solvers
readarray -t solvers < "$project_root"/sh/solvers.txt
declare -r -a solvers

declare -a setsolver_calldatas
declare setsolver_calldata
declare prev_solver=0x0000000000000000000000000000000000000001
declare solver
for solver in "${solvers[@]}" ; do
    setsolver_calldata="$(cast calldata 'setSolver(address,address,bool)' "$prev_solver" "$solver" true)"
    setsolver_calldatas+=("$setsolver_calldata")
    prev_solver="$solver"
done
unset -v solver
unset -v prev_solver
unset -v setsolver_calldata

if [[ -n "${deployer_address-}" ]] ; then
    declare -a deploy_calldatas
    if (( chainid == 534352 )) ; then
        declare setsolver_calldata
        for setsolver_calldata in "${setsolver_calldatas[@]}" ; do
            deploy_calldatas+=(
                "$(
                    cast concat-hex                                               \
                    0x00                                                          \
                    "$next_intent_settler_address"                                \
                    "$(cast to-uint256 0)"                                        \
                    "$(cast to-uint256 $(( (${#setsolver_calldata} - 2) / 2 )) )" \
                    "$setsolver_calldata"
                )"
            )
        done
        deploy_calldatas=(
            0 "$deploy_taker_calldata" "$deployer_address"
            0 "$deploy_metatx_calldata" "$deployer_address"
            0 "$deploy_intent_calldata" "$deployer_address"
            1 "$(cast calldata "$multisend_sig" "$(cast concat-hex "${deploy_calldatas[@]}")")" "$multicall_address"
        )
    else
        deploy_calldatas+=(
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

            "$(
                cast concat-hex                                                   \
                0x00                                                              \
                "$deployer_address"                                               \
                "$(cast to-uint256 0)"                                            \
                "$(cast to-uint256 $(( (${#deploy_intent_calldata} - 2) / 2 )) )" \
                "$deploy_intent_calldata"
            )"
        )
        for setsolver_calldata in "${setsolver_calldatas[@]}" ; do
            deploy_calldatas+=(
                "$(
                    cast concat-hex                                               \
                    0x00                                                          \
                    "$next_intent_settler_address"                                \
                    "$(cast to-uint256 0)"                                        \
                    "$(cast to-uint256 $(( (${#setsolver_calldata} - 2) / 2 )) )" \
                    "$setsolver_calldata"
                )"
            )
        done
        declare multicall_args
        multicall_args="$(cast concat-hex "${deploy_calldatas[@]}")"
        multicall_args="${multicall_args:2}"

        declare multicall_args_length="${#multicall_args}"

        declare -i padding_length=$((multicall_args_length % 64))
        if (( padding_length )) ; then
            padding_length=$((64 - padding_length))
            multicall_args="$multicall_args""$(seq 1 $padding_length | xargs printf '0%.0s')"
        fi

        multicall_args_length=$(( multicall_args_length / 2 ))
        multicall_args_length="$(cast to-uint256 $multicall_args_length)"
        multicall_args_length="${multicall_args_length:2}"

        multicall_args="$multisend_selector"'0000000000000000000000000000000000000000000000000000000000000020'"$multicall_args_length""$multicall_args"

        deploy_calldatas=(
            1 "$multicall_args" "$multicall_address"
        )
    fi
fi
