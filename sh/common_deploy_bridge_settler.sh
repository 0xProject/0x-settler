if [[ "${bridge_settler_skip_clean-no}" != [Yy]es ]] ; then
    forge clean
fi

declare flat_bridge_settler_source
flat_bridge_settler_source="$project_root"/src/flat/"$chain_display_name"BridgeSettlerFlat.sol
declare -r flat_bridge_settler_source

if [[ "${bridge_settler_skip_clean-no}" == [Yy]es ]] ; then
    declare swap_settler_trap
    swap_settler_trap="$(trap -p EXIT)"

    if [[ $swap_settler_trap != "trap -- 'trap - EXIT; set +e; "* ]] || [[ $swap_settler_trap != *"' EXIT" ]] ; then
        echo '`trap EXIT` cleanup malformed; cannot add a new cleanup' >&2
        exit 1
    fi
    swap_settler_trap="${swap_settler_trap%\' EXIT}"
    swap_settler_trap="${swap_settler_trap#trap -- \'trap - EXIT; set +e; }"
    trap 'trap - EXIT; set +e; '"$swap_settler_trap"'; rm -f '"$(_escape "$flat_bridge_settler_source")" EXIT

    unset -v swap_settler_trap
else
    trap 'trap - EXIT; set +e; rm -f '"$(_escape "$flat_bridge_settler_source")" EXIT
fi

forge flatten -o "$flat_bridge_settler_source" src/chains/"$chain_display_name"/BridgeSettler.sol >/dev/null
FOUNDRY_SOLC_VERSION=0.8.34 forge build "$flat_bridge_settler_source"

declare bridge_settler_artifact
bridge_settler_artifact="$project_root"/out/"$chain_display_name"BridgeSettlerFlat.sol/"$chain_display_name"BridgeSettler.json
declare -r bridge_settler_artifact

if [ ! -f "$bridge_settler_artifact" ] ; then
    echo 'Cannot find '"$chain_display_name"'BridgeSettler.json' >&2
    exit 1
fi

if [[ -z "${constructor_args-}" ]] ; then
    declare constructor_args
    constructor_args="$(cast abi-encode 'constructor(bytes20)' 0x"$(git rev-parse HEAD)")"
    declare -r constructor_args
elif [[ "$constructor_args" != "$(cast abi-encode 'constructor(bytes20)' 0x"$(git rev-parse HEAD)")" ]] ; then
    echo 'Malformed constructor arguments' >&2
    exit 1
fi

declare bridge_settler_initcode
bridge_settler_initcode="$(cast concat-hex "$(jq -Mr .bytecode.object < "$bridge_settler_artifact")" "$constructor_args")"
declare -r bridge_settler_initcode

if [[ -z "${deploy_sig-}" ]] ; then
    declare -r deploy_sig='deploy(uint128,bytes)(address,uint32)'
fi

declare deploy_bridge_settler_calldata
deploy_bridge_settler_calldata="$(cast calldata "$deploy_sig" 5 "$bridge_settler_initcode")"
declare -r deploy_bridge_settler_calldata

if [[ -n "${deployer_address-}" ]] ; then
    declare -a deploy_calldatas
    deploy_calldatas=(
        0 "$deploy_bridge_settler_calldata" "$deployer_address"
    )
fi
