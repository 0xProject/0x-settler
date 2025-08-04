forge clean
declare flat_bridge_settler_source
flat_bridge_settler_source="$project_root"/src/flat/"$chain_display_name"BridgeSettlerFlat.sol
declare -r flat_bridge_settler_source
trap 'trap - EXIT; set +e; rm -f '"$(_escape "$flat_bridge_settler_source")" EXIT
forge flatten -o "$flat_bridge_settler_source" src/chains/"$chain_display_name"/BridgeSettler.sol >/dev/null
forge build "$flat_bridge_settler_source"

declare bridge_settler_artifact
bridge_settler_artifact="$project_root"/out/"$chain_display_name"BridgeSettlerFlat.sol/"$chain_display_name"BridgeSettler.json
declare -r bridge_settler_artifact

if [ ! -f "$bridge_settler_artifact" ] ; then
    echo 'Cannot find '"$chain_display_name"'BridgeSettler.json' >&2
    exit 1
fi

declare constructor_args
constructor_args="$(cast abi-encode 'constructor(bytes20)' 0x"$(git rev-parse HEAD)")"
declare -r constructor_args

declare bridge_settler_initcode
bridge_settler_initcode="$(cast concat-hex "$(jq -Mr .bytecode.object < "$bridge_settler_artifact")" "$constructor_args")"
declare -r bridge_settler_initcode

declare -r deploy_sig='deploy(uint128,bytes)(address,uint32)'

declare deploy_bridge_settler_calldata
deploy_bridge_settler_calldata="$(cast calldata "$deploy_sig" 5 "$bridge_settler_initcode")"
declare -r deploy_bridge_settler_calldata

declare -a deploy_calldatas
deploy_calldatas=(
    0 "$deploy_bridge_settler_calldata" "$deployer_address"
)
