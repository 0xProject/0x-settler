forge build

if [ ! -f "$project_root"/out/Settler.sol/Settler.json ] ; then
    echo 'Cannot find Settler.json' >&2
    exit 1
fi

declare constructor_args
constructor_args="$(cast abi-encode 'constructor(address)' "$(get_config uniV3.factory)")"
declare -r constructor_args

declare initcode
initcode="$(cast concat-hex "$(jq -Mr .bytecode.object < out/Settler.sol/Settler.json)" "$constructor_args")"
declare -r initcode

declare -r deploy_sig='deploy(uint128,bytes)(address,uint32)'
declare deploy_calldata
deploy_calldata="$(cast calldata "$deploy_sig" $feature "$initcode")"
declare -r deploy_calldata
