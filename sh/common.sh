if ! hash forge &>/dev/null ; then
    echo 'foundry is not installed' >&2
    exit 1
fi

declare forge_version
forge_version="$(forge --version)"
forge_version="${forge_version:13:7}"
declare -r forge_version
if [[ $forge_version != '59f354c' ]] ; then
    echo 'Wrong foundry version installed -- '"$forge_version" >&2
    echo 'Run `foundryup -v nightly-59f354c179f4e7f6d7292acb3d068815c79286d1`' >&2
    exit 1
fi

if ! hash curl &>/dev/null ; then
    echo 'curl is not installed' >&2
    exit 1
fi

if ! hash jq &>/dev/null ; then
    echo 'jq is not installed' >&2
    exit 1
fi

if [ ! -f "$project_root"/api_secrets.json ] ; then
    echo 'api_secrets.json is missing' >&2
    exit 1
fi

if [[ $(ls -l "$project_root"/api_secrets.json | cut -d' ' -f1 | cut -d. -f1) != '-rw-------' ]] ; then
    echo 'api_secrets.json permissions too lax' >&2
    echo 'run: chmod 600 api_secrets.json' >&2
    exit 1
fi

declare -r chain_name="$1"
shift

if [[ $(jq -Mr ."$chain_name" < api_secrets.json) == 'null' ]] ; then
    echo "$chain_name"' is missing from api_secrets.json' >&2
    exit 1
fi

function get_api_secret {
    jq -Mr ."$chain_name"."$1" < "$project_root"/api_secrets.json
}

function get_config {
    jq -Mr ."$chain_name"."$1" < "$project_root"/chain_config.json
}

if [[ ${IGNORE_HARDFORK-no} != [Yy]es ]] ; then
    if [[ $(get_config isShanghai) != [Tt]rue ]] ; then
        echo 'Chains without the Shanghai hardfork (PUSH0) are not supported' >&2
        exit 1
    fi

    if [[ $(get_config isCancun) != [Tt]rue ]] ; then
        echo 'You are on the wrong branch' >&2
        exit 1
    fi
fi

declare -i chainid
chainid="$(get_config chainId)"
declare -r -i chainid

declare chain_display_name
chain_display_name="$(get_config displayName)"
declare -r chain_display_name

declare rpc_url
rpc_url="$(get_api_secret rpcUrl)"
declare -r rpc_url

if [[ ${rpc_url:-unset} = 'unset' ]] || [[ $rpc_url == 'null' ]] ; then
    echo '`rpcUrl` is unset in `api_secrets.json` for chain "'"$chain_name"'"' >&2
    exit 1
fi

function verify_contract {
    declare -r _verify_constructor_args="$1"
    shift
    declare -r _verify_deployed_address="$1"
    shift
    declare -r _verify_source_path="$1"
    shift

    if (( chainid == 34443 )) || (( chainid == 57073 )) ; then # Mode and Ink use Blockscout, not Etherscan
        forge verify-contract --watch --chain $chainid --verifier blockscout --verifier-url "$(get_config blockscoutApi)" --constructor-args "$_verify_constructor_args" "$_verify_deployed_address" "$_verify_source_path"
    else
        forge verify-contract --watch --chain $chainid --verifier custom --verifier-api-key "$(get_api_secret etherscanKey)" --verifier-url "$(get_config etherscanApi)" --constructor-args "$_verify_constructor_args" "$_verify_deployed_address" "$_verify_source_path"
    fi
    if (( chainid != 146 )) && (( chainid != 480 )) && (( chainid != 57073 )) && (( chainid != 81457 )) && (( chainid != 167000 )); then # Sourcify doesn't support Sonic, World Chain, Blast, Taiko, or Ink
        forge verify-contract --watch --chain $chainid --verifier sourcify --constructor-args "$_verify_constructor_args" "$_verify_deployed_address" "$_verify_source_path"
    fi
}
