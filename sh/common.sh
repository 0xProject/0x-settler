if ! hash forge &>/dev/null ; then
    echo 'foundry is not installed' >&2
    exit 1
fi

declare forge_version
forge_version="$(forge --version)"
forge_version="${forge_version:13:7}"
declare -r forge_version
if [[ $forge_version != 'fe2acca' ]] ; then
    echo 'Wrong foundry version installed -- '"$forge_version" >&2
    echo 'Run `foundryup -v nightly-fe2acca4e379793539db80e032d76ffe0110298b`' >&2
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

if [[ $(get_config isShanghai) != [Tt]rue ]] ; then
    echo 'Chains without the Shanghai hardfork (PUSH0) are not supported' >&2
    exit 1
fi

if [[ $(get_config isCancun) != [Tt]rue ]] ; then
    echo 'You are on the wrong branch' >&2
    exit 1
fi
