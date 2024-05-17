if ! hash forge &>/dev/null ; then
    echo 'foundry is not installed' >&2
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

if [[ $(ls -l api_secrets.json | cut -d' ' -f1) != '-rw-------' ]] ; then
    echo 'api_secrets.json permissions too lax' >&2
    echo 'run: chmod 600 api_secrets.json' >&2
    exit 1
fi

declare -r chain_name="$1"
shift

if [[ $(jq -r -M ."$chain_name" < api_secrets.json) == 'null' ]] ; then
    echo "$chain_name"' is missing from api_secrets.json' >&2
    exit 1
fi

function get_api_secret {
    jq -r -M ."$chain_name"."$1" < "$project_root"/api_secrets.json
}

function get_config {
    jq -r -M ."$chain_name"."$1" < "$project_root"/chain_config.json
}

if [[ $(get_config isCancun) != [Tt]rue ]] ; then
    echo 'You are on the wrong branch' >&2
    exit 1
fi
