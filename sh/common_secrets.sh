if ! hash sha256sum &>/dev/null ; then
    echo 'sha256sum is not installed' >&2
    exit 1
fi

if [ ! -f "$project_root"/secrets.json ] ; then
    echo 'secrets.json is missing' >&2
    exit 1
fi

declare secrets_permissions
secrets_permissions="$(ls -l "$project_root"/secrets.json)"
secrets_permissions="${secrets_permissions::10}"
declare -r secrets_permissions
if [[ $secrets_permissions != '-rw-------' ]] ; then
    echo 'secrets.json permissions too lax' >&2
    echo 'run: chmod 600 secrets.json' >&2
    exit 1
fi

if ! sha256sum -c <<<'aecc29dbca963a4397effa7e019a754aa2108c0b80f8cd67db7ee8e2b3c76c2b  secrets.json' >/dev/null ; then
    echo 'Secrets are wrong' >&2
    exit 1
fi

function get_secret {
    jq -Mr ."$1"."$2" < "$project_root"/secrets.json
}
