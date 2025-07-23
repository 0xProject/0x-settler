if ! hash sha256sum &>/dev/null ; then
    echo 'sha256sum is not installed' >&2
    exit 1
fi

if ! hash scrypt &>/dev/null ; then
    echo 'scrypt is not installed' >&2
    exit 1
fi

if [ ! -f "$project_root"/secrets.json.scrypt ] ; then
    echo 'secrets.json.scrypt is missing' >&2
    exit 1
fi

declare secrets_permissions
secrets_permissions="$(ls -l "$project_root"/secrets.json.scrypt)"
secrets_permissions="${secrets_permissions::10}"
declare -r secrets_permissions
if [[ $secrets_permissions != '-rw-------' ]] ; then
    echo 'secrets.json.scrypt permissions too lax' >&2
    echo 'run: chmod 600 secrets.json.scrypt' >&2
    exit 1
fi

if [ -f "$project_root"/secrets.json ] ; then
    echo 'secrets.json exists, remove it - will use secrets.json.scrypt only' >&2
    exit 1
fi

declare secrets

function decrypt_secrets {
    secrets="$(scrypt dec -f "$project_root"/secrets.json.scrypt)"

    if [[ "$(sha256sum <<<"$secrets")" != '22ee172d78023ae1bd0f6009d7f2facebbb86ecbc2469908e28314d6436c83fc  -' ]] ; then
        echo "Decrypted secrets.json hash verification failed" >&2
        exit 1
    fi
}

function get_secret {
    if [[ -z "${secrets-}" ]]; then
        echo 'You forgot to run `decrypt_secrets` before accessing secrets' >&2
        exit 1
    fi
    jq -Mr ."$1"."$2" <<<"$secrets"
}
