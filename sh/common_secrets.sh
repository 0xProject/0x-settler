declare secrets

if [[ ${DECRYPT_SECRETS-yes} = [Nn]o ]] ; then
    # Read public values from secrets.json.template (no decryption needed)
    if [ ! -f "$project_root"/secrets.json.template ] ; then
        echo 'secrets.json.template is missing' >&2
        exit 1
    fi

    function decrypt_secrets {
        secrets="$(<"$project_root"/secrets.json.template)"
    }

    function get_secret {
        declare _secret_value
        _secret_value="$(jq -Mr ."$1"."$2" <<<"$secrets")"
        if [[ ${_secret_value:-unset} = 'unset' ]] || [[ $_secret_value = 'null' ]] ; then
            echo 'Secret "'"$1"'.'"$2"'" requires decryption but DECRYPT_SECRETS=no' >&2
            exit 1
        fi
        echo "$_secret_value"
    }
else
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

    function decrypt_secrets {
        secrets="$(scrypt dec -f "$project_root"/secrets.json.scrypt)"

        if [[ "$(jq -cM <<<"$secrets" | sha256sum)" != '9ab39d18541f716172c96cc7a1bf79350364bae743faf846109d89de32a2db4e  -' ]] ; then
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
fi
