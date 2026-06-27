declare secrets

if [[ ${DECRYPT_SECRETS-yes} = [Nn]o ]] ; then
    # Read public values from secrets.json.template (no decryption needed)
    if [ ! -f "$project_root"/secrets.json.template ] ; then
        die 'secrets.json.template is missing'
    fi

    function decrypt_secrets {
        secrets="$(<"$project_root"/secrets.json.template)"
    }

    function get_secret {
        declare _secret_value
        _secret_value="$(jq -Mr ."$1"."$2" <<<"$secrets")"
        if [[ ${_secret_value:-unset} = 'unset' ]] || [[ $_secret_value = 'null' ]] ; then
            die 'Secret "'"$1"'.'"$2"'" requires decryption but DECRYPT_SECRETS=no'
        fi
        echo "$_secret_value"
    }
else
    if ! hash sha256sum &>/dev/null ; then
        die 'sha256sum is not installed'
    fi

    if ! hash scrypt &>/dev/null ; then
        die 'scrypt is not installed'
    fi

    if [ ! -f "$project_root"/secrets.json.scrypt ] ; then
        die 'secrets.json.scrypt is missing'
    fi

    declare secrets_permissions
    secrets_permissions="$(ls -l "$project_root"/secrets.json.scrypt)"
    secrets_permissions="${secrets_permissions::10}"
    declare -r secrets_permissions
    if [[ $secrets_permissions != '-rw-------' ]] ; then
        die 'secrets.json.scrypt permissions too lax' \
            'run: chmod 600 secrets.json.scrypt'
    fi

    if [ -f "$project_root"/secrets.json ] ; then
        die 'secrets.json exists, remove it - will use secrets.json.scrypt only'
    fi

    function decrypt_secrets {
        secrets="$(scrypt dec -f "$project_root"/secrets.json.scrypt)"

        if [[ "$(jq -cM <<<"$secrets" | sha256sum)" != 'a6290f70ec6fd0d919093736c02ef2f1a12a3fa17a2984a97f94cc9cd6e16592  -' ]] ; then
            die 'Decrypted secrets.json hash verification failed'
        fi
    }

    function get_secret {
        if [[ -z "${secrets-}" ]]; then
            die 'You forgot to run `decrypt_secrets` before accessing secrets'
        fi
        jq -Mr ."$1"."$2" <<<"$secrets"
    }
fi
