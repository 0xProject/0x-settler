if ! hash sha256sum &>/dev/null ; then
    echo 'sha256sum is not installed' >&2
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

declare secrets_storage

function decrypt_secrets {
    local password
    echo 'Enter passphrase for secrets.json.scrypt'
    local decrypted
    decrypted="$(scrypt dec "$project_root"/secrets.json.scrypt)"
    if [ $? -ne 0 ]; then
        echo "Failed to decrypt secrets.json.scrypt" >&2
        exit 1
    fi

    # 24290900be9575d1fb6349098b1c11615a2eac8091bc486bec6cf67239b7846a previous version prior to allowanceHolderLondon
    if ! echo "$decrypted" | sha256sum | grep -q "^bb82de121880f1182dbae410b341749e5ac1355954ae6c03151a1826e7bba745"; then
        echo "Decrypted secrets.json hash verification failed" >&2
        exit 1
    fi
    secrets_storage="$decrypted"
}

function get_secret {
    if [ -z "$secrets_storage" ]; then
        decrypt_secrets
    fi
    jq -Mr ."$1"."$2" <<< "$secrets_storage"
}
