if ! hash sha256sum &>/dev/null ; then
    echo 'sha256sum is not installed' >&2
    exit 1
fi

if [ ! -f "$project_root"/secrets.json ] ; then
    echo 'secrets.json is missing' >&2
    exit 1
fi

if [[ $(ls -l secrets.json | cut -d' ' -f1 | cut -d. -f1) != '-rw-------' ]] ; then
    echo 'secrets.json permissions too lax' >&2
    echo 'run: chmod 600 secrets.json' >&2
    exit 1
fi

if ! sha256sum -c <<<'bb82de121880f1182dbae410b341749e5ac1355954ae6c03151a1826e7bba745  secrets.json' >/dev/null ; then
    echo 'Secrets are wrong' >&2
    exit 1
fi

function get_secret {
    jq -Mr ."$1"."$2" < "$project_root"/secrets.json
}
