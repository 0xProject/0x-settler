# Reads public addresses from secrets.json.template

if ! hash jq &>/dev/null ; then
    echo 'jq is not installed' >&2
    exit 1
fi

if [ ! -f "$project_root"/secrets.json.template ] ; then
    echo 'secrets.json.template is missing' >&2
    exit 1
fi

function get_public_secret {
    jq -Mr ."$1"."$2" < "$project_root"/secrets.json.template
}
