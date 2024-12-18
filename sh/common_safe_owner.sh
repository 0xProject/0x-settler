declare signer

declare -r saved_safe_owner="$project_root"/config/safe_owner.txt
if [[ -f "$saved_safe_owner" && -r "$saved_safe_owner" ]] ; then
    signer="$(<"$saved_safe_owner")"
fi

contains() {
    declare -r elem="$1"
    shift

    declare i
    for i ; do
        if [[ $i == "$elem" ]] ; then
            return 0
        fi
    done

    return 1
}

if ! contains "${signer-unset}" "${owners_array[@]}" ; then
    PS3='Who are you?: '
    select signer in "${owners_array[@]}" ; do break ; done

    if [[ ${signer:-unset} = 'unset' ]] ; then
        echo 'I do not know who that is' >&2
        exit 1
    fi

    echo "$signer" >"$saved_safe_owner"
fi

declare -r signer
