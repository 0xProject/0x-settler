if (( BASH_VERSINFO[0] < 5 )) ; then
    echo 'Your `bash` is too old. Upgrade to version 5' >&2
    exit 1
fi
