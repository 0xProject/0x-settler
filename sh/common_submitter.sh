declare -r saved_submitter="$project_root"/config/submitter.txt

declare suggested_submitter=0xEf37aD2BACD70119F141140f7B5E46Cd53a65fc4
if [[ -f "$saved_submitter" && -r "$saved_submitter" ]] ; then
    suggested_submitter="$(<"$saved_submitter")"
fi
declare -r suggested_submitter

declare signer
IFS='' read -p 'What address will you submit with?: ' -e -r -i "$suggested_submitter" signer
declare -r signer

echo "$signer" >"$saved_submitter"
