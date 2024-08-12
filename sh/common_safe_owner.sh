declare -r get_owners_sig='getOwners()(address[])'
declare owners
owners="$(cast abi-decode "$get_owners_sig" "$(cast call --rpc-url "$rpc_url" "$safe_address" "$(cast calldata "$get_owners_sig")")")"
owners="${owners:1:$((${#owners} - 2))}"
owners="${owners//, /;}"
declare -r owners

declare -a owners_array
IFS=';' read -r -a owners_array <<<"$owners"
declare -r -a owners_array

PS3='Who are you?: '
declare signer
select signer in "${owners_array[@]}" ; do break ; done
declare -r signer

if [[ ${signer:-unset} = 'unset' ]] ; then
    echo 'I do not know who that is' >&2
    exit 1
fi
