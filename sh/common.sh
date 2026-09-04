function die {
    if (( $# != 0 )) ; then
        printf '%s\n' "$@" >&2
    fi
    exit 1
}

function utc_month_start_after {
    declare -r _utc_month_start_after_months="$1"
    shift
    if [[ ! $_utc_month_start_after_months =~ ^[0-9]+$ ]] ; then
        die 'Invalid month offset: '"$_utc_month_start_after_months"
    fi

    declare _utc_month_start_after_current
    _utc_month_start_after_current="$(date -u '+%Y %m')"
    declare -r _utc_month_start_after_current
    declare -i _utc_month_start_after_index
    _utc_month_start_after_index=$((
        ${_utc_month_start_after_current% *} * 12
        + 10#${_utc_month_start_after_current#* } - 1
        + 10#$_utc_month_start_after_months
    ))
    declare -r -i _utc_month_start_after_index
    declare -r -i _utc_month_start_after_year=$((_utc_month_start_after_index / 12))
    declare -r -i _utc_month_start_after_month=$((_utc_month_start_after_index % 12 + 1))

    declare _utc_month_start_after_date
    if date -d '1 second' &>/dev/null ; then
        printf -v _utc_month_start_after_date \
            '%04d-%02d-01T00:00:00-00:00' \
            $_utc_month_start_after_year $_utc_month_start_after_month
        date -u -d "$_utc_month_start_after_date" +%s
    else
        # BSD date accepts MMDDhhmmCCYY rather than ISO 8601.
        printf -v _utc_month_start_after_date \
            '%02d010000%04d' \
            $_utc_month_start_after_month $_utc_month_start_after_year
        date -u -j "$_utc_month_start_after_date" +%s
    fi
}

. "$project_root"/sh/common_bash_version_check.sh

function register_exit_cleanup {
    # In a subshell, `trap -p` reports the parent's traps, so composing here would rerun the
    # parent's cleanups at subshell exit.
    if (( BASH_SUBSHELL != 0 )) ; then
        die '`register_exit_cleanup` must not be called in a subshell'
    fi

    declare -r _register_exit_cleanup="$1"
    shift

    # `trap -p` emits the trap body as a single shell-quoted word, so `eval`ing its output inside an
    # array assignment recovers the body verbatim (embedded quotes included) without executing any
    # of it.
    declare -r IFS=' '
    declare -a _register_exit_trap
    eval "_register_exit_trap=( $(trap -p EXIT) )"
    declare -r -a _register_exit_trap

    if (( ${#_register_exit_trap[@]} == 0 )) || [[ ${_register_exit_trap[*]} = 'trap -- - EXIT' ]] ; then
        trap 'trap - EXIT; set +eu; '"$_register_exit_cleanup" EXIT
        return
    fi

    if (( ${#_register_exit_trap[@]} != 4 )) || [[ ${_register_exit_trap[2]} != 'trap - EXIT; set +eu; '* ]] ; then
        die '`trap EXIT` cleanup malformed; cannot add a new cleanup'
    fi

    # Cleanups run in the reverse of registration order and are newline-joined so that a cleanup
    # ending in a comment or `&` cannot swallow the cleanups registered before it.
    trap 'trap - EXIT; set +eu; '"$_register_exit_cleanup"$'\n'"${_register_exit_trap[2]#trap - EXIT; set +eu; }" EXIT
}

if ! hash forge &>/dev/null ; then
    die 'foundry is not installed'
fi

if ! hash cast &>/dev/null ; then
    die 'cast is not installed'
fi

declare foundry_version
foundry_version="$(forge --version)"
declare -r foundry_version

declare cast_version
cast_version="$(cast --version)"
declare -r cast_version

declare foundry_flavor
if [[ $foundry_version == *foundry-zksync* ]] ; then
    foundry_flavor=zkfoundry
else
    foundry_flavor=vanilla
fi
declare -r foundry_flavor

declare cast_flavor
if [[ $cast_version == *foundry-zksync* ]] ; then
    cast_flavor=zkfoundry
else
    cast_flavor=vanilla
fi
declare -r cast_flavor

if [[ $cast_flavor != "$foundry_flavor" ]] ; then
    die '`forge` and `cast` are from different Foundry toolchains' \
        'forge: '"$foundry_version" \
        'cast:  '"$cast_version"
fi

declare -r vanilla_foundry_version=b0a9dd9ceda36f63e2326ce530c10e6916f4b8a2
declare -r zk_foundry_version=foundry-zksync-v0.1.9

if ! hash curl &>/dev/null ; then
    die 'curl is not installed'
fi

if ! hash jq &>/dev/null ; then
    die 'jq is not installed'
fi

if [ ! -f "$project_root"/api_secrets.json ] ; then
    die 'api_secrets.json is missing'
fi

declare api_secrets_permissions
api_secrets_permissions="$(ls -l "$project_root"/api_secrets.json)"
api_secrets_permissions="${api_secrets_permissions::10}"
declare -r api_secrets_permissions
if [[ $api_secrets_permissions != '-rw-------' ]] ; then
    die 'api_secrets.json permissions too lax' \
        'run: chmod 600 api_secrets.json'
fi

if (( $# == 0 )) ; then
    die 'chain_name argument is missing'
fi
declare -r chain_name="$1"
shift

if [[ $(jq -Mr .'"'"$chain_name"'"' < "$project_root"/api_secrets.json) = [nN][uU][lL][lL] ]] ; then
    die "$chain_name"' is missing from api_secrets.json'
fi

function get_api_secret {
    jq -Mr .'"'"$chain_name"'"'."$1" < "$project_root"/api_secrets.json
}

function get_config {
    jq -Mr .'"'"$chain_name"'"'."$1" < "$project_root"/chain_config.json
}

function get_config_strict {
    declare _get_config_strict_result
    _get_config_strict_result="$(get_config "$1")"
    declare -r _get_config_strict_result
    if [[ ${_get_config_strict_result:-null} = [nN][uU][lL][lL] ]] ; then
        die 'Config key '"$1"' is missing for chain '"$chain_name"
    fi
    echo "$_get_config_strict_result"
}

if [[ ${IGNORE_HARDFORK-no} != [Yy]es ]] ; then
    if [[ $(get_config hardfork.shanghai) != [Tt]rue ]] ; then
        die 'You are on the wrong branch (switch to `fork/london`)'
    fi

    if [[ $(get_config hardfork.cancun) != [Tt]rue ]] ; then
        die 'You are on the wrong branch (switch to `fork/shanghai`)'
    fi

    if [[ $(get_config hardfork.osaka) != [Tt]rue ]] ; then
        die 'You are on the wrong branch (switch to `fork/cancun`)'
    fi
fi

declare era_vm
era_vm="$(get_config hardfork.eraVm)"
declare -r era_vm

if [[ $foundry_flavor = zkfoundry ]] && [[ $era_vm = [Ff]alse ]] ; then
    die 'zkFoundry must not be used on non-EraVM chains' \
        'Run this script with vanilla Foundry v1.5.1 first in PATH'
fi

if [[ $foundry_flavor = vanilla ]] ; then
    if [[ $foundry_version != *"$vanilla_foundry_version"* ]] ; then
        die 'Wrong vanilla Foundry version installed' \
            'Run `foundryup -i v1.5.1`' \
            'This doesn'"'"'t work on old versions of `foundryup`' \
            'You have to `curl -L https://foundry.paradigm.xyz | bash` to update `foundryup`'
    fi
    if [[ $cast_version != *"$vanilla_foundry_version"* ]] ; then
        die 'Wrong vanilla cast version installed' \
            'Run `foundryup -i v1.5.1`'
    fi
else
    if [[ $foundry_version != *"$zk_foundry_version"* ]] ; then
        die 'Wrong zkFoundry version installed' \
            'Run `foundryup-zksync -i '"$zk_foundry_version"'`'
    fi
    if [[ $cast_version != *"$zk_foundry_version"* ]] ; then
        die 'Wrong zkFoundry cast version installed' \
            'Run `foundryup-zksync -i '"$zk_foundry_version"'`'
    fi
fi

function require_vanilla_foundry {
    if [[ $foundry_flavor != vanilla ]] ; then
        die 'This operation requires vanilla Foundry, but `forge` is the zkFoundry fork' \
            'Run `foundryup -i v1.5.1` and make sure it is first in PATH'
    fi
}

function require_zk_foundry {
    if [[ $era_vm = [Ff]alse ]] ; then
        die 'This operation requested zkFoundry on a non-EraVM chain'
    fi
    if [[ $foundry_flavor != zkfoundry ]] ; then
        die 'This operation requires the zkFoundry fork for EraVM bytecode' \
            'Install it with `foundryup-zksync -i '"$zk_foundry_version"'` and make sure it is first in PATH'
    fi
}

if [[ $era_vm != [Ff]alse ]] ; then
    if (( $(get_config gasMultiplierPercent) < 500 )) ; then
        die 'EraVm chains must set a gas multiplier of 5x or more'
    fi
fi

declare -i chainid
chainid="$(get_config chainId)"
declare -r -i chainid

declare chain_display_name
chain_display_name="$(get_config displayName)"
declare -r chain_display_name

declare rpc_url
rpc_url="$(get_api_secret rpcUrl)"
declare -r rpc_url

if [[ ${rpc_url:-null} = [nN][uU][lL][lL] ]] ; then
    die '`rpcUrl` is unset in `api_secrets.json` for chain "'"$chain_name"'"'
fi

declare -i rpc_chainid
rpc_chainid="$(cast chain-id --rpc-url "$rpc_url")"
declare -r -i rpc_chainid

if (( rpc_chainid != chainid )) ; then
    die 'Your RPC thinks you are on chain '$rpc_chainid'. You probably have the wrong RPC.'
fi

declare -a extra_flags
extra_flags=( $(get_config extraFlags) )
declare -r -a extra_flags

function verify_contract {
    declare -r _verify_constructor_args="$1"
    shift
    declare -r _verify_deployed_address="$1"
    shift
    declare -r _verify_source_path="$1"
    shift
    declare -a _verify_extra_flags
    if (( $# > 0 )) ; then
        _verify_extra_flags+=(--compiler-version "$1")
        shift
    fi
    if [[ $foundry_flavor == zkfoundry ]] ; then
        _verify_extra_flags+=(--zksync)
    fi
    declare -r -a _verify_extra_flags

    declare _verify_etherscanApi
    _verify_etherscanApi="$(get_api_secret etherscanApi)"
    if [[ ${_verify_etherscanApi:-null} == [nN][uU][lL][lL] ]] ; then
        _verify_etherscanApi="$(get_config etherscanApi)"
    fi
    declare -r _verify_etherscanApi

    declare _verify_blockscoutApi
    _verify_blockscoutApi="$(get_api_secret blockscoutApi)"
    if [[ ${_verify_blockscoutApi:-null} == [nN][uU][lL][lL] ]] ; then
        _verify_blockscoutApi="$(get_config blockscoutApi)"
    fi
    declare -r _verify_blockscoutApi

    declare _verify_sourcifyApi
    _verify_sourcifyApi="$(get_api_secret sourcifyApi)"
    if [[ ${_verify_sourcifyApi:-null} == [nN][uU][lL][lL] ]] ; then
        _verify_sourcifyApi="$(get_config sourcifyApi)"
    fi
    declare -r _verify_sourcifyApi

    if [[ ${_verify_etherscanApi:-null} != [nN][uU][lL][lL] ]] ; then
        declare _verify_etherscanKey
        _verify_etherscanKey="$(get_api_secret etherscanKey)"
        declare -r _verify_etherscanKey

        if [[ ${_verify_etherscanKey:-null} == [nN][uU][lL][lL] ]] ; then
            forge verify-contract --watch --verifier custom --verifier-url "$_verify_etherscanApi" --constructor-args "$_verify_constructor_args" "${_verify_extra_flags[@]}" "$_verify_deployed_address" "$_verify_source_path"
        elif [[ $_verify_etherscanApi == https://api.etherscan.io/v2/api* ]] ; then
            forge verify-contract --watch --verifier etherscan --verifier-api-key "$_verify_etherscanKey" --verifier-url "$_verify_etherscanApi" --constructor-args "$_verify_constructor_args" "${_verify_extra_flags[@]}" "$_verify_deployed_address" "$_verify_source_path"
        else
            forge verify-contract --watch --chain "$chainid" --verifier custom --verifier-api-key "$_verify_etherscanKey" --verifier-url "$_verify_etherscanApi" --constructor-args "$_verify_constructor_args" "${_verify_extra_flags[@]}" "$_verify_deployed_address" "$_verify_source_path"
        fi
    fi

    if [[ ${_verify_blockscoutApi:-null} != [nN][uU][lL][lL] ]] ; then
        forge verify-contract --watch --chain $chainid --verifier blockscout --verifier-url "$_verify_blockscoutApi" --constructor-args "$_verify_constructor_args" "${_verify_extra_flags[@]}" "$_verify_deployed_address" "$_verify_source_path"
    fi

    if [[ ${_verify_sourcifyApi:-null} != [nN][uU][lL][lL] ]] ; then
        forge verify-contract --watch --chain $chainid --verifier sourcify --verifier-url "$_verify_sourcifyApi" --constructor-args "$_verify_constructor_args" "${_verify_extra_flags[@]}" "$_verify_deployed_address" "$_verify_source_path"
    fi
}
