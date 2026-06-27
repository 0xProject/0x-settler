. "$project_root"/sh/common_bash_version_check.sh

function register_exit_cleanup {
    declare -r _register_exit_cleanup="$1"
    declare _register_exit_trap
    _register_exit_trap="$(trap -p EXIT)"

    if [[ -z $_register_exit_trap ]] || [[ $_register_exit_trap = 'trap -- - EXIT' ]] ; then
        trap 'trap - EXIT; set +e; '"$_register_exit_cleanup" EXIT
        return
    fi

    if [[ $_register_exit_trap != "trap -- 'trap - EXIT; set +e; "* ]] || [[ $_register_exit_trap != *"' EXIT" ]] ; then
        echo '`trap EXIT` cleanup malformed; cannot add a new cleanup' >&2
        exit 1
    fi
    _register_exit_trap="${_register_exit_trap%\' EXIT}"
    _register_exit_trap="${_register_exit_trap#trap -- \'trap - EXIT; set +e; }"
    trap 'trap - EXIT; set +e; '"$_register_exit_cleanup"'; '"$_register_exit_trap" EXIT
}

if ! hash forge &>/dev/null ; then
    echo 'foundry is not installed' >&2
    exit 1
fi

if ! hash cast &>/dev/null ; then
    echo 'cast is not installed' >&2
    exit 1
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
    echo '`forge` and `cast` are from different Foundry toolchains' >&2
    echo 'forge: '"$foundry_version" >&2
    echo 'cast:  '"$cast_version" >&2
    exit 1
fi

function require_vanilla_foundry {
    if [[ $foundry_flavor != vanilla ]] ; then
        echo 'This operation requires vanilla Foundry, but `forge` is the zkFoundry fork' >&2
        exit 1
    fi
}

function require_zk_foundry {
    if [[ $era_vm != [Tt]rue ]] ; then
        echo 'This operation requested zkFoundry on a non-EraVM chain' >&2
        exit 1
    fi
    if [[ $foundry_flavor != zkfoundry ]] ; then
        echo 'This operation requires the zkFoundry fork for EraVM bytecode' >&2
        echo 'Install it with `foundryup-zksync --install 0.1.9` and make sure it is first in PATH' >&2
        exit 1
    fi
}

if ! hash curl &>/dev/null ; then
    echo 'curl is not installed' >&2
    exit 1
fi

if ! hash jq &>/dev/null ; then
    echo 'jq is not installed' >&2
    exit 1
fi

if [ ! -f "$project_root"/api_secrets.json ] ; then
    echo 'api_secrets.json is missing' >&2
    exit 1
fi

declare api_secrets_permissions
api_secrets_permissions="$(ls -l "$project_root"/api_secrets.json)"
api_secrets_permissions="${api_secrets_permissions::10}"
declare -r api_secrets_permissions
if [[ $api_secrets_permissions != '-rw-------' ]] ; then
    echo 'api_secrets.json permissions too lax' >&2
    echo 'run: chmod 600 api_secrets.json' >&2
    exit 1
fi

if (( $# == 0 )) ; then
    echo 'chain_name argument is missing' >&2
    exit 1
fi
declare -r chain_name="$1"
shift

if [[ $(jq -Mr .'"'"$chain_name"'"' < "$project_root"/api_secrets.json) == 'null' ]] ; then
    echo "$chain_name"' is missing from api_secrets.json' >&2
    exit 1
fi

function get_api_secret {
    jq -Mr .'"'"$chain_name"'"'."$1" < "$project_root"/api_secrets.json
}

function get_config {
    jq -Mr .'"'"$chain_name"'"'."$1" < "$project_root"/chain_config.json
}

if [[ ${IGNORE_HARDFORK-no} != [Yy]es ]] ; then
    if [[ $(get_config hardfork.shanghai) != [Tt]rue ]] ; then
        echo 'You are on the wrong branch (switch to `fork/london`)' >&2
        exit 1
    fi

    if [[ $(get_config hardfork.cancun) != [Tt]rue ]] ; then
        echo 'You are on the wrong branch (switch to `fork/shanghai`)' >&2
        exit 1
    fi

    if [[ $(get_config hardfork.osaka) != [Tt]rue ]] ; then
        echo 'You are on the wrong branch (switch to `fork/cancun`)' >&2
        exit 1
    fi
fi

declare era_vm
era_vm="$(get_config hardfork.eraVm)"
declare -r era_vm

if [[ $foundry_flavor = zkfoundry ]] && [[ $era_vm = [Ff]alse ]] ; then
    echo 'zkFoundry must not be used on non-EraVM chains' >&2
    echo 'Run this script with vanilla Foundry v1.5.1 first in PATH' >&2
    exit 1
fi

if [[ $foundry_flavor = vanilla ]] ; then
    if [[ $foundry_version != *b0a9dd9ceda36f63e2326ce530c10e6916f4b8a2* ]] ; then
        echo 'Wrong vanilla Foundry version installed' >&2
        echo 'Run `foundryup -i v1.5.1`' >&2
        echo 'This doesn'"'"'t work on old versions of `foundryup`' >&2
        echo 'You have to `curl -L https://foundry.paradigm.xyz | bash` to update `foundryup`' >&2
        exit 1
    fi
    if [[ $cast_version != *b0a9dd9ceda36f63e2326ce530c10e6916f4b8a2* ]] ; then
        echo 'Wrong vanilla cast version installed' >&2
        echo 'Run `foundryup -i v1.5.1`' >&2
        exit 1
    fi
else
    if [[ $foundry_version != *foundry-zksync-v0.1.9* ]] ; then
        echo 'Wrong zkFoundry version installed' >&2
        echo 'Run `foundryup-zksync --install 0.1.9`' >&2
        exit 1
    fi
    if [[ $cast_version != *foundry-zksync-v0.1.9* ]] ; then
        echo 'Wrong zkFoundry cast version installed' >&2
        echo 'Run `foundryup-zksync --install 0.1.9`' >&2
        exit 1
    fi
fi

if [[ $era_vm != [Ff]alse ]] ; then
    if (( $(get_config gasMultiplierPercent) < 500 )) ; then
        echo 'EraVm chains must set a gas multiplier of 5x or more' >&2
        exit 1
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

if [[ ${rpc_url:-unset} = 'unset' ]] || [[ $rpc_url = 'null' ]] ; then
    echo '`rpcUrl` is unset in `api_secrets.json` for chain "'"$chain_name"'"' >&2
    exit 1
fi

declare -i rpc_chainid
rpc_chainid="$(cast chain-id --rpc-url "$rpc_url")"
declare -r -i rpc_chainid

if (( rpc_chainid != chainid )) ; then
    echo 'Your RPC thinks you are on chain '$rpc_chainid'. You probably have the wrong RPC.' >&2
    exit 1
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
