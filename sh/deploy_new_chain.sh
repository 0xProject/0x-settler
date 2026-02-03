#!/usr/bin/env bash

## POSIX Bash implementation of realpath
## Copied and modified from https://github.com/mkropat/sh-realpath and https://github.com/AsymLabs/realpath-lib/
## Copyright (c) 2014 Michael Kropat - MIT License
## Copyright (c) 2013 Asymmetry Laboratories - MIT License

function realpath {
    _resolve_symlinks "$(_canonicalize "$1")"
}

function _directory {
    local out slsh
    slsh=/
    out="$1"
    out="${out//$slsh$slsh/$slsh}"
    if [ "$out" = / ]; then
        echo /
        return
    fi
    out="${out%/}"
    case "$out" in
        */*)
            out="${out%/*}"
        ;;
        *)
            out=.
        ;;
    esac
    if [ "$out" ]; then
        printf '%s\n' "$out"
    else
        echo /
    fi
}

function _file {
    local out slsh
    slsh=/
    out="$1"
    out="${out//$slsh$slsh/$slsh}"
    if [ "$out" = / ]; then
        echo /
        return
    fi
    out="${out%/}"
    out="${out##*/}"
    printf '%s\n' "$out"
}

function _resolve_symlinks {
    local path pattern context
    while [ -L "$1" ]; do
        context="$(_directory "$1")"
        path="$(POSIXLY_CORRECT=y ls -ld -- "$1" 2>/dev/null)"
        pattern='*'"$(_escape "$1")"' -> '
        path="${path#$pattern}"
        set -- "$(_canonicalize "$(_prepend_context "$context" "$path")")" "$@"
        _assert_no_path_cycles "$@" || return 1
    done
    printf '%s\n' "$1"
}

function _escape {
    local out
    out=''
    local -i i
    for ((i=0; i < ${#1}; i+=1)); do
        out+='\'"${1:$i:1}"
    done
    printf '%s\n' "$out"
}

function _prepend_context {
    if [ "$1" = . ]; then
        printf '%s\n' "$2"
    else
        case "$2" in
            /* ) printf '%s\n' "$2" ;;
             * ) printf '%s\n' "$1/$2" ;;
        esac
    fi
}

function _assert_no_path_cycles {
    local target path

    if [ $# -gt 16 ]; then
        return 1
    fi

    target="$1"
    shift

    for path in "$@"; do
        if [ "$path" = "$target" ]; then
            return 1
        fi
    done
}

function _canonicalize {
    local d f
    if [ -d "$1" ]; then
        (CDPATH= cd -P "$1" 2>/dev/null && pwd -P)
    else
        d="$(_directory "$1")"
        f="$(_file "$1")"
        (CDPATH= cd -P "$d" 2>/dev/null && printf '%s/%s\n' "$(pwd -P)" "$f")
    fi
}

## end POSIX Bash implementation of realpath

set -Eeufo pipefail -o posix

declare project_root
project_root="$(_directory "$(_directory "$(realpath "${BASH_SOURCE[0]}")")")"
declare -r project_root
cd "$project_root"

if [[ ! -f "$project_root"/sh/initial_description_taker.md ]] ; then
    echo 'sh/initial_description_taker.md is missing' >&2
    exit 1
fi
if [[ ! -f "$project_root"/sh/initial_description_metatx.md ]] ; then
    echo 'sh/initial_description_metatx.md is missing' >&2
    exit 1
fi
if [[ ! -f "$project_root"/sh/initial_description_bridge_settler.md ]] ; then
    echo 'sh/initial_description_bridge_settler.md is missing' >&2
    exit 1
fi

. "$project_root"/sh/common.sh
. "$project_root"/sh/common_secrets.sh

decrypt_secrets

. "$project_root"/sh/common_deploy_settler.sh

declare -r bridge_settler_skip_clean=Yes

. "$project_root"/sh/common_deploy_bridge_settler.sh

declare module_deployer
module_deployer="$(get_secret iceColdCoffee deployer)"
declare -r module_deployer
declare proxy_deployer
proxy_deployer="$(get_secret deployer deployer)"
declare -r proxy_deployer
# we can't do key derivation in Bash, so we rely on the Foundry script to check that these are correct
declare deployer_proxy
deployer_proxy="$(get_secret deployer address)"
declare -r deployer_proxy
declare ice_cold_coffee
ice_cold_coffee="$(get_secret iceColdCoffee address)"
declare -r ice_cold_coffee
declare deployer_impl
deployer_impl="$(cast keccak "$(cast to-rlp '["'"$module_deployer"'", "0x01"]')")"
deployer_impl="$(cast to-check-sum-address "0x${deployer_impl:26:40}")"
declare -r deployer_impl

declare taker_submitted_description
taker_submitted_description="$(jq -MRs < "$project_root"/sh/initial_description_taker.md)"
taker_submitted_description="${taker_submitted_description:1:$((${#taker_submitted_description} - 2))}"
declare -r taker_submitted_description
declare metatransaction_description
metatransaction_description="$(jq -MRs < "$project_root"/sh/initial_description_metatx.md)"
metatransaction_description="${metatransaction_description:1:$((${#metatransaction_description} - 2))}"
declare -r metatransaction_description
declare intents_description
intents_description="$(jq -MRs < "$project_root"/sh/initial_description_intent.md)"
intents_description="${intents_description:1:$((${#intents_description} - 2))}"
declare -r intents_description
declare bridge_description
bridge_description="$(jq -MRs < "$project_root"/sh/initial_description_bridge_settler.md)"
bridge_description="${bridge_description:1:$((${#bridge_description} - 2))}"
declare -r bridge_description

# safe constants
declare safe_factory
safe_factory="$(get_config safe.factory)"
declare -r safe_factory
declare safe_singleton
safe_singleton="$(get_config safe.singleton)"
declare -r safe_singleton
declare safe_creation_sig
safe_creation_sig='proxyCreationCode()(bytes)'
declare -r safe_creation_sig
declare safe_initcode
safe_initcode="$(cast abi-decode "$safe_creation_sig" "$(cast call --rpc-url "$rpc_url" "$safe_factory" "$(cast calldata "$safe_creation_sig")")")"
declare -r safe_initcode
declare safe_inithash
if [[ $era_vm = [Ff]alse ]] ; then
    safe_inithash="$(cast keccak "$(cast concat-hex "$safe_initcode" "$(cast to-uint256 "$safe_singleton")")")"
else
    # https://web.archive.org/web/20251108135035/https://docs.zksync.io/zksync-protocol/era-vm/differences/evm-instructions#datasize-dataoffset-datacopy
    # https://web.archive.org/web/20251108134721/https://matter-labs.github.io/zksync-era/core/latest/guides/advanced/12_alternative_vm_intro.html#bytecode-hashes
    safe_inithash=0x"${safe_initcode:74:64}"

    declare safe_constructorhash
    safe_constructorhash="$(cast keccak "$(cast to-uint256 "$safe_singleton")")"
    declare -r safe_constructorhash
fi
declare -r safe_inithash
declare safe_fallback
safe_fallback="$(get_config safe.fallback)"
declare -r safe_fallback
declare safe_multicall
safe_multicall="$(get_config safe.multiCall)"
declare -r safe_multicall

# compute deployment safe
declare -r setup_signature='setup(address[] owners,uint256 threshold,address to,bytes data,address fallbackHandler,address paymentToken,uint256 paymentAmount,address paymentReceiver)'
declare deployment_safe_initializer
deployment_safe_initializer="$(
    cast calldata            \
    "$setup_signature"       \
    '['"$module_deployer"']' \
    1                        \
    $(cast address-zero)     \
    0x                       \
    "$safe_fallback"         \
    $(cast address-zero)     \
    0                        \
    $(cast address-zero)
)"
declare -r deployment_safe_initializer
declare deployment_safe_salt
deployment_safe_salt="$(cast keccak "$(cast concat-hex "$(cast keccak "$deployment_safe_initializer")" "$(cast hash-zero)")")"
declare -r deployment_safe_salt
declare deployment_safe
if [[ $era_vm = [Ff]alse ]] ; then
    deployment_safe="$(cast keccak "$(cast concat-hex 0xff "$safe_factory" "$deployment_safe_salt" "$safe_inithash")")"
else
    deployment_safe="$(cast keccak "$(cast concat-hex "$(cast keccak zksyncCreate2)" "$(cast to-uint256 "$safe_factory")" "$deployment_safe_salt" "$safe_inithash" "$safe_constructorhash")")"
fi
deployment_safe="$(cast to-check-sum-address "0x${deployment_safe:26:40}")"
declare -r deployment_safe

# compute ugprade safe
declare upgrade_safe_initializer
upgrade_safe_initializer="$(
    cast calldata           \
    "$setup_signature"      \
    '['"$proxy_deployer"']' \
    1                       \
    $(cast address-zero)    \
    0x                      \
    "$safe_fallback"        \
    $(cast address-zero)    \
    0                       \
    $(cast address-zero)
)"
declare -r upgrade_safe_initializer
declare upgrade_safe_salt
upgrade_safe_salt="$(cast keccak "$(cast concat-hex "$(cast keccak "$upgrade_safe_initializer")" "$(cast hash-zero)")")"
declare -r upgrade_safe_salt
declare upgrade_safe
if [[ $era_vm = [Ff]alse ]] ; then
    upgrade_safe="$(cast keccak "$(cast concat-hex 0xff "$safe_factory" "$upgrade_safe_salt" "$safe_inithash")")"
else
    upgrade_safe="$(cast keccak "$(cast concat-hex "$(cast keccak zksyncCreate2)" "$(cast to-uint256 "$safe_factory")" "$upgrade_safe_salt" "$safe_inithash" "$safe_constructorhash")")"
fi
upgrade_safe="$(cast to-check-sum-address "0x${upgrade_safe:26:40}")"
declare -r upgrade_safe

. "$project_root"/sh/common_gas.sh

declare -a maybe_broadcast=()
if [[ ${BROADCAST-no} = [Yy]es ]] ; then
    maybe_broadcast+=(--broadcast)
fi
declare -r -a maybe_broadcast

if [[ ${BROADCAST-no} = [Yy]es ]] ; then
    if (( $(cast balance --rpc-url "$rpc_url" "$module_deployer") == 0 )) ; then
        echo 'You forgot to send ETH to '"$module_deployer"'.' >&2
        exit 1
    fi
    if (( $(cast balance --rpc-url "$rpc_url" "$proxy_deployer") == 0 )) ; then
        echo 'You forgot to send ETH to '"$proxy_deployer"'.' >&2
        exit 1
    fi
fi

export FOUNDRY_OPTIMIZER_RUNS=1000000

declare ICECOLDCOFFEE_DEPLOYER_KEY
ICECOLDCOFFEE_DEPLOYER_KEY="$(get_secret iceColdCoffee key)"
export ICECOLDCOFFEE_DEPLOYER_KEY
declare DEPLOYER_PROXY_DEPLOYER_KEY
DEPLOYER_PROXY_DEPLOYER_KEY="$(get_secret deployer key)"
export DEPLOYER_PROXY_DEPLOYER_KEY
forge script                                             \
    --slow                                               \
    --no-storage-caching                                 \
    --skip 'Flat.sol'                                    \
    --skip 'CrossChainReceiverFactory.sol'               \
    --skip 'src/allowanceholder/*.sol'                   \
    --skip 'src/chains/*.sol'                            \
    --skip 'src/core/*.sol'                              \
    --skip 'src/multicall/*.sol'                         \
    --skip 'src/utils/*.sol'                             \
    --gas-estimate-multiplier $gas_estimate_multiplier   \
    --with-gas-price $gas_price                          \
    --chain $chainid                                     \
    --rpc-url "$rpc_url"                                 \
    -vvvvv                                               \
    "${maybe_broadcast[@]}"                              \
    --sig 'run(bool,address,address,address,address,address,address,address,address,address,address,uint128,uint128,uint128,uint128,string,string,string,string,string,bytes,address[])' \
    "${extra_flags[@]}"                                  \
    $(get_config extraScriptFlags)                       \
    script/DeploySafes.s.sol:DeploySafes                 \
    "$era_vm" "$module_deployer" "$proxy_deployer" "$ice_cold_coffee" "$deployer_proxy" "$deployment_safe" "$upgrade_safe" "$safe_factory" "$safe_singleton" "$safe_fallback" "$safe_multicall" \
    2 3 4 5 "$taker_submitted_description" "$metatransaction_description" "$intents_description" "$bridge_description" \
    "$chain_display_name" "$constructor_args" "$(IFS=, ; echo "[${solvers[*]}]")"
unset -v ICECOLDCOFFEE_DEPLOYER_KEY
unset -v DEPLOYER_PROXY_DEPLOYER_KEY

if [[ ${BROADCAST-no} = [Yy]es ]] ; then
    echo 'Waiting for 1 minute for Etherscan to pick up the deployment' >&2
    sleep 60

    echo 'Verifying pause Safe module' >&2

    verify_contract "$(cast abi-encode 'constructor(address)' "$deployment_safe")" "$ice_cold_coffee" src/deployer/SafeModule.sol:ZeroExSettlerDeployerSafeModule

    echo 'Verified Safe module -- now verifying Deployer implementation' >&2

    verify_contract "$(cast abi-encode 'constructor(uint256)' 1)" "$deployer_impl" src/deployer/Deployer.sol:Deployer

    echo 'Run ./sh/verify_settler.sh and ./sh/verify_bridge_settler.sh to verify newly-deployed Settlers' >&2
fi

echo 'Deployment is complete' >&2
echo 'Add the following to your chain_config.json' >&2
echo '"governance": {' >&2
echo '	"upgradeSafe": "'"$upgrade_safe"'",' >&2
echo '	"deploymentSafe": "'"$deployment_safe"'",' >&2
echo '	"pause": "'"$ice_cold_coffee"'"' >&2
echo '},' >&2
echo '"deployment": {' >&2
echo '	"deployer": "'"$deployer_proxy"'"' >&2
echo '}' >&2
