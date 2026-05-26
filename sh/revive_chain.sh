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

. "$project_root"/sh/common.sh
. "$project_root"/sh/common_secrets.sh

decrypt_secrets

declare -r bridge_settler_skip_clean=Yes
. "$project_root"/sh/common_deploy_settler.sh
. "$project_root"/sh/common_deploy_bridge_settler.sh

declare module_deployer
module_deployer="$(get_secret iceColdCoffee deployer)"
declare -r module_deployer
declare proxy_deployer
proxy_deployer="$(get_secret deployer deployer)"
declare -r proxy_deployer

declare deployer_proxy
deployer_proxy="$(get_config deployment.deployer)"
declare -r deployer_proxy
declare ice_cold_coffee
ice_cold_coffee="$(get_config governance.pause)"
declare -r ice_cold_coffee

declare deployment_safe
deployment_safe="$(get_config governance.deploymentSafe)"
declare -r deployment_safe
declare upgrade_safe
upgrade_safe="$(get_config governance.upgradeSafe)"
declare -r upgrade_safe

declare safe_multicall
safe_multicall="$(get_config safe.multiCall)"
declare -r safe_multicall

# set minimum gas price (mostly for Arbitrum and BNB)
declare -i min_gas_price
min_gas_price="$(get_config minGasPriceGwei)"
min_gas_price=$((min_gas_price * 1000000000))
declare -r -i min_gas_price
declare -i gas_price
gas_price="$(cast gas-price --rpc-url "$rpc_url")"
if (( gas_price < min_gas_price )) ; then
    echo 'Setting gas price to minimum of '$((min_gas_price / 1000000000))' gwei' >&2
    gas_price=$min_gas_price
fi
declare -r -i gas_price

# set gas multiplier/headroom (again mostly for Arbitrum)
declare -i gas_estimate_multiplier
gas_estimate_multiplier="$(get_config gasMultiplierPercent)"
declare -r -i gas_estimate_multiplier

export FOUNDRY_OPTIMIZER_RUNS=1000000

function _run_redeploy_script {
    ICECOLDCOFFEE_DEPLOYER_KEY="$(get_secret iceColdCoffee key)" DEPLOYER_PROXY_DEPLOYER_KEY="$(get_secret deployer key)" \
        forge script                                         \
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
        "$@"                                                 \
        --sig 'run(address,address,address,address,address,address,address,uint128,uint128,uint128,uint128,string,bytes,address[])' \
        $(get_config extraFlags)                             \
        $(get_config extraScriptFlags)                       \
        script/RedeploySettlers.s.sol:RedeploySettlers       \
        "$module_deployer" "$proxy_deployer" "$ice_cold_coffee" "$deployer_proxy" "$deployment_safe" "$upgrade_safe" "$safe_multicall" \
        2 3 4 5 \
        "$chain_display_name" "$constructor_args" "$(IFS=, ; echo "[${solvers[*]}]")"
}

# Always run a dry-run simulation first: populates broadcast/.../dry-run/run-latest.json
# with per-tx gas the node would charge under whatever rules are currently active.
_run_redeploy_script

if [[ ${BROADCAST-no} = [Yy]es ]] ; then
    # Check each deployer's balance against its own subtotal of tx gas (sender-grouped from
    # the dry-run). Auto-tracks active gas pricing including EIP-8037-style changes.
    declare dry_run_json
    dry_run_json="$project_root/broadcast/RedeploySettlers.s.sol/$chainid/dry-run/run-latest.json"
    declare -r dry_run_json
    if [ ! -f "$dry_run_json" ] ; then
        echo "Dry-run JSON not found at $dry_run_json" >&2
        exit 1
    fi

    # Buffer jq's output and check its exit code before iterating: `jq | while read` via process
    # substitution would emit valid prefix rows to stdout before failing, leaving sender_gas
    # partially populated and silently broadcasting an unchecked sender.
    declare jq_out
    if ! jq_out="$(jq -r '.transactions[] | [.transaction.from // error, .transaction.gas // error] | @tsv' "$dry_run_json")" ; then
        echo "Failed to parse dry-run JSON at $dry_run_json" >&2
        exit 1
    fi

    declare -A sender_gas=()
    while IFS=$'\t' read -r from gas_hex ; do
        sender_gas[$from]=$(( ${sender_gas[$from]:-0} + gas_hex ))
    done <<<"$jq_out"

    if (( ${#sender_gas[@]} == 0 )) ; then
        echo "No transactions parsed from dry-run JSON; cannot verify balances" >&2
        exit 1
    fi

    declare sender required actual
    for sender in "${!sender_gas[@]}" ; do
        # `sender_gas` already includes `gas_estimate_multiplier` (forge applies it during
        # simulation before serializing tx.gas), so don't multiply again.
        required="$(bc <<<"$gas_price * ${sender_gas[$sender]}")"
        actual="$(cast balance --rpc-url "$rpc_url" "$sender")"
        if (( $(bc <<<"$actual < $required") )) ; then
            echo "Insufficient ETH at $sender ($actual wei, need >= $required wei for ${sender_gas[$sender]} gas)" >&2
            exit 1
        fi
    done

    _run_redeploy_script --broadcast

    echo 'Settlers redeployed and Safes returned to canonical multisig ownership.' >&2
    echo 'Run `sh/verify_settler.sh '"$chain_name"'` to verify on Etherscan.' >&2
fi
