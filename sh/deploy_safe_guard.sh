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

if (( $# != 0 )) ; then
    die 'Unexpected extra arguments'
fi

function ensure_hex {
    declare _ensure_hex_value="$1"
    if [[ $_ensure_hex_value != 0x* ]] ; then
        _ensure_hex_value=0x"$_ensure_hex_value"
    fi
    echo "$_ensure_hex_value"
}

function checksum_address {
    cast to-check-sum-address "$1"
}

function require_address {
    declare -r _require_address_value="$1"
    declare -r _require_address_label="$2"
    if [[ ! $_require_address_value =~ ^0x[0-9a-fA-F]{40}$ ]] ; then
        die "$_require_address_label is not an address: $_require_address_value"
    fi
}

function require_non_null {
    declare -r _require_non_null_value="$1"
    declare -r _require_non_null_label="$2"
    if [[ ${_require_non_null_value:-null} = [Nn][Uu][Ll][Ll] || -z $_require_non_null_value ]] ; then
        die "$_require_non_null_label is not configured"
    fi
}

function get_safe_config {
    declare -r _get_safe_config_key="$1"
    jq -Mr --arg chain "$chain_name" --arg version "$safe_version" --arg key "$_get_safe_config_key" \
        '.[$chain].safe[$version][$key]' < "$project_root"/chain_config.json
}

function parse_storage_address {
    checksum_address "$(cast parse-bytes32-address "$1")"
}

function require_code {
    declare -r _require_code_address="$1"
    declare -r _require_code_label="$2"
    declare _require_code_code
    _require_code_code="$(cast code --rpc-url "$rpc_url" "$_require_code_address")"
    declare -r _require_code_code
    if [[ $_require_code_code = 0x || $_require_code_code = 0x0 ]] ; then
        die "$_require_code_label has no code at $_require_code_address"
    fi
}

function code_hash {
    cast keccak "$(cast code --rpc-url "$rpc_url" "$1")"
}

function preapproved_signature {
    cast concat-hex "$(cast to-uint256 "$1")" "$(cast hash-zero)" 0x01
}

function verify_zksync_contract {
    declare -r _verify_constructor_args="$1"
    shift
    declare -r _verify_deployed_address="$1"
    shift
    declare -r _verify_source_path="$1"
    shift

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

    if [[ ${_verify_etherscanApi:-null} != [nN][uU][lL][lL] ]] ; then
        declare _verify_etherscanKey
        _verify_etherscanKey="$(get_api_secret etherscanKey)"
        declare -r _verify_etherscanKey

        if [[ ${_verify_etherscanKey:-null} == [nN][uU][lL][lL] ]] ; then
            forge verify-contract --zksync --watch --verifier custom --verifier-url "$_verify_etherscanApi" \
                --constructor-args "$_verify_constructor_args" "$_verify_deployed_address" "$_verify_source_path"
        elif [[ $_verify_etherscanApi == https://api.etherscan.io/v2/api* ]] ; then
            forge verify-contract --zksync --watch --verifier etherscan --verifier-api-key "$_verify_etherscanKey" \
                --verifier-url "$_verify_etherscanApi" --constructor-args "$_verify_constructor_args" \
                "$_verify_deployed_address" "$_verify_source_path"
        else
            forge verify-contract --zksync --watch --chain "$chainid" --verifier custom \
                --verifier-api-key "$_verify_etherscanKey" --verifier-url "$_verify_etherscanApi" \
                --constructor-args "$_verify_constructor_args" "$_verify_deployed_address" "$_verify_source_path"
        fi
    fi

    if [[ ${_verify_blockscoutApi:-null} != [nN][uU][lL][lL] ]] ; then
        forge verify-contract --zksync --watch --chain $chainid --verifier blockscout \
            --verifier-url "$_verify_blockscoutApi" --constructor-args "$_verify_constructor_args" \
            "$_verify_deployed_address" "$_verify_source_path"
    fi
}

declare safe_address
safe_address="$(get_config governance.upgradeSafe)"
require_non_null "$safe_address" governance.upgradeSafe
require_address "$safe_address" governance.upgradeSafe
safe_address="$(checksum_address "$safe_address")"
declare -r safe_address

require_code "$safe_address" 'upgrade Safe'

. "$project_root"/sh/common_safe.sh

declare safe_singleton
safe_singleton="$(cast call --rpc-url "$rpc_url" "$safe_address" 'masterCopy()(address)')"
safe_singleton="$(checksum_address "$safe_singleton")"
declare -r safe_singleton

declare safe_version=''
for candidate_safe_version in 'v1.3.0' 'v1.4.1' ; do
    declare candidate_singleton
    candidate_singleton="$(jq -Mr --arg chain "$chain_name" --arg version "$candidate_safe_version" \
        '.[$chain].safe[$version].singleton' < "$project_root"/chain_config.json)"
    if [[ $candidate_singleton != [Nn][Uu][Ll][Ll] ]] ; then
        candidate_singleton="$(checksum_address "$candidate_singleton")"
        if [[ $candidate_singleton = "$safe_singleton" ]] ; then
            safe_version="$candidate_safe_version"
            break
        fi
    fi
done
declare -r safe_version

if [[ -z $safe_version ]] ; then
    die 'The upgrade Safe singleton does not match any configured Safe version'
fi

declare guard_contract
case "$safe_version:$era_vm" in
    'v1.3.0:false' | 'v1.3.0:False' | 'v1.3.0:FALSE')
        require_vanilla_foundry
        guard_contract=ZeroExSettlerDeployerSafeGuardOnePointThree
        ;;
    'v1.4.1:false' | 'v1.4.1:False' | 'v1.4.1:FALSE')
        require_vanilla_foundry
        guard_contract=ZeroExSettlerDeployerSafeGuardOnePointFourPointOne
        ;;
    'v1.3.0:true' | 'v1.3.0:True' | 'v1.3.0:TRUE')
        require_zk_foundry
        guard_contract=ZeroExSettlerDeployerSafeGuardOnePointThreeEraVm
        ;;
    'v1.4.1:true' | 'v1.4.1:True' | 'v1.4.1:TRUE')
        require_zk_foundry
        guard_contract=ZeroExSettlerDeployerSafeGuardOnePointFourPointOneEraVm
        ;;
    *)
        die 'Unsupported Safe version / EraVM combination'
        ;;
esac
declare -r guard_contract

declare safe_toehold
safe_toehold="$(get_safe_config toehold)"
require_non_null "$safe_toehold" "safe.$safe_version.toehold"
require_address "$safe_toehold" "safe.$safe_version.toehold"
safe_toehold="$(checksum_address "$safe_toehold")"
declare -r safe_toehold

declare configured_singleton
configured_singleton="$(get_safe_config singleton)"
require_non_null "$configured_singleton" "safe.$safe_version.singleton"
configured_singleton="$(checksum_address "$configured_singleton")"
declare -r configured_singleton

declare safe_fallback
safe_fallback="$(get_safe_config fallback)"
require_non_null "$safe_fallback" "safe.$safe_version.fallback"
safe_fallback="$(checksum_address "$safe_fallback")"
declare -r safe_fallback

declare safe_multicall
safe_multicall="$(get_safe_config multiCall)"
require_non_null "$safe_multicall" "safe.$safe_version.multiCall"
safe_multicall="$(checksum_address "$safe_multicall")"
declare -r safe_multicall

if [[ $configured_singleton != "$safe_singleton" ]] ; then
    die 'Internal error: configured singleton no longer matches detected singleton'
fi

require_code "$safe_toehold" "Safe $safe_version toehold"
require_code "$configured_singleton" "Safe $safe_version singleton"
require_code "$safe_fallback" "Safe $safe_version fallback handler"
require_code "$safe_multicall" "Safe $safe_version MultiSendCallOnly"

declare toehold_codehash
toehold_codehash="$(code_hash "$safe_toehold")"
declare -r toehold_codehash
if [[ $era_vm = [Ff]alse ]] ; then
    case "$(checksum_address "$safe_toehold")" in
        '0x4e59b44847b379578588920cA78FbF26c0B4956C' | '0x914d7Fec6aaC8cd542e72Bca78B30650d45643d7')
            if [[ $toehold_codehash != 0x2fa86add0aed31f33a762c9d88e807c475bd51d0f52bd0955754b2608f7e4989 ]] ; then
                die 'Configured Safe toehold codehash is unexpected'
            fi
            ;;
    esac
else
    if [[ $safe_toehold != 0xaECDbB0a3B1C6D1Fe1755866e330D82eC81fD4FD ]] ; then
        die 'Configured EraVM Safe toehold is not the supported Safe singleton factory'
    fi
    if [[ $toehold_codehash != 0x6596c8365f1908eef6ca6cd32cd136c7afe63c3eb5156488e0bda67d62b2836c ]] ; then
        die 'Configured EraVM Safe toehold codehash is unexpected'
    fi
fi

declare constructor_args
constructor_args="$(cast abi-encode 'constructor(address)' "$safe_address")"
declare -r constructor_args

declare artifact
declare bytecode
declare initcode
declare deploy_calldata
declare guard_address
declare -a zk_factory_deps=()

if [[ $era_vm = [Tt]rue ]] ; then
    forge build --zksync --zk-compile -o zkout --cache-path zkcache src/deployer/SafeGuard.sol zksrc/SafeGuardWrappers.sol

    artifact="$project_root"/zkout/SafeGuard.sol/"$guard_contract".json
    if [[ ! -f "$artifact" ]] ; then
        die "Missing zkSync SafeGuard artifact: $artifact"
    fi

    bytecode="$(ensure_hex "$(jq -Mr '.bytecode.object' < "$artifact")")"
    declare bytecode_hash
    bytecode_hash="$(ensure_hex "$(jq -Mr '.hash' < "$artifact")")"
    declare -r bytecode_hash
    declare constructor_hash
    constructor_hash="$(cast keccak "$constructor_args")"
    declare -r constructor_hash

    declare guard_address_hash
    guard_address_hash="$(
        cast keccak "$(
            cast concat-hex "$(cast keccak zksyncCreate2)" "$(cast to-uint256 "$safe_toehold")" \
                "$(cast hash-zero)" "$bytecode_hash" "$constructor_hash"
        )"
    )"
    guard_address="$(checksum_address "0x${guard_address_hash:26:40}")"

    deploy_calldata="$(
        cast concat-hex "$(cast hash-zero)" \
            "$(cast calldata 'create2(bytes32,bytes32,bytes)' "$(cast hash-zero)" "$bytecode_hash" "$constructor_args")"
    )"

    zk_factory_deps+=("$bytecode")
    while IFS='' read -r dependency_artifact ; do
        if [[ -z $dependency_artifact ]] ; then
            continue
        fi
        declare dependency_file
        dependency_file="$project_root"/zkout/"${dependency_artifact%%:*}"/"${dependency_artifact##*:}".json
        dependency_file="${dependency_file/src\/deployer\/SafeGuard.sol/SafeGuard.sol}"
        if [[ ! -f "$dependency_file" ]] ; then
            die "Missing zkSync factory dependency artifact: $dependency_file"
        fi
        zk_factory_deps+=("$(ensure_hex "$(jq -Mr '.bytecode.object' < "$dependency_file")")")
    done < <(jq -Mr '.factoryDependenciesUnlinked[]?' < "$artifact")
else
    FOUNDRY_EVM_VERSION=london FOUNDRY_OPTIMIZER_RUNS=200 FOUNDRY_SOLC_VERSION=0.8.25 \
        forge build src/deployer/SafeGuard.sol

    artifact="$project_root"/out/SafeGuard.sol/"$guard_contract".json
    if [[ ! -f "$artifact" ]] ; then
        die "Missing SafeGuard artifact: $artifact"
    fi

    bytecode="$(ensure_hex "$(jq -Mr '.bytecode.object' < "$artifact")")"
    initcode="$(cast concat-hex "$bytecode" "$constructor_args")"
    deploy_calldata="$(cast concat-hex "$(cast hash-zero)" "$initcode")"
    guard_address="$(cast compute-address --salt "$(cast hash-zero)" --init-code "$initcode" "$safe_toehold")"
    guard_address="${guard_address##* }"
    guard_address="$(checksum_address "$guard_address")"
fi

initcode="$(cast concat-hex "$bytecode" "$constructor_args")"
declare -r artifact
declare -r bytecode
declare -r initcode
declare -r deploy_calldata
declare -r guard_address
declare -r -a zk_factory_deps

declare guard_code
guard_code="$(cast code --rpc-url "$rpc_url" "$guard_address")"
declare -r guard_code
declare guard_deployed=false
if [[ $guard_code != 0x && $guard_code != 0x0 ]] ; then
    declare deployed_guard_safe
    deployed_guard_safe="$(cast call --rpc-url "$rpc_url" "$guard_address" 'safe()(address)')"
    deployed_guard_safe="$(checksum_address "$deployed_guard_safe")"
    if [[ $deployed_guard_safe != "$safe_address" ]] ; then
        die "A contract already exists at the predicted guard address $guard_address"
    fi
    guard_deployed=true
fi
declare -r guard_deployed

declare -r guard_slot=0x4a204f620c8c5ccdca3fd54d003badd85ba500436a431f0cbda4f558c93c34c8
declare -r fallback_slot=0x6c9a6c4a39284e37ed1cf53d337577d14212a4870fb976a4366c693b939918d5

declare current_guard
current_guard="$(parse_storage_address "$(cast storage --rpc-url "$rpc_url" "$safe_address" "$guard_slot")")"
declare -r current_guard

declare current_fallback
current_fallback="$(parse_storage_address "$(cast storage --rpc-url "$rpc_url" "$safe_address" "$fallback_slot")")"
declare -r current_fallback

if [[ $current_fallback != "$safe_fallback" ]] ; then
    die "Upgrade Safe fallback handler is $current_fallback, expected $safe_fallback"
fi

declare modules_page
modules_page="$(cast call --rpc-url "$rpc_url" "$safe_address" \
    'getModulesPaginated(address,uint256)(address[],address)' 0x0000000000000000000000000000000000000001 1)"
declare -r modules_page
if [[ $modules_page != *'[]'* ]] ; then
    die 'Upgrade Safe has at least one module installed'
fi

declare -r -i owner_count="${#owners_array[@]}"
if (( owner_count < 4 )) ; then
    die 'Upgrade Safe has fewer than 4 owners'
fi

declare -i threshold
threshold="$(cast call --rpc-url "$rpc_url" "$safe_address" 'getThreshold()(uint256)')"
declare -r -i threshold
if (( threshold < 2 )) ; then
    die 'Upgrade Safe threshold is below 2'
fi
if (( owner_count - threshold < 2 )) ; then
    die 'Upgrade Safe threshold leaves fewer than 2 non-threshold owners'
fi

declare guard_is_owner
guard_is_owner="$(cast call --rpc-url "$rpc_url" "$safe_address" 'isOwner(address)(bool)' "$guard_address")"
declare -r guard_is_owner
if [[ $guard_is_owner != false ]] ; then
    die 'Predicted SafeGuard address is already an owner of the upgrade Safe'
fi

declare -r zero_address="$(cast address-zero)"
case "$safe_version" in
    'v1.3.0')
        if [[ $current_guard != "$guard_address" ]] ; then
            echo 'Safe v1.3.0 guard is not installed. Predicted SafeGuard address:' >&2
            echo "$guard_address"
            exit 0
        fi
        if [[ $guard_deployed = true ]] ; then
            echo 'SafeGuard is already deployed at '"$guard_address" >&2
            exit 0
        fi
        ;;
    'v1.4.1')
        if [[ $guard_deployed = true ]] ; then
            echo 'SafeGuard is already deployed at '"$guard_address" >&2
            exit 0
        fi
        if [[ $current_guard != "$zero_address" ]] ; then
            die "Upgrade Safe already has a guard installed at $current_guard; refusing to deploy into an ambiguous configuration"
        fi
        ;;
esac

declare signer
declare -r standard_gas_payer=0xEf37aD2BACD70119F141140f7B5E46Cd53a65fc4
IFS='' read -p 'What address will pay gas?: ' -e -r -i "$standard_gas_payer" signer
require_address "$signer" signer
signer="$(checksum_address "$signer")"
declare -r signer

. "$project_root"/sh/common_gas.sh

declare -a zk_tx_args=()
declare -a zk_call_args=()
if [[ $era_vm = [Tt]rue ]] ; then
    declare zk_factory_deps_arg
    zk_factory_deps_arg="$(IFS=, ; echo "${zk_factory_deps[*]}")"
    declare -r zk_factory_deps_arg
    zk_tx_args=(--zksync --zk-factory-deps "$zk_factory_deps_arg")
    zk_call_args=(--zksync)
fi
declare -r -a zk_tx_args
declare -r -a zk_call_args

declare -i gas_estimate
gas_estimate="$(
    cast estimate --from "$signer" --rpc-url "$rpc_url" --gas-price $gas_price \
        "${extra_flags[@]}" "${zk_tx_args[@]}" "$safe_toehold" "$deploy_calldata"
)"
declare -r -i gas_estimate

declare -i gas_limit
gas_limit="$(apply_gas_multiplier $gas_estimate)"
declare -r -i gas_limit

declare -r dry_run_private_key=0x0000000000000000000000000000000000000000000000000000000000000001
declare dry_run_sender
dry_run_sender="$(cast wallet address --private-key "$dry_run_private_key")"
declare -r dry_run_sender

declare anvil_pid=''
declare anvil_rpc=''
function cleanup_anvil {
    if [[ -n ${anvil_pid:-} ]] ; then
        kill "$anvil_pid" &>/dev/null || true
        wait "$anvil_pid" &>/dev/null || true
    fi
    anvil_pid=''
    anvil_rpc=''
}
register_exit_cleanup cleanup_anvil

function start_anvil_fork {
    declare -i _start_anvil_attempt
    for ((_start_anvil_attempt=0; _start_anvil_attempt < 10; _start_anvil_attempt++)) ; do
        declare -i _start_anvil_port=$((20000 + RANDOM % 30000))
        anvil_rpc='http://127.0.0.1:'"$_start_anvil_port"
        anvil -q --fork-url "$rpc_url" --chain-id "$chainid" --auto-impersonate --port "$_start_anvil_port" \
            >/tmp/settler-safeguard-anvil."$_start_anvil_port".log 2>&1 &
        anvil_pid=$!

        declare -i _start_anvil_wait
        for ((_start_anvil_wait=0; _start_anvil_wait < 40; _start_anvil_wait++)) ; do
            if cast chain-id --rpc-url "$anvil_rpc" &>/dev/null ; then
                return
            fi
            if ! kill -0 "$anvil_pid" &>/dev/null ; then
                break
            fi
            sleep 0.25
        done

        cleanup_anvil
    done
    die 'Unable to start an anvil fork for the SafeGuard dry run'
}

function start_anvil_zksync_fork {
    if ! hash anvil-zksync &>/dev/null ; then
        die 'anvil-zksync is not installed'
    fi

    declare -r _start_anvil_zksync_protocol_version="${ANVIL_ZKSYNC_PROTOCOL_VERSION:-29}"
    declare -i _start_anvil_attempt
    for ((_start_anvil_attempt=0; _start_anvil_attempt < 10; _start_anvil_attempt++)) ; do
        declare -i _start_anvil_port=$((20000 + RANDOM % 30000))
        anvil_rpc='http://127.0.0.1:'"$_start_anvil_port"
        declare _start_anvil_log=/tmp/settler-safeguard-anvil-zksync."$_start_anvil_port".log
        anvil-zksync --protocol-version "$_start_anvil_zksync_protocol_version" --port "$_start_anvil_port" \
            --chain-id "$chainid" --auto-impersonate --log-file-path "$_start_anvil_log" --cache memory \
            fork --fork-url "$rpc_url" >/tmp/settler-safeguard-anvil-zksync."$_start_anvil_port".stdout.log 2>&1 &
        anvil_pid=$!

        declare -i _start_anvil_wait
        for ((_start_anvil_wait=0; _start_anvil_wait < 80; _start_anvil_wait++)) ; do
            if cast chain-id --rpc-url "$anvil_rpc" &>/dev/null ; then
                declare _fork_safe_singleton
                if _fork_safe_singleton="$(cast call --rpc-url "$anvil_rpc" "$safe_address" 'masterCopy()(address)' 2>/dev/null)" ; then
                    _fork_safe_singleton="$(checksum_address "$_fork_safe_singleton")"
                    if [[ $_fork_safe_singleton = "$safe_singleton" ]] ; then
                        return
                    fi
                fi
            fi
            if ! kill -0 "$anvil_pid" &>/dev/null ; then
                break
            fi
            sleep 0.25
        done

        cleanup_anvil
    done
    die 'Unable to start an anvil-zksync fork for the SafeGuard dry run'
}

function require_receipt_success {
    declare -r _require_receipt_success_receipt="$1"
    declare -r _require_receipt_success_context="$2"
    if [[ $(jq -Mr '.status' <<<"$_require_receipt_success_receipt") != 0x1 ]] ; then
        die "$_require_receipt_success_context"
    fi
}

function fork_set_balance {
    cast rpc --rpc-url "$anvil_rpc" anvil_setBalance "$1" 0x3635c9adc5dea00000 >/dev/null
}

function fork_send_unlocked {
    if [[ $era_vm = [Tt]rue ]] ; then
        cast send --json --unlocked --from "$1" --rpc-url "$anvil_rpc" --gas-price $gas_price \
            --gas-limit $gas_limit --zksync "${@:2}"
    else
        cast send --json --unlocked --from "$1" --rpc-url "$anvil_rpc" --gas-price $gas_price \
            --gas-limit $gas_limit --chain $chainid "${extra_flags[@]}" "${@:2}"
    fi
}

function fork_send_with_private_key {
    if [[ $era_vm = [Tt]rue ]] ; then
        cast send --json --private-key "$dry_run_private_key" --rpc-url "$anvil_rpc" --gas-price $gas_price \
            --gas-limit $gas_limit "${extra_flags[@]}" "${@:1}"
    else
        cast send --json --private-key "$dry_run_private_key" --rpc-url "$anvil_rpc" --gas-price $gas_price \
            --gas-limit $gas_limit --chain $chainid "${extra_flags[@]}" "${@:1}"
    fi
}

function dry_run_safe_set_guard_transaction {
    declare -r _dry_run_set_guard_calldata="$(cast calldata 'setGuard(address)' "$guard_address")"
    declare _dry_run_safe_tx_hash
    _dry_run_safe_tx_hash="$(eip712_hash "$_dry_run_set_guard_calldata" 0 "$safe_address")"
    declare -r _dry_run_safe_tx_hash

    declare -a _dry_run_sorted_owners=()
    declare _dry_run_owner
    while IFS='' read -r _dry_run_owner ; do
        if [[ -n $_dry_run_owner ]] ; then
            _dry_run_sorted_owners+=("$(checksum_address "$_dry_run_owner")")
        fi
    done < <(printf '%s\n' "${owners_array[@]}" | tr '[:upper:]' '[:lower:]' | sort)
    declare -r -a _dry_run_sorted_owners

    declare _dry_run_signatures=0x
    declare -i _dry_run_owner_index
    for ((_dry_run_owner_index=0; _dry_run_owner_index < threshold; _dry_run_owner_index++)) ; do
        _dry_run_owner="${_dry_run_sorted_owners[$_dry_run_owner_index]}"
        fork_set_balance "$_dry_run_owner"

        declare _dry_run_approve_receipt
        _dry_run_approve_receipt="$(fork_send_unlocked "$_dry_run_owner" "$safe_address" 'approveHash(bytes32)' "$_dry_run_safe_tx_hash")"
        require_receipt_success "$_dry_run_approve_receipt" 'SafeGuard dry-run approveHash transaction failed'

        declare -i _dry_run_approved_hash
        _dry_run_approved_hash="$(
            cast call --rpc-url "$anvil_rpc" "$safe_address" 'approvedHashes(address,bytes32)(uint256)' \
                "$_dry_run_owner" "$_dry_run_safe_tx_hash"
        )"
        if (( _dry_run_approved_hash == 0 )) ; then
            die 'SafeGuard dry-run approveHash did not preapprove the Safe transaction hash'
        fi

        _dry_run_signatures="$(cast concat-hex "$_dry_run_signatures" "$(preapproved_signature "$_dry_run_owner")")"
    done
    declare -r _dry_run_signatures

    declare _dry_run_exec_receipt
    if [[ $era_vm = [Tt]rue ]] ; then
        _dry_run_exec_receipt="$(
            fork_send_with_private_key --zksync "$safe_address" "$execTransaction_sig" "$safe_address" 0 "$_dry_run_set_guard_calldata" \
                0 0 0 0 "$(cast address-zero)" "$(cast address-zero)" "$_dry_run_signatures"
        )"
    else
        _dry_run_exec_receipt="$(
            fork_send_unlocked "$signer" "$safe_address" "$execTransaction_sig" "$safe_address" 0 "$_dry_run_set_guard_calldata" \
                0 0 0 0 "$(cast address-zero)" "$(cast address-zero)" "$_dry_run_signatures"
        )"
    fi
    require_receipt_success "$_dry_run_exec_receipt" 'SafeGuard dry-run Safe execTransaction(setGuard) failed'

    declare _dry_run_installed_guard
    _dry_run_installed_guard="$(parse_storage_address "$(cast storage --rpc-url "$anvil_rpc" "$safe_address" "$guard_slot")")"
    declare -r _dry_run_installed_guard
    if [[ $_dry_run_installed_guard != "$guard_address" ]] ; then
        die 'SafeGuard dry-run Safe execTransaction(setGuard) did not set the expected guard address'
    fi
}

function dry_run_evm_deployment {
    start_anvil_fork

    fork_set_balance "$signer"

    declare _dry_run_receipt
    _dry_run_receipt="$(fork_send_unlocked "$signer" "$safe_toehold" "$deploy_calldata")"
    require_receipt_success "$_dry_run_receipt" 'SafeGuard anvil dry-run deployment transaction failed'

    declare _dry_run_code
    _dry_run_code="$(cast code --rpc-url "$anvil_rpc" "$guard_address")"
    declare -r _dry_run_code
    if [[ $_dry_run_code = 0x || $_dry_run_code = 0x0 ]] ; then
        die 'SafeGuard dry-run deployment did not produce code at the predicted address'
    fi

    declare _dry_run_guard_safe
    _dry_run_guard_safe="$(cast call --rpc-url "$anvil_rpc" "$guard_address" 'safe()(address)')"
    _dry_run_guard_safe="$(checksum_address "$_dry_run_guard_safe")"
    declare -r _dry_run_guard_safe
    if [[ $_dry_run_guard_safe != "$safe_address" ]] ; then
        die 'SafeGuard dry-run deployment has the wrong Safe immutable'
    fi

    if [[ $safe_version = 'v1.4.1' ]] ; then
        declare -r _guard_interface_id=0xe6d7a83a
        declare _supports_guard
        _supports_guard="$(cast call --from "$safe_address" --rpc-url "$anvil_rpc" "$guard_address" \
            'supportsInterface(bytes4)(bool)' "$_guard_interface_id")"
        declare -r _supports_guard
        if [[ $_supports_guard != true ]] ; then
            die 'SafeGuard does not report IGuard support when called by the upgrade Safe on the anvil fork'
        fi

        dry_run_safe_set_guard_transaction
    fi

    cleanup_anvil
}

function dry_run_eravm_deployment {
    start_anvil_zksync_fork

    fork_set_balance "$dry_run_sender"

    # Auto-impersonated eth_sendTransaction does not preserve zk factory dependencies in anvil-zksync.
    # The tx sender is not semantically relevant to this CREATE2 deployment.
    declare _dry_run_receipt
    _dry_run_receipt="$(fork_send_with_private_key "${zk_tx_args[@]}" "$safe_toehold" "$deploy_calldata")"
    require_receipt_success "$_dry_run_receipt" 'SafeGuard anvil-zksync dry-run deployment transaction failed'

    declare _dry_run_code
    _dry_run_code="$(cast code --rpc-url "$anvil_rpc" "$guard_address")"
    declare -r _dry_run_code
    if [[ $_dry_run_code = 0x || $_dry_run_code = 0x0 ]] ; then
        die 'SafeGuard anvil-zksync dry-run deployment did not produce code at the predicted address'
    fi

    declare _dry_run_guard_safe
    _dry_run_guard_safe="$(cast call --rpc-url "$anvil_rpc" "$guard_address" 'safe()(address)')"
    _dry_run_guard_safe="$(checksum_address "$_dry_run_guard_safe")"
    declare -r _dry_run_guard_safe
    if [[ $_dry_run_guard_safe != "$safe_address" ]] ; then
        die 'SafeGuard anvil-zksync dry-run deployment has the wrong Safe immutable'
    fi

    if [[ $safe_version = 'v1.4.1' ]] ; then
        declare -r _guard_interface_id=0xe6d7a83a
        declare _supports_guard
        _supports_guard="$(cast call --from "$safe_address" --rpc-url "$anvil_rpc" "$guard_address" \
            'supportsInterface(bytes4)(bool)' "$_guard_interface_id")"
        declare -r _supports_guard
        if [[ $_supports_guard != true ]] ; then
            die 'SafeGuard does not report IGuard support when called by the upgrade Safe on the anvil-zksync fork'
        fi

        dry_run_safe_set_guard_transaction
    fi

    cleanup_anvil
}

if [[ $era_vm = [Ff]alse ]] ; then
    if ! hash anvil &>/dev/null ; then
        die 'anvil is not installed'
    fi
    dry_run_evm_deployment
else
    dry_run_eravm_deployment
fi

echo 'SafeGuard deployment checks passed' >&2
echo 'Chain:        '"$chain_display_name"' ('"$chainid"')' >&2
echo 'Safe version: '"$safe_version" >&2
echo 'Upgrade Safe: '"$safe_address" >&2
echo 'Guard:        '"$guard_address" >&2
echo 'Deployer:     '"$safe_toehold" >&2
echo 'Gas estimate: '"$gas_estimate" >&2
echo 'Gas limit:    '"$gas_limit" >&2

declare -a maybe_broadcast=()
declare submit_rpc
if [[ ${BROADCAST-no} = [Yy]es ]] ; then
    . "$project_root"/sh/common_wallet_type.sh

    maybe_broadcast+=(send --chain $chainid --confirmations 10)
    if [[ $wallet_type = 'frame' ]] ; then
        maybe_broadcast+=(--unlocked)
        submit_rpc='http://127.0.0.1:1248/'
    else
        maybe_broadcast+=("${wallet_args[@]}")
        submit_rpc="$rpc_url"
    fi
else
    echo 'Did not broadcast; set BROADCAST=yes to deploy after reviewing the output above' >&2
    exit 0
fi
declare -r -a maybe_broadcast
declare -r submit_rpc

cast "${maybe_broadcast[@]}" --from "$signer" --rpc-url "$submit_rpc" --gas-price $gas_price \
    --gas-limit $gas_limit "${extra_flags[@]}" "${zk_tx_args[@]}" "$safe_toehold" "$deploy_calldata"

guard_code="$(cast code --rpc-url "$rpc_url" "$guard_address")"
if [[ $guard_code = 0x || $guard_code = 0x0 ]] ; then
    die 'Broadcast transaction completed, but no SafeGuard code exists at the predicted address'
fi

if [[ $safe_version = 'v1.4.1' ]] ; then
    declare deployed_supports_guard
    deployed_supports_guard="$(cast call --from "$safe_address" --rpc-url "$rpc_url" "${zk_call_args[@]}" \
        "$guard_address" 'supportsInterface(bytes4)(bool)' 0xe6d7a83a)"
    declare -r deployed_supports_guard
    if [[ $deployed_supports_guard != true ]] ; then
        die 'Broadcast SafeGuard does not report IGuard support when called by the upgrade Safe'
    fi

    echo 'Deploy complete. The follow-up Safe transaction should call:' >&2
    echo '  to:   '"$safe_address" >&2
    echo '  data: '"$(cast calldata 'setGuard(address)' "$guard_address")" >&2
else
    echo 'Deploy complete. The upgrade Safe guard slot was already set to the deployed guard.' >&2
fi

if [[ $era_vm = [Ff]alse ]] ; then
    verify_contract "$constructor_args" "$guard_address" src/deployer/SafeGuard.sol:"$guard_contract" 0.8.25
else
    verify_zksync_contract "$constructor_args" "$guard_address" src/deployer/SafeGuard.sol:"$guard_contract"
fi
