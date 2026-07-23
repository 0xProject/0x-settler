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

declare safe
safe="$(get_config governance.upgradeSafe)"
declare -r safe

if [[ ${safe:-null} == [nN][uU][lL][lL] ]] ; then
    echo 'governance.upgradeSafe is missing from chain_config.json for chain "'"$chain_name"'"' >&2
    exit 1
fi

declare safe_codehash
if [[ $era_vm = [Tt]rue ]] ; then
    # On EraVM an account's codehash is the versioned bytecode hash recorded by the AccountCodeStorage
    # system contract, not the keccak256 of its code.
    # https://docs.zksync.io/zksync-protocol/contracts/system-contracts#accountcodestorage
    safe_codehash="$(cast call --rpc-url "$rpc_url" 0x0000000000000000000000000000000000008002 'getCodeHash(uint256)(bytes32)' "$safe")"
    case "$safe_codehash" in
        0x0100004124426fb9ebb25e27d670c068e52f9ba631bd383279a188be47e3f86d|\
        0x0100003b6cfa15bd7d1cae1c9c022074524d7785d34859ad0576d8fab4305d4f) ;;
        *)
            echo 'Upgrade Safe ('"$safe"') is not a recognized EraVM Safe proxy (codehash '"$safe_codehash"')' >&2
            exit 1
            ;;
    esac
else
    safe_codehash="$(cast keccak "$(cast code --rpc-url "$rpc_url" "$safe")")"
    case "$safe_codehash" in
        0xaea7d4252f6245f301e540cfbee27d3a88de543af8e49c5c62405d5499fab7e5|\
        0xb89c1b3bdf2cf8827818646bce9a8f6e372885f8c55e5c07acbd307cb133b000|\
        0xd7d408ebcd99b2b70be43e20253d6d92a8ea8fab29bd3be7f55b10032331fb4c) ;;
        *)
            echo 'Upgrade Safe ('"$safe"') is not a recognized Safe proxy (codehash '"$safe_codehash"')' >&2
            exit 1
            ;;
    esac
fi
declare -r safe_codehash

declare onchain_singleton
onchain_singleton="$(cast call --rpc-url "$rpc_url" "$safe" 'masterCopy()(address)')"
declare -r onchain_singleton

declare -a candidate_factories
declare -A singleton_inithash
if [[ $era_vm = [Tt]rue ]] ; then
    candidate_factories=(0xaECDbB0a3B1C6D1Fe1755866e330D82eC81fD4FD)
    singleton_inithash=(
        [ZeroExSettlerDeployerSafeGuardOnePointThreeEraVm]=0x0100080f935a1a562e892e1e71d9a0ca8cd349d19a413e0b7e7172c5e8c83ed1
        [ZeroExSettlerDeployerSafeGuardOnePointFourPointOneEraVm]=0x010006c19437ff25b448f038f7ea0a4c910e0ae9cd8e55f2d199b7916b72eb1e
    )
else
    candidate_factories=(
        0x4e59b44847b379578588920cA78FbF26c0B4956C # Arachnid ("Nick's method")
        0x914d7Fec6aaC8cd542e72Bca78B30650d45643d7 # Safe Singleton Factory
        0xC0DEb853af168215879d284cc8B4d0A645fA9b0E # ERC-7955
        0x0000000000000000000000000000000000000012 # EIP-7997
    )
    singleton_inithash=(
        [ZeroExSettlerDeployerSafeGuardOnePointThree]=0x49f30800a6ac5996a48b80c47ff20f19f8728812498a2a7fe75a14864fab6438
        [ZeroExSettlerDeployerSafeGuardOnePointFourPointOne]=0x3555bd3ee95b1c6605c602740d71efaf200068e0395ccd701ac82ab8e42307bd
    )
fi

function predict_create2 {
    cast create2 --deployer "$1" --salt "$(cast hash-zero)" --init-code-hash "$2"
}

function predict_create2_era_vm {
    if (( ${#1} != 42 || ${#2} != 66 || ${#3} != 66 )) ; then
        echo 'predict_create2_era_vm: argument has the wrong width' >&2
        return 1
    fi
    declare _predict_out
    _predict_out="$(cast keccak "$(cast concat-hex "$(cast keccak zksyncCreate2)" "$(cast to-uint256 "$1")" "$(cast hash-zero)" "$2" "$3")")"
    cast to-check-sum-address "0x${_predict_out:26:40}"
}

declare guard_contract='' factory=''
declare _f _v _predicted_singleton
for _f in "${candidate_factories[@]}" ; do
    for _v in "${!singleton_inithash[@]}" ; do
        if [[ $era_vm = [Tt]rue ]] ; then
            _predicted_singleton="$(predict_create2_era_vm "$_f" "${singleton_inithash[$_v]}" "$(cast keccak 0x)")"
        else
            _predicted_singleton="$(predict_create2 "$_f" "${singleton_inithash[$_v]}")"
        fi
        if [[ $_predicted_singleton == "$onchain_singleton" ]] ; then
            guard_contract="$_v"
            factory="$_f"
            break 2
        fi
    done
done
if [[ -z $guard_contract ]] ; then
    echo 'No supported (factory, Safe version) pair produces the upgrade Safe'"'"'s singleton ('"$onchain_singleton"') on chain "'"$chain_name"'".' >&2
    echo 'Either the Safe uses an unsupported version, or its singleton was deployed by a factory the Guard does not support.' >&2
    exit 1
fi
declare -r guard_contract factory

if [[ $guard_contract == *OnePointThree* ]] ; then
    echo 'Chain "'"$chain_name"'" runs Safe 1.3.0, whose Guard ('"$guard_contract"') cannot be deployed by this script.' >&2
    echo 'The 1.3.0 Guard disables itself at construction unless the Safe already designates it as its guard' >&2
    echo 'It must be created and enabled in one atomic transaction executed by the upgrade Safe' >&2
    exit 1
fi

if [[ $(cast code --rpc-url "$rpc_url" "$factory") == '0x' ]] ; then
    echo 'The CREATE2 factory ('"$factory"') is not deployed on chain "'"$chain_name"'"' >&2
    exit 1
fi

declare signer
IFS='' read -p 'What address will you submit with?: ' -e -r -i 0xEf37aD2BACD70119F141140f7B5E46Cd53a65fc4 signer
declare -r signer

. "$project_root"/sh/common_wallet_type.sh
. "$project_root"/sh/common_gas.sh

# The Guard MUST compile with these exact settings: 
export FOUNDRY_EVM_VERSION=london
export FOUNDRY_OPTIMIZER_RUNS=200

declare constructor_args
constructor_args="$(cast abi-encode 'constructor(address)' "$safe")"
declare -r constructor_args

declare predicted
if [[ $era_vm = [Tt]rue ]] ; then
    # EraVM needs zkSync artifacts so we switch to the zksync aware foundry version
    foundryup-zksync -u foundry-zksync-v0.1.9 || true
    if [[ $(forge --version) != *14afc70e251c89b7e2af6e6ac02e9ac6f095b5cc* ]] ; then
        echo 'Wrong foundry version installed' >&2
        echo 'Run `foundryup-zksync -i foundry-zksync-v0.1.9`' >&2
        exit 1
    fi
    forge clean
    forge build --zksync --zk-compile src/deployer/SafeGuard.sol
    declare art="$project_root/zkout/SafeGuard.sol/$guard_contract.json"
    declare bytecode_hash guard_bytecode
    bytecode_hash="0x$(jq -Mr '.hash' "$art")"
    guard_bytecode="0x$(jq -Mr '.bytecode.object' "$art")"
    declare -r bytecode_hash guard_bytecode
    predicted="$(predict_create2_era_vm "$factory" "$bytecode_hash" "$(cast keccak "$constructor_args")")"
else
    forge clean
    forge build src/deployer/SafeGuard.sol
    declare guard_bytecode initcode
    guard_bytecode="$(forge inspect src/deployer/SafeGuard.sol:"$guard_contract" bytecode)"
    initcode="$(cast concat-hex "$guard_bytecode" "$constructor_args")"
    declare -r guard_bytecode initcode
    predicted="$(predict_create2 "$factory" "$(cast keccak "$initcode")")"
fi
declare -r predicted

echo 'SafeGuard variant : '"$guard_contract" >&2
echo 'Protected Safe    : '"$safe" >&2
echo 'Predicted address : '"$predicted" >&2

if [[ $(cast code --rpc-url "$rpc_url" "$predicted") != '0x' ]] ; then
    echo 'SafeGuard already deployed at '"$predicted"' on chain "'"$chain_name"'". Nothing to do.' >&2
    exit 0
fi

declare -a deploy_args zk_tx_flags=()
if [[ $era_vm = [Tt]rue ]] ; then
    declare _create2_calldata
    _create2_calldata="$(cast calldata 'create2(bytes32,bytes32,bytes)' "$(cast hash-zero)" "$bytecode_hash" "$constructor_args")"
    deploy_args=("$factory" "$(cast concat-hex "$(cast hash-zero)" "$_create2_calldata")")
    zk_tx_flags=(--zksync --zk-factory-deps "$guard_bytecode")
else
    deploy_args=("$factory" "$(cast concat-hex "$(cast hash-zero)" "$initcode")")
fi
declare -r -a deploy_args zk_tx_flags

declare -i gas_limit
if [[ ${BROADCAST-no} = [Yy]es ]] ; then
    declare -i gas_estimate
    gas_estimate="$(cast estimate --from "$signer" --rpc-url "$rpc_url" --gas-price $gas_price --chain $chainid "${extra_flags[@]}" "${zk_tx_flags[@]}" "${deploy_args[@]}")"
    declare -r -i gas_estimate
    gas_limit="$(apply_gas_multiplier $gas_estimate)"
else
    gas_limit=$eip7825_gas_limit
fi
declare -r -i gas_limit

declare -a maybe_broadcast=()
declare submit_rpc
if [[ ${BROADCAST-no} = [Yy]es ]] ; then
    maybe_broadcast+=(send --chain $chainid)
    if [[ $wallet_type = 'frame' ]] ; then
        submit_rpc='http://127.0.0.1:1248'
        maybe_broadcast+=(--unlocked)
    else
        submit_rpc="$rpc_url"
        maybe_broadcast+=("${wallet_args[@]}")
    fi
else
    maybe_broadcast+=(call --trace -vvvv)
    submit_rpc="$rpc_url"
fi
declare -r -a maybe_broadcast
declare -r submit_rpc

cast "${maybe_broadcast[@]}" --from "$signer" --rpc-url "$submit_rpc" --gas-price $gas_price --gas-limit $gas_limit "${extra_flags[@]}" "${zk_tx_flags[@]}" "${deploy_args[@]}"

if [[ ${BROADCAST-no} = [Yy]es ]] ; then
    sleep 60

    verify_contract "$constructor_args" "$predicted" src/deployer/SafeGuard.sol:"$guard_contract" 0.8.25

    echo 'SafeGuard deployed to '"$predicted"' on chain "'"$chain_name"'"' >&2
else
    echo 'Did not broadcast; skipping verification' >&2
fi
