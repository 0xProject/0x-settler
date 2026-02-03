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

declare -r toehold=0x4e59b44847b379578588920cA78FbF26c0B4956C
declare -r toehold_codehash=0x2fa86add0aed31f33a762c9d88e807c475bd51d0f52bd0955754b2608f7e4989

if [[ "$(cast keccak "$(cast code --rpc-url "$rpc_url" "$toehold")")" != $toehold_codehash ]] ; then
    echo 'The Arachnid deterministic deployment proxy does not exist or is corrupt' >&2
    exit 1
fi

. "$project_root"/sh/common_secrets.sh
decrypt_secrets
declare signer
signer="$(get_secret wrappedNativeStorage deployer)"
declare -r signer

. "$project_root"/sh/common_gas.sh

export FOUNDRY_OPTIMIZER_RUNS=1000000
export FOUNDRY_EVM_VERSION=london
export FOUNDRY_SOLC_VERSION=0.8.28

forge clean
forge build src/CrossChainReceiverFactory.sol

declare -r shim_initcode=0x326df01b1d1c8eef6c6cf71a0b658fbc1815601657fe5b7f60143603803560601c6df01b1d1c8eef6c6cf71a0b658fbc14336ccf9e3c5a263d527f621af382fa17f24f1416602e57fe5b3d54604b57583d55803d3d373d34f03d8159526d6045573dfd5b5260203df35b30ff60901b5952604e3df3
declare -r crosschainfactory_salt=0x0000000000000000000000000000000000000009435af220071616d150499b5f

declare shim_salt
shim_salt="$(cast keccak 'Wrapped Native Token Address')"
declare -r shim_salt

declare crosschainfactory_initcode
crosschainfactory_initcode="$(forge inspect src/CrossChainReceiverFactory.sol:CrossChainReceiverFactory bytecode)"
declare -r crosschainfactory_initcode

declare -r forwarding_multicall_sig='multicall((address,uint8,uint256,bytes)[],uint256)((bool,bytes)[])'
declare -r non_forwarding_multicall_sig='multiSend(bytes)'

declare shim
shim="$(cast concat-hex 0xff "$toehold" "$shim_salt" "$(cast keccak "$shim_initcode")")"
shim="$(cast keccak "$shim")"
shim="${shim:26:40}"
shim="$(cast to-check-sum-address "$shim")"
declare -r shim

declare wnative_storage
wnative_storage="$(cast concat-hex 0xd694 "$shim" 0x01)"
wnative_storage="$(cast keccak "$wnative_storage")"
wnative_storage="${wnative_storage:26:40}"
wnative_storage="$(cast to-check-sum-address "$wnative_storage")"
declare -r wnative_storage

declare non_forwarding_multicall
non_forwarding_multicall="$(get_config safe.multiCall)"
declare -r non_forwarding_multicall

declare deploy_shim_calldata
deploy_shim_calldata="$(cast concat-hex 0x00 "$toehold" "$(cast to-uint256 0)" "$(cast to-uint256 "$(((${#shim_initcode} - 2) / 2 + 32))")" "$(cast concat-hex "$shim_salt" "$shim_initcode")")"
deploy_shim_calldata="$(cast calldata "$non_forwarding_multicall_sig" "$deploy_shim_calldata")"
declare -r deploy_shim_calldata

declare deploy_crosschainfactory_calldata
deploy_crosschainfactory_calldata="$(cast concat-hex 0x00 "$toehold" "$(cast to-uint256 2)" "$(cast to-uint256 "$(((${#crosschainfactory_initcode} - 2) / 2 + 32))")" "$(cast concat-hex "$crosschainfactory_salt" "$crosschainfactory_initcode")")"
deploy_crosschainfactory_calldata="$(cast calldata "$non_forwarding_multicall_sig" "$deploy_crosschainfactory_calldata")"
declare -r deploy_crosschainfactory_calldata

declare forwarding_multicall
forwarding_multicall="$(get_config deployment.forwardingMultiCall)"
declare -r forwarding_multicall

declare wnative
wnative="$(get_config wnative)"
declare -r wnative

declare wnative_storage_initcode
wnative_storage_initcode="$(cast concat-hex 0x7f30ff00000000000000000000 "$wnative" 0x600052596000f3)"
declare -r wnative_storage_initcode

declare -a deploy_calldatas=()
deploy_calldatas+=(
    # target, revert policy, value, data
    "$non_forwarding_multicall" 0 0wei "$deploy_shim_calldata"
    "$shim" 0 0wei "$wnative_storage_initcode"
    "$shim" 0 0wei 0x00000000
    "$wnative_storage" 0 0wei 0x00000000
    "$non_forwarding_multicall" 0 2wei "$deploy_crosschainfactory_calldata"
)

declare deploy_calldata
while (( ${#deploy_calldatas[@]} >= 4 )) ; do
    declare target="${deploy_calldatas[0]}"
    declare -i revert_policy="${deploy_calldatas[1]}"
    declare value="${deploy_calldatas[2]}"
    declare data="${deploy_calldatas[3]}"
    deploy_calldatas=( "${deploy_calldatas[@]:4:$((${#deploy_calldatas[@]}-4))}" )

    if [[ -z ${deploy_calldata-} ]] ; then
        deploy_calldata='['
    else
        deploy_calldata="$deploy_calldata"','
    fi
    deploy_calldata="$deploy_calldata"'('"$target"','"$revert_policy"','"$value"','"$data"')'
done
deploy_calldata="$(cast calldata "$forwarding_multicall_sig" "$deploy_calldata"']' 0)"
declare -r deploy_calldata

declare -i gas_limit
if [[ ${BROADCAST-no} = [Yy]es ]] ; then
    declare -i gas_estimate
    gas_estimate="$(cast estimate --from "$signer" --chain $chainid --value 2wei --rpc-url "$rpc_url" --gas-price $gas_price "${extra_flags[@]}" "$forwarding_multicall" "$deploy_calldata")"
    declare -r -i gas_estimate

    gas_limit="$(apply_gas_multiplier $gas_estimate)"
else
    gas_limit=$eip7825_gas_limit
fi
declare -r -i gas_limit

declare -a maybe_broadcast=()
if [[ ${BROADCAST-no} = [Yy]es ]] ; then
    maybe_broadcast+=(send --chain $chainid --private-key)
    maybe_broadcast+=("$(get_secret wrappedNativeStorage key)")
else
    maybe_broadcast+=(call --trace -vvvv)
fi
declare -r -a maybe_broadcast

cast "${maybe_broadcast[@]}" --from "$signer" --value 2wei --rpc-url "$rpc_url" --gas-price $gas_price --gas-limit $gas_limit "${extra_flags[@]}" "$forwarding_multicall" "$deploy_calldata"

if [[ ${BROADCAST-no} = [Yy]es ]] ; then
    sleep 60

    verify_contract 0x 0x00000000000000304861c3aDfb80dd5ebeC96325 src/CrossChainReceiverFactory.sol:CrossChainReceiverFactory

    echo 'Deployment is complete' >&2
    echo 'Add the following to your chain_config.json' >&2
    echo '"deployment": {' >&2
    echo '	"crossChainFactory": "0x00000000000000304861c3aDfb80dd5ebeC96325"' >&2
    echo '}' >&2
else
    echo 'Did not broadcast; skipping verification' >&2
fi
