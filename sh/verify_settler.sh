#!/bin/bash

## POSIX Bash implementation of realpath
## Copied and modified from https://github.com/mkropat/sh-realpath and https://github.com/AsymLabs/realpath-lib/
## Copyright (c) 2014 Michael Kropat - MIT License
## Copyright (c) 2013 Asymmetry Laboratories - MIT License

realpath() {
    _resolve_symlinks "$(_canonicalize "$1")"
}

_directory() {
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

_file() {
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

_resolve_symlinks() {
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

_escape() {
    local out
    out=''
    local -i i
    for ((i=0; i < ${#1}; i+=1)); do
        out+='\'"${1:$i:1}"
    done
    printf '%s\n' "$out"
}

_prepend_context() {
    if [ "$1" = . ]; then
        printf '%s\n' "$2"
    else
        case "$2" in
            /* ) printf '%s\n' "$2" ;;
             * ) printf '%s\n' "$1/$2" ;;
        esac
    fi
}

_assert_no_path_cycles() {
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

_canonicalize() {
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

declare -i chainid
chainid="$(get_config chainId)"
declare -r -i chainid

declare rpc_url
rpc_url="$(get_api_secret rpcUrl)"
declare -r rpc_url
if [[ ${rpc_url:-unset} = 'unset' ]] ; then
    echo '`rpcUrl` is unset in `api_secrets.json` for chain "'"$chain_name"'"' >&2
    exit 1
fi

declare deployer_address
deployer_address="$(get_config deployment.deployer)"
declare -r deployer_address

# calls encoded as operation (always zero) 1 byte
#                  target address          20 bytes
#                  value                   32 bytes
#                  data length             32 bytes
#                  data                    variable
declare -r multisend_sig='multiSend(bytes)'

. "$project_root"/sh/common_deploy_settler.sh

declare -r erc721_ownerof_sig='ownerOf(uint256)(address)'

echo 'Verifying taker-submitted settler...' >&2

declare taker_settler
taker_settler="$(cast call --rpc-url "$rpc_url" "$deployer_address" "$erc721_ownerof_sig" 2)"
declare -r taker_settler
forge verify-contract --watch --chain $chainid --etherscan-api-key "$(get_api_secret etherscanKey)" --verifier-url "$(get_config etherscanApi)" --constructor-args "$constructor_args" "$taker_settler" src/flat/"$chain_display_name"Flat.sol:"$chain_display_name"Settler
if (( chainid != 81457 )) && (( chainid != 59144 )); then # sourcify doesn't support Blast or Linea
    forge verify-contract --watch --chain $chainid --verifier sourcify --constructor-args "$constructor_args" "$taker_settler" src/flat/"$chain_display_name"Flat.sol:"$chain_display_name"Settler
fi

echo 'Verified taker-submitted Settler... verifying metatx Settler...' >&2

declare metatx_settler
metatx_settler="$(cast call --rpc-url "$rpc_url" "$deployer_address" "$erc721_ownerof_sig" 3)"
declare -r metatx_settler
forge verify-contract --watch --chain $chainid --etherscan-api-key "$(get_api_secret etherscanKey)" --verifier-url "$(get_config etherscanApi)" --constructor-args "$constructor_args" "$metatx_settler" src/flat/"$chain_display_name"Flat.sol:"$chain_display_name"SettlerMetaTxn
if (( chainid != 81457 )) && (( chainid != 59144 )) ; then # sourcify doesn't support Blast or Linea
    forge verify-contract --watch --chain $chainid --verifier sourcify --constructor-args "$constructor_args" "$metatx_settler" src/flat/"$chain_display_name"Flat.sol:"$chain_display_name"SettlerMetaTxn
fi

echo 'Verified metatx Settler. All done!' >&2
