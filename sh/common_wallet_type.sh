declare wallet_type

declare -r saved_wallet_type="$project_root"/config/wallet_type.txt
if [[ -f "$saved_wallet_type" && -r "$saved_wallet_type" ]] ; then
    wallet_type="$(<"$saved_wallet_type")"
else
    PS3='What kind of wallet are you using? '
    select wallet_type in ledger trezor hot frame ; do break ; done

    if [[ ${wallet_type:-unset} = 'unset' ]] ; then
        exit 1
    fi

    echo "$wallet_type" >"$saved_wallet_type"
fi

declare -r wallet_type

declare -a wallet_args
case $wallet_type in
    'ledger')
        wallet_args=(--ledger)
        ;;
    'trezor')
        wallet_args=(--trezor)
        ;;
    'hot')
        wallet_args=(--interactive)
        ;;
    'frame')
        wallet_args=(--unlocked)
        ;;
    *)
        echo 'Unrecognized wallet type: '"$wallet_type" >&2
        exit 1
        ;;
esac

if [[ $wallet_type = 'ledger' ]] ; then
    declare -r saved_wallet_ledger_path="$project_root"/config/ledger_hd_path.txt
    if [[ -f "$saved_wallet_ledger_path" && -r "$saved_wallet_ledger_path" ]] ; then
        wallet_args+=(
            --mnemonic-derivation-path "$(<"$saved_wallet_ledger_path")"
        )
    else
        IFS='' read -r -e -p 'Ledger wallet HD path (BIP32) [default '"m/44'/60'/0'/0"']: '
        if [[ ${REPLY:-unset} = 'unset' ]] ; then
            wallet_args+=(
                --mnemonic-derivation-path "m/44'/60'/0'/0"
            )
            echo "m/44'/60'/0'/0" >"$saved_wallet_ledger_path"
        else
            wallet_args+=(
                --mnemonic-derivation-path "$REPLY"
            )
            echo "$REPLY" >"$saved_wallet_ledger_path"
        fi
    fi
fi
