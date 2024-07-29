PS3='What kind of wallet are you using? '
declare wallet_type
select wallet_type in ledger trezor hot frame ; do break ; done
declare -r wallet_Type

if [[ ${wallet_type:-unset} = 'unset' ]] ; then
    exit 1
fi

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
    IFS='' read -r -e -p 'Ledger wallet HD path (BIP32) [default '"44'/60'/0'/0"']: '
    if [[ ${REPLY:-unset} = 'unset' ]] ; then
        wallet_args+=(
            --mnemonic-derivation-path "44'/60'/0'/0"
        )
    else
        wallet_args+=(
            --mnemonic-derivation-path "$REPLY"
        )
    fi
fi
