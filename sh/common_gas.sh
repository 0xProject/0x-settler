# Common gas price and gas limit utilities

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

declare -i gas_estimate_multiplier
gas_estimate_multiplier="$(get_config gasMultiplierPercent)"
declare -r -i gas_estimate_multiplier

# EIP-7825 gas limit cap (2^24)
declare -r -i eip7825_gas_limit=16777216

declare -r -i tempo_gas_limit=30000000

declare -i transaction_gas_limit=$eip7825_gas_limit
declare transaction_gas_limit_description='EIP-7825 limit'
declare -a maybe_tx_gas_limit=(--enable-tx-gas-limit)
if (( chainid == 4217 )) ; then
    transaction_gas_limit=$tempo_gas_limit
    transaction_gas_limit_description='Tempo gas limit'
    maybe_tx_gas_limit=()
elif (( chainid == 5000 )) || [[ $era_vm = [Tt]rue ]] ; then
    transaction_gas_limit=0
    transaction_gas_limit_description=
    maybe_tx_gas_limit=()
fi
declare -r -i transaction_gas_limit
declare -r transaction_gas_limit_description
declare -r -a maybe_tx_gas_limit

# Apply gas multiplier and check transaction gas limit
# Usage: gas_limit="$(apply_gas_multiplier <gas_estimate>)"
function apply_gas_multiplier {
    declare -i _gas_estimate="$1"
    shift

    if (( transaction_gas_limit > 0 && _gas_estimate > transaction_gas_limit )) ; then
        die "Gas estimate without buffer /already/ exceeds the $transaction_gas_limit_description"
    fi

    declare -i _gas_limit=$((_gas_estimate * gas_estimate_multiplier / 100))

    if (( transaction_gas_limit > 0 && _gas_limit > transaction_gas_limit )) ; then
        declare _gas_limit_keep_going
        IFS='' read -p "Gas limit with multiplier exceeds $transaction_gas_limit_description. Cap gas limit and keep going? [y/N]: " -e -r -i n _gas_limit_keep_going
        declare -r _gas_limit_keep_going
        if [[ "${_gas_limit_keep_going:-n}" != [Yy] ]] ; then
            die '' 'Exiting as requested'
        fi
        _gas_limit=$transaction_gas_limit
    fi

    echo $_gas_limit
}
