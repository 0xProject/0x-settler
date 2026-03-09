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

# Apply gas multiplier and check EIP-7825 limit
# Usage: gas_limit="$(apply_gas_multiplier <gas_estimate>)"
function apply_gas_multiplier {
    declare -i _gas_estimate="$1"
    shift

    # Mantle has funky gas rules, exclude it from this logic. EraVm chains similarly price in ergs, not gas.
    if (( _gas_estimate > eip7825_gas_limit )) ; then
        if (( chainid != 5000 )) && [[ $era_vm != [Tt]rue ]] ; then
            echo 'Gas estimate without buffer /already/ exceeds the EIP-7825 limit' >&2
            exit 1
        fi
    fi

    declare -i _gas_limit=$((_gas_estimate * gas_estimate_multiplier / 100))

    if (( _gas_limit > eip7825_gas_limit )) ; then
        if (( chainid != 5000 )) && [[ $era_vm != [Tt]rue ]] ; then
            declare _gas_limit_keep_going
            IFS='' read -p 'Gas limit with multiplier exceeds EIP-7825 limit. Cap gas limit and keep going? [y/N]: ' -e -r -i n _gas_limit_keep_going
            declare -r _gas_limit_keep_going
            if [[ "${_gas_limit_keep_going:-n}" != [Yy] ]] ; then
                echo >&2
                echo 'Exiting as requested' >&2
                exit 1
            fi
            _gas_limit=$eip7825_gas_limit
        fi
    fi

    echo $_gas_limit
}
