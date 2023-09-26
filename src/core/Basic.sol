// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {ERC20} from "solmate/src/tokens/ERC20.sol";

import {SafeTransferLib} from "../utils/SafeTransferLib.sol";
import {FullMath} from "../utils/FullMath.sol";
import {Panic} from "../utils/Panic.sol";

abstract contract Basic {
    using SafeTransferLib for ERC20;
    using FullMath for uint256;

    address internal constant ETH_ADDRESS = 0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE;

    /// @dev Permit2 address
    address private immutable PERMIT2;

    constructor(address permit2) {
        PERMIT2 = permit2;
    }

    error ConfusedDeputy();

    /// @dev Sell to a pool with a generic approval, transferFrom interaction.
    /// offset in the calldata is used to update the sellAmount given a proportion of the sellToken balance
    function basicSellToPool(address pool, ERC20 sellToken, uint256 bips, uint256 offset, bytes memory data) internal {
        if (pool == PERMIT2) {
            revert ConfusedDeputy();
        }
        if ((offset += 32) > data.length) {
            Panic.panic(Panic.ARRAY_OUT_OF_BOUNDS);
        }

        uint256 value;
        uint256 amount;
        if (sellToken == ERC20(ETH_ADDRESS)) {
            value = amount = address(this).balance.mulDiv(bips, 10_000);
        } else {
            amount = sellToken.balanceOf(address(this)).mulDiv(bips, 10_000);
            if (pool != address(sellToken)) {
                sellToken.safeApproveIfBelow(pool, amount);
            }
        }
        assembly ("memory-safe") {
            mstore(add(data, offset), amount)
        }
        // We omit the EXTCODESIZE check here deliberately. This can be used to send value to EOAs.
        (bool success, bytes memory returnData) = payable(pool).call{value: value}(data);
        if (!success) {
            assembly ("memory-safe") {
                revert(add(0x20, returnData), mload(returnData))
            }
        }
    }
}
