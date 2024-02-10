// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {Permit2PaymentAbstract} from "./Permit2Payment.sol";
import {InvalidOffset, ConfusedDeputy, InvalidTarget} from "./SettlerErrors.sol";

import {IERC20} from "../IERC20.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {FullMath} from "../vendor/FullMath.sol";
import {Panic} from "../utils/Panic.sol";
import {Revert} from "../utils/Revert.sol";

abstract contract Basic is Permit2PaymentAbstract {
    using SafeTransferLib for IERC20;
    using FullMath for uint256;
    using Revert for bool;

    address internal constant ETH_ADDRESS = 0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE;

    /// @dev Sell to a pool with a generic approval, transferFrom interaction.
    /// offset in the calldata is used to update the sellAmount given a proportion of the sellToken balance
    function basicSellToPool(address pool, IERC20 sellToken, uint256 bips, uint256 offset, bytes memory data)
        internal
    {
        if (isRestrictedTarget(pool)) {
            revert ConfusedDeputy();
        }

        bool success;
        bytes memory returnData;
        uint256 value;
        if (sellToken == IERC20(ETH_ADDRESS)) {
            value = address(this).balance.mulDiv(bips, 10_000);
            if (data.length == 0) {
                if (offset != 0) revert InvalidOffset();
                (success, returnData) = payable(pool).call{value: value}("");
                success.maybeRevert(returnData);
                return;
            } else {
                if ((offset += 32) > data.length) {
                    Panic.panic(Panic.ARRAY_OUT_OF_BOUNDS);
                }
                assembly ("memory-safe") {
                    mstore(add(data, offset), value)
                }
            }
        } else if (address(sellToken) == address(0)) {
            if (offset != 0) revert InvalidOffset();
        } else {
            uint256 amount = sellToken.balanceOf(address(this)).mulDiv(bips, 10_000);
            if ((offset += 32) > data.length) {
                Panic.panic(Panic.ARRAY_OUT_OF_BOUNDS);
            }
            assembly ("memory-safe") {
                mstore(add(data, offset), amount)
            }
            if (address(sellToken) != pool) {
                sellToken.safeApproveIfBelow(pool, amount);
            }
        }
        (success, returnData) = payable(pool).call{value: value}(data);
        success.maybeRevert(returnData);
        // forbid sending data to EOAs
        if (returnData.length == 0 && pool.code.length == 0) revert InvalidTarget();
    }
}
