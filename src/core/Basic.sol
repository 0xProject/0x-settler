// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {SettlerAbstract} from "../SettlerAbstract.sol";
import {InvalidOffset, ConfusedDeputy, InvalidTarget} from "./SettlerErrors.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {FullMath} from "../vendor/FullMath.sol";
import {Panic} from "../utils/Panic.sol";
import {Revert} from "../utils/Revert.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";

abstract contract Basic is SettlerAbstract {
    using UnsafeMath for uint256;
    using SafeTransferLib for IERC20;
    using FullMath for uint256;
    using Revert for bool;

    /// @dev Sell to a pool with a generic approval, transferFrom interaction.
    /// offset in the calldata is used to update the sellAmount given a proportion of the sellToken balance
    function basicSellToPool(IERC20 sellToken, uint256 bps, address pool, uint256 offset, bytes memory data) internal {
        if (_isRestrictedTarget(pool)) {
            assembly ("memory-safe") {
                mstore(0x00, 0xe758b8d5) // selector for `ConfusedDeputy()`
                revert(0x1c, 0x04)
            }
        }

        bool success;
        bytes memory returnData;
        uint256 value;
        if (sellToken == ETH_ADDRESS) {
            unchecked {
                value = (address(this).balance * bps).unsafeDiv(BASIS);
            }
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
            // TODO: check for zero `bps`
            if (offset != 0) revert InvalidOffset();
        } else {
            uint256 amount = sellToken.fastBalanceOf(address(this)).mulDiv(bps, BASIS);
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
