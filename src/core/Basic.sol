// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {SettlerAbstract} from "../SettlerAbstract.sol";
import {InvalidOffset, revertConfusedDeputy, InvalidTarget} from "./SettlerErrors.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {Panic} from "../utils/Panic.sol";
import {Revert} from "../utils/Revert.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {tmp} from "../utils/512Math.sol";

abstract contract Basic is SettlerAbstract {
    using UnsafeMath for uint256;
    using SafeTransferLib for IERC20;
    using Revert for bool;

    /// @dev Sell to a pool with a generic approval, transferFrom interaction.
    /// offset in the calldata is used to update the sellAmount given a proportion of the sellToken balance
    /// high 128 bits of offset can optionally contain a min-out calldata offset to scale
    function basicSellToPool(IERC20 sellToken, uint256 bps, address pool, uint256 offset, bytes memory data) internal {
        if (_isRestrictedTarget(pool)) {
            revertConfusedDeputy();
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
            // We treat `bps > BASIS` as a GIGO error
            uint256 amount = tmp().omul(sellToken.fastBalanceOf(address(this)), bps).unsafeDiv(BASIS);

            uint256 minOffset = offset >> 128;
            offset = uint256(uint128(offset));
            uint256 amountSlot = offset + 32;
            if (amountSlot > data.length) {
                Panic.panic(Panic.ARRAY_OUT_OF_BOUNDS);
            }
            if (minOffset != 0) {
                uint256 minSlot = minOffset + 32;
                if (minSlot > data.length) {
                    Panic.panic(Panic.ARRAY_OUT_OF_BOUNDS);
                }
                uint256 placeholder;
                uint256 encodedMin;
                assembly ("memory-safe") {
                    placeholder := mload(add(data, amountSlot))
                    encodedMin := mload(add(data, minSlot))
                }
                // reject exact-out
                if (placeholder >> 255 != 0) revert InvalidOffset();
                if (placeholder != 0 && amount < placeholder) {
                    uint256 newMin = tmp().omul(encodedMin, amount).unsafeDiv(placeholder);
                    assembly ("memory-safe") {
                        mstore(add(data, minSlot), newMin)
                    }
                }
            }
            assembly ("memory-safe") {
                mstore(add(data, amountSlot), amount)
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
