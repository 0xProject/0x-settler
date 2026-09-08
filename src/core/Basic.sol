// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {SettlerAbstract} from "../SettlerAbstract.sol";
import {InvalidOffset, revertConfusedDeputy, InvalidTarget} from "./SettlerErrors.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import "./Constants.sol" as Constants;
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
    function basicSellToPool(IERC20 sellToken, uint256 ppm, address pool, uint256 offset, bytes memory data) internal {
        if (_isRestrictedTarget(pool)) {
            revertConfusedDeputy();
        }

        bool success;
        bytes memory returnData;
        uint256 value;
        if (address(sellToken) == Constants.ETH_ADDRESS) {
            unchecked {
                value = (address(this).balance * ppm).unsafeDiv(Constants.BASIS);
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
            // TODO: check for zero `ppm`
            if (offset != 0) revert InvalidOffset();
        } else {
            // We treat `ppm > Constants.BASIS` as a GIGO error
            uint256 amount = tmp().omul(sellToken.fastBalanceOf(address(this)), ppm).unsafeDiv(Constants.BASIS);

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
