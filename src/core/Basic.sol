// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {SettlerAbstract} from "../SettlerAbstract.sol";
import {InvalidOffset, revertConfusedDeputy, InvalidTarget} from "./SettlerErrors.sol";

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
            revertConfusedDeputy();
        }
        {
            // This check is NOT an exhaustive check. There are many tokens that have alternative
            // allowance-spending methods, including (also nonexhaustively) DAI's `pull`, ERC677 and
            // ERC1363's `transferFromAndCall`, ERC777's `operatorSend`, and LZ OFT's `sendFrom` and
            // `sendAndCall`. We specifically blacklist ERC20's `transferFrom` because it is
            // universally implemented. This check is comparatively cheap and covers many cases that
            // could result in loss of funds. Fundamentally, though, for correct operation, it is
            // forbidden to set allowances on this contract. The fact that this does not cover all
            // cases IS NOT A BUG.
            uint256 selector;
            assembly ("memory-safe") {
                selector := mul(lt(0x00, mload(data)), and(0xffffffff, mload(add(0x04, data))))
            }
            if (selector == uint32(IERC20.transferFrom.selector)) {
                revertConfusedDeputy();
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
            // We treat `bps > BASIS` as a GIGO error
            uint256 amount = sellToken.fastBalanceOf(address(this)).unsafeMulDiv(bps, BASIS);

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
