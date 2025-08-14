// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {SettlerAbstract} from "../SettlerAbstract.sol";
import {InvalidOffset, revertConfusedDeputy, InvalidTarget} from "./SettlerErrors.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {FullMath} from "../vendor/FullMath.sol";
import {Panic} from "../utils/Panic.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";

abstract contract Basic is SettlerAbstract {
    using UnsafeMath for uint256;
    using SafeTransferLib for address payable;
    using SafeTransferLib for IERC20;
    using FullMath for uint256;

    /// @dev Sell to a pool with a generic approval, transferFrom interaction.
    /// offset in the calldata is used to update the sellAmount given a proportion of the sellToken balance
    function basicSellToPool(IERC20 sellToken, uint256 bps, address pool, uint256 offset, bytes memory data) internal {
        {
            bool condition = _isRestrictedTarget(pool);
            // This check is NOT an exhaustive check. There are many tokens that have alternative
            // allowance-spending methods, including (also nonexhaustively) DAI's `pull`, ERC677 and
            // ERC1363's `transferFromAndCall`, ERC777's `operatorSend`, and LZ OFT's `sendFrom` and
            // `sendAndCall`. We specifically blacklist ERC20's `transferFrom` because it is
            // universally implemented. This check is comparatively cheap and covers many cases that
            // could result in loss of funds. Fundamentally, though, for correct operation, it is
            // forbidden to set allowances on this contract. The fact that this does not cover all
            // cases IS NOT A BUG.
            assembly ("memory-safe") {
                // `0x23b872dd` is the selector for `transferFrom(address,address,uint256)`
                // `transferFrom` requires a calldata length of 0x64 bytes, not 0x44, but some (old)
                // ERC20s don't check `CALLDATASIZE` and implicitly pad `amount` with
                // zeroes. Therefore if `data` is 0x45 bytes or longer, it could result in loss of
                // funds.
                condition :=
                    or(iszero(shl(0xe0, xor(0x23b872dd, mul(lt(0x44, mload(data)), mload(add(0x04, data)))))), condition)
            }
            if (condition) {
                revertConfusedDeputy();
            }
        }

        bool success;
        bytes memory returnData;
        uint256 value;
        if (sellToken == ETH_ADDRESS) {
            unchecked {
                // `bps > BASIS` will result in a revert when we try to send more ETH than we have
                value = (address(this).balance * bps).unsafeDiv(BASIS);
            }
            if (data.length == 0) {
                if (offset != 0) {
                    assembly ("memory-safe") {
                        mstore(0x00, 0x01da1572) // selector for `InvalidOffset()`
                        revert(0x1c, 0x04)
                    }
                }
                payable(pool).safeTransferETH(value);
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
            // `bps != 0` is treated as a GIGO error
            if (offset != 0) {
                assembly ("memory-safe") {
                    mstore(0x00, 0x01da1572) // selector for `InvalidOffset()`
                    revert(0x1c, 0x04)
                }
            }
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
        assembly ("memory-safe") {
            if iszero(call(gas(), pool, value, add(0x20, data), mload(data), 0x00, 0x00)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            if iszero(returndatasize()) {
                if iszero(extcodesize(pool)) {
                    // forbid sending data to EOAs
                    mstore(0x00, 0x82d5d76a) // selector for `InvalidTarget()`
                    revert(0x1c, 0x04)
                }
            }
        }
    }
}
