// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {SettlerSwapAbstract} from "../SettlerAbstract.sol";
import {IDeepstateV1} from "../interfaces/IDeepstateV1.sol";
import {tmp} from "../utils/512Math.sol";
import {FastLogic} from "../utils/FastLogic.sol";
import {Ternary} from "../utils/Ternary.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {revertInvalidDeepstateRoute, revertNonStandardDeepstateToken} from "./SettlerErrors.sol";
import "./Constants.sol" as Constants;

IDeepstateV1 constant ROBINHOOD_DEEPSTATE = IDeepstateV1(0x6cf19308C22FC82ea620Fa0B3E94948d20f27B96);

library FastDeepstate {
    function fastFill(
        IDeepstateV1 deepstate,
        uint256 value,
        address token0,
        address token1,
        uint256 epoch,
        int32 tick,
        uint160 quantity,
        bool isBid
    ) internal {
        // Manual encoding avoids allocating and copying a struct. Equivalent Solidity:
        // deepstate.fill{value: value}(IDeepstateV1.FillParams({token0: token0, token1: token1, epoch: epoch,
        //     order: bytes32((uint256(uint32(tick)) << 224) | (uint256(quantity) << 64)),
        //     isBid: isBid, noRest: true, fillOrKill: false}));
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(ptr, 0x5d6222ab) // selector for `fill((address,address,uint256,bytes32,bool,bool,bool))`
            mstore(add(0x20, ptr), and(0xffffffffffffffffffffffffffffffffffffffff, token0))
            mstore(add(0x40, ptr), and(0xffffffffffffffffffffffffffffffffffffffff, token1))
            mstore(add(0x60, ptr), epoch)
            mstore(add(0x80, ptr), or(shl(0xe0, tick), shl(0x40, quantity)))
            mstore(add(0xa0, ptr), lt(0x00, isBid))
            mstore(add(0xc0, ptr), 0x01) // noRest
            mstore(add(0xe0, ptr), 0x00) // fillOrKill

            if iszero(call(gas(), deepstate, value, add(0x1c, ptr), 0xe4, 0x00, 0x00)) {
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
        }
    }
}

abstract contract Deepstate is SettlerSwapAbstract {
    using SafeTransferLib for IERC20;
    using FastLogic for bool;
    using Ternary for bool;
    using UnsafeMath for uint256;
    using FastDeepstate for IDeepstateV1;

    constructor() {
        assert(address(ROBINHOOD_DEEPSTATE).code.length > 0 || block.chainid == 31337);
    }

    function _isRestrictedTarget(address target) internal view virtual override returns (bool) {
        return (target == address(ROBINHOOD_DEEPSTATE)).or(super._isRestrictedTarget(target));
    }

    function sellToDeepstate(
        IERC20 sellToken,
        uint256 ppm,
        IERC20 buyToken,
        uint256 epoch,
        int32 tick,
        uint256 inversePriceX128
    ) internal {
        address sellAsset = _deepstateAsset(sellToken);
        address buyAsset = _deepstateAsset(buyToken);
        if (sellAsset == buyAsset) revertInvalidDeepstateRoute();

        bool sendNative = address(sellToken) == Constants.ETH_ADDRESS;
        uint256 balanceBefore = sendNative ? address(this).balance : sellToken.fastBalanceOf(address(this));
        uint256 maxSellAmount = tmp().omul(balanceBefore, ppm).unsafeDiv(Constants.BASIS);

        bool isBid = sellAsset > buyAsset;
        (address token0, address token1) = isBid.maybeSwap(sellAsset, buyAsset);
        uint160 quantity = _deepstateQuantity(maxSellAmount, inversePriceX128, isBid);

        if (sendNative) {
            ROBINHOOD_DEEPSTATE.fastFill(maxSellAmount, token0, token1, epoch, tick, quantity, isBid);
            if (address(this).balance > balanceBefore) revertNonStandardDeepstateToken(sellToken);
        } else {
            uint256 engineBalanceBefore = sellToken.fastBalanceOf(address(ROBINHOOD_DEEPSTATE));

            sellToken.safeApprove(address(ROBINHOOD_DEEPSTATE), 0);
            sellToken.safeApprove(address(ROBINHOOD_DEEPSTATE), maxSellAmount);
            ROBINHOOD_DEEPSTATE.fastFill(0, token0, token1, epoch, tick, quantity, isBid);
            sellToken.safeApprove(address(ROBINHOOD_DEEPSTATE), 0);

            uint256 balanceAfter = sellToken.fastBalanceOf(address(this));
            uint256 engineBalanceAfter = sellToken.fastBalanceOf(address(ROBINHOOD_DEEPSTATE));
            if (balanceAfter > balanceBefore || engineBalanceAfter < engineBalanceBefore) {
                revertNonStandardDeepstateToken(sellToken);
            }
            unchecked {
                if (balanceBefore - balanceAfter > maxSellAmount) revertNonStandardDeepstateToken(sellToken);
                if (engineBalanceAfter - engineBalanceBefore != balanceBefore - balanceAfter) {
                    revertNonStandardDeepstateToken(sellToken);
                }
            }
        }
    }

    function _deepstateQuantity(uint256 sellAmount, uint256 inversePriceX128, bool isBid)
        private
        pure
        returns (uint160 quantity)
    {
        uint256 amount = sellAmount;
        if (isBid) {
            // Deepstate order quantities are token0-denominated. Rounding the tick's Q128 reciprocal down
            // keeps a bid within its token1 budget; the exact temporary allowance is an independent hard cap.
            (uint256 hi, uint256 lo) = tmp().omul(sellAmount, inversePriceX128).into();
            if (hi > type(uint32).max) return type(uint160).max;
            amount = (hi << 128) | (lo >> 128);
        }
        if (amount > type(uint160).max) return type(uint160).max;
        // `amount` is now bounded to the full `uint160` range.
        // forge-lint: disable-next-line(unsafe-typecast)
        quantity = uint160(amount);
    }

    function _deepstateAsset(IERC20 token) private pure returns (address asset) {
        asset = address(token);
        if (asset == Constants.ETH_ADDRESS) return address(0);
        if (asset == address(0)) revertInvalidDeepstateRoute();
    }
}
