// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {Ternary} from "../utils/Ternary.sol";
import {tmp} from "../utils/512Math.sol";
import "./Constants.sol" as Constants;

import {SettlerSwapAbstract} from "../SettlerAbstract.sol";

interface IDeepstateV1 {
    /// @param token0 Lower address of the pair. Native ETH is `address(0)`. Asks sell it; bids buy it.
    /// @param token1 Higher address of the pair. Bids pay it; asks receive it.
    /// @param epoch Book epoch. The book id is `keccak256(token0, token1, epoch)`.
    /// @param order `int32 tick << 224 | uint160 token0Quantity << 64`. The low 64 bits must be clear.
    /// @param noRest Discard unmatched quantity instead of resting it as maker liquidity.
    /// @param fillOrKill Revert unless the entire quantity matches.
    struct FillParams {
        address token0;
        address token1;
        uint256 epoch;
        bytes32 order;
        bool isBid;
        bool noRest;
        bool fillOrKill;
    }

    function fill(FillParams calldata params) external payable returns (bytes32 restingOrder);
}

IDeepstateV1 constant ROBINHOOD_DEEPSTATE = IDeepstateV1(0x6cf19308C22FC82ea620Fa0B3E94948d20f27B96);

library FastDeepstate {
    /// Unmatched quantity is never rested. A resting order would be owned by this contract, which has no
    /// way to cancel it, so the collateral would be lost.
    function fastFill(
        IDeepstateV1 deepstate,
        uint256 value,
        address token0,
        address token1,
        uint256 epoch,
        int32 tick,
        uint256 quantity,
        bool isBid
    ) internal {
        // Manually ABI-encode the call to avoid allocating and copying a `FillParams` struct. Equivalent to:
        //     deepstate.fill{value: value}(
        //         IDeepstateV1.FillParams(token0, token1, epoch, bytes32(uint256(uint32(tick)) << 224 | quantity << 64), isBid, true, false)
        //     );
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
    using UnsafeMath for uint256;
    using Ternary for bool;
    using FastDeepstate for IDeepstateV1;

    constructor() {
        assert(address(ROBINHOOD_DEEPSTATE).code.length > 0 || block.chainid == 31337);
    }

    /// Deepstate pays the caller directly, so the proceeds land in this contract for later actions to
    /// forward. Any quantity the book cannot match stays here as `sellToken` for the same reason.
    function sellToDeepstate(
        IERC20 sellToken,
        uint256 ppm,
        IERC20 buyToken,
        uint256 epoch,
        int32 tick,
        uint256 inversePriceX128
    ) internal {
        bool sendNative = address(sellToken) == Constants.ETH_ADDRESS;
        uint256 sellAmount;
        unchecked {
            if (sendNative) {
                sellAmount = (address(this).balance * ppm).unsafeDiv(Constants.BASIS);
            } else {
                sellAmount = (sellToken.fastBalanceOf(address(this)) * ppm).unsafeDiv(Constants.BASIS);
                sellToken.safeApproveIfBelow(address(ROBINHOOD_DEEPSTATE), sellAmount);
            }
        }

        // Deepstate designates native ETH as `address(0)`, so it always sorts as `token0`.
        address sellAsset = sendNative.ternary(address(0), address(sellToken));
        address buyAsset = (address(buyToken) == Constants.ETH_ADDRESS).ternary(address(0), address(buyToken));
        bool isBid = sellAsset > buyAsset;
        (address token0, address token1) = isBid.maybeSwap(sellAsset, buyAsset);

        // Orders are sized in `token0`. A bid spends `token1`, so the sell amount is converted through the
        // caller's price. Rounding down keeps the engine's debit within the sell amount; the engine's own
        // per-order rounding is absorbed by the caller's choice of `tick`.
        uint256 quantity = sellAmount;
        if (isBid) {
            (uint256 hi, uint256 lo) = tmp().omul(sellAmount, inversePriceX128).into();
            quantity = (hi << 128) | (lo >> 128);
        }

        ROBINHOOD_DEEPSTATE.fastFill(sendNative.orZero(sellAmount), token0, token1, epoch, tick, quantity, isBid);
    }
}
