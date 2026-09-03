// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {Ternary} from "../utils/Ternary.sol";
import {tmp} from "../utils/512Math.sol";
import {ETH_ADDRESS, BASIS} from "./Constants.sol";

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
        IERC20 token0,
        IERC20 token1,
        uint256 epoch,
        int32 tick,
        uint256 quantity,
        bool isBid
    ) internal {
        // deepstate.fill{value: value}(
        //     IDeepstateV1.FillParams(
        //         token0, token1, epoch, bytes32(uint256(uint32(tick)) << 224 | quantity << 64), isBid, true, false
        //     )
        // );
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(add(0xe0, ptr), 0x00) // fillOrKill
            mstore(add(0xc0, ptr), 0x01) // noRest
            mstore(add(0xa0, ptr), lt(0x00, isBid))
            mstore(add(0x80, ptr), or(shl(0xe0, tick), shl(0x40, quantity)))
            mstore(add(0x60, ptr), epoch)
            mstore(add(0x40, ptr), token1)
            mstore(add(0x2c, ptr), shl(0x60, token0)) // Clears `token1`'s padding.
            mstore(add(0x0c, ptr), 0x5d6222ab000000000000000000000000) // Selector for `fill((address,address,uint256,bytes32,bool,bool,bool))`, with `token0`'s padding.

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
        bool sendNative;
        assembly ("memory-safe") {
            // DeepState uses address(0) for native token
            sellToken := mul(sellToken, lt(0x00, shl(0x60, xor(sellToken, ETH_ADDRESS))))
            buyToken := mul(buyToken, lt(0x00, shl(0x60, xor(buyToken, ETH_ADDRESS))))

            sendNative := iszero(sellToken)
        }

        uint256 sellAmount;
        unchecked {
            if (sendNative) {
                sellAmount = (address(this).balance * ppm).unsafeDiv(BASIS);
            } else {
                sellAmount = (sellToken.fastBalanceOf(address(this)) * ppm).unsafeDiv(BASIS);
                sellToken.safeApproveIfBelow(address(ROBINHOOD_DEEPSTATE), sellAmount);
            }
        }

        bool isBid = sellToken > buyToken;
        (IERC20 token0, IERC20 token1) = isBid.maybeSwap(sellToken, buyToken);

        // Orders are sized in `token0`. A bid spends `token1`, so the sell amount is converted through the
        // reciprocal of the limit price, which bounds the engine's debit by the sell amount. The one wei the
        // engine can add when it partially consumes an ask is absorbed by the caller taking `inversePriceX128`
        // one tick past the limit.
        if (isBid) {
            (, sellAmount) = tmp().omul(sellAmount, inversePriceX128).ishr(128).into();
        }

        ROBINHOOD_DEEPSTATE.fastFill(sendNative.orZero(sellAmount), token0, token1, epoch, tick, sellAmount, isBid);
    }
}
