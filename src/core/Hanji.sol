// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {revertTooMuchSlippage} from "./SettlerErrors.sol";

import {SettlerAbstract} from "../SettlerAbstract.sol";

interface IHanjiPool {
    function placeOrder(
        bool isAsk,
        uint128 quantity,
        uint72 price,
        uint128 max_commission,
        bool market_only,
        bool post_only,
        bool transfer_executed_tokens,
        uint256 expires
    ) external payable returns (
        uint64 order_id,
        uint128 executed_shares,
        uint128 executed_value,
        uint128 aggressive_fee
    );

    function placeMarketOrderWithTargetValue(
        bool isAsk,
        uint128 target_token_y_value,
        uint72 price,
        uint128 max_commission,
        bool transfer_executed_tokens,
        uint256 expires
    ) external payable returns (
        uint128 executed_shares,
        uint128 executed_value,
        uint128 aggressive_fee
    );
}

library FastHanjiPool {
    function placeMarketOrder(IHanjiPool pool, bool isAsk, uint128 quantity) internal returns (uint256 executed_value) {
        uint256 price; // TODO:
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(ptr, xor(0xad73d32e, mul(0x58603c62, isAsk)))       // selector
            mstore(add(0x20, ptr), isAsk)
            mstore(add(0x40, ptr), and(0xffffffffffffffffffffffffffffffff, quantity))
            mstore(add(0x60, ptr), and(0xffffffffffffffffff, price))
            mstore(add(0x80, ptr), 0xffffffffffffffffffffffffffffffff) // max_commission
            mstore(add(0xa0, ptr), 0x01)                               // market_only/transfer_executed_tokens
            mstore(add(0xc0, ptr), sub(isAsk, 0x01))                   // post_only/expires
            mstore(add(0xe0, ptr), 0x01)                               // transfer_executed_tokens/ignored
            mstore(add(0x100, ptr), not(0x00))                         // expires/ignored

            if iszero(call(gas(), pool, 0x00 /* TODO: handle value */, add(0x1c, ptr), 0x104, 0x00, 0x60)) {
                let ptr_ := mload(0x40)
                returndatacopy(ptr_, 0x00, returndatasize())
                revert(ptr_, returndatasize())
            }

            // TODO: this is probably wrong. which of shares/value is which is undocumented
            // TODO: this is probably wrong. this value may not be inclusive of fees
            executed_value := mload(add(0x20, shl(0x05, isAsk)))

            mstore(0x40, ptr)
        }
    }
}

abstract contract Hanji is SettlerAbstract {
    using FastHanjiPool for IHanjiPool;
    using SafeTransferLib for IERC20;
    using UnsafeMath for uint256;

    function hanjiSellToPool(
        address recipient, // TODO: remove if there's no mechanism for custody optimization
        IERC20 sellToken,
        uint256 bps,
        address pool,
        uint256 scalingFactor,
        bool isAsk,
        uint256 minBuyAmount // TODO: remove if there's no mechanism for custody optimization
    ) internal returns (uint256 buyAmount) {
        // TODO: handle value
        uint256 sellAmount = (sellToken.fastBalanceOf(address(this)) * bps) / 10000;

        uint256 scaledSellAmount = sellAmount.unsafeDiv(scalingFactor);

        sellToken.safeApproveIfBelow(pool, sellAmount);

        unchecked {
            buyAmount = IHanjiPool(pool).placeMarketOrder(isAsk, uint128(scaledSellAmount)) * scalingFactor;
        }
        if (buyAmount < minBuyAmount) {
            revertTooMuchSlippage(IERC20(address(0)) /* TODO: get the buy token */, minBuyAmount, buyAmount);
        }
    }
}
