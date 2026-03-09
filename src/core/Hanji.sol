// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {FastLogic} from "../utils/FastLogic.sol";
import {Ternary} from "../utils/Ternary.sol";
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
    )
        external
        payable
        returns (uint64 order_id, uint128 executed_shares, uint128 executed_value, uint128 aggressive_fee);

    function placeMarketOrderWithTargetValue(
        bool isAsk,
        uint128 target_token_y_value,
        uint72 price,
        uint128 max_commission,
        bool transfer_executed_tokens,
        uint256 expires
    ) external payable returns (uint128 executed_shares, uint128 executed_value, uint128 aggressive_fee);

    function getConfig()
        external
        view
        returns (
            uint256 _scaling_factor_token_x,
            uint256 _scaling_factor_token_y,
            address _token_x,
            address _token_y,
            bool _supports_native_eth,
            bool _is_token_x_weth,
            address _ask_trie,
            address _bid_trie,
            uint64 _admin_commission_rate,
            uint64 _total_aggressive_commission_rate,
            uint64 _total_passive_commission_rate,
            uint64 _passive_order_payout_rate,
            bool _should_invoke_on_trade
        );
}

library FastHanjiPool {
    function placeMarketOrder(
        IHanjiPool pool,
        uint256 sendNativeScaling,
        bool isAsk,
        uint128 quantity,
        uint72 priceLimit
    ) internal returns (uint256 executed) {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(ptr, xor(0xad73d32e, mul(0x58603c62, isAsk)))       // selector
            mstore(add(0x20, ptr), isAsk)
            mstore(add(0x40, ptr), and(0xffffffffffffffffffffffffffffffff, quantity))
            mstore(add(0x60, ptr), and(0xffffffffffffffffff, priceLimit))
            mstore(add(0x80, ptr), 0xffffffffffffffffffffffffffffffff) // max_commission
            mstore(add(0xa0, ptr), 0x01)                               // market_only/transfer_executed_tokens
            mstore(add(0xc0, ptr), sub(isAsk, 0x01))                   // post_only/expires
            mstore(add(0xe0, ptr), 0x01)                               // transfer_executed_tokens/ignored
            mstore(add(0x100, ptr), not(0x00))                         // expires/ignored

            if iszero(call(gas(), pool, mul(sendNativeScaling, quantity), add(0x1c, ptr), 0x104, 0x00, 0x80)) {
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }

            executed := mload(shl(0x06, isAsk))
            executed := sub(executed, mload(0x60))

            mstore(0x40, ptr)
            mstore(0x60, 0x00)
        }
    }

    function getToken(IHanjiPool pool, bool tokenY) internal view returns (IERC20 result) {
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            mstore(0x00, 0xc3f909d4) // IHanjiPool.getConfig.selector
            if iszero(staticcall(gas(), pool, 0x1c, 0x04, 0x00, 0x80)) {
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }

            result := mload(add(0x40, shl(0x05, tokenY)))

            mstore(0x40, ptr)
            mstore(0x60, 0x00)
        }
    }
}

abstract contract Hanji is SettlerAbstract {
    using FastHanjiPool for IHanjiPool;
    using SafeTransferLib for IERC20;
    using UnsafeMath for uint256;
    using FastLogic for bool;
    using Ternary for bool;

    function sellToHanji(
        IERC20 sellToken,
        uint256 bps,
        address pool,
        uint256 sellScalingFactor,
        uint256 buyScalingFactor,
        bool isAsk,
        uint256 priceLimit,
        uint256 minBuyAmount
    ) internal returns (uint256 buyAmount) {
        bool sendNative = sellToken == ETH_ADDRESS;
        uint256 sellAmount;
        unchecked {
            if (sendNative) {
                sellAmount = address(this).balance * bps / BASIS;
            } else {
                sellAmount = sellToken.fastBalanceOf(address(this)) * bps / BASIS;
                sellToken.safeApproveIfBelow(pool, sellAmount);
            }
        }

        uint256 scaledSellAmount = sellAmount.unsafeDiv(sellScalingFactor);

        unchecked {
            buyAmount = IHanjiPool(pool)
                .placeMarketOrder(
                    sendNative.orZero(sellScalingFactor), isAsk, uint128(scaledSellAmount), uint72(priceLimit)
                ) * buyScalingFactor;
        }
        if (buyAmount < minBuyAmount) {
            revertTooMuchSlippage(IHanjiPool(pool).getToken(isAsk), minBuyAmount, buyAmount);
        }
    }
}
