// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";

import {SettlerAbstract} from "../SettlerAbstract.sol";

interface INativeV2Router {
    struct WidgetFee {
        address feeRecipient;
        uint256 feeRate;
    }

    struct RFQTQuote {
        /// @notice RFQ pool address or external swap router address
        address pool;
        /// @notice market maker
        address signer;
        /// @notice The recipient of the buyerToken at the end of the trade.
        address recipient;
        /// @notice The token that the trader sells.
        address sellerToken;
        /// @notice The token that the trader buys.
        address buyerToken;
        /// @notice The max amount of sellerToken sold.
        uint256 sellerTokenAmount;
        /// @notice The amount of buyerToken bought when sellerTokenAmount is sold.
        uint256 buyerTokenAmount;
        /// @notice Minimum buyerToken amount received
        uint256 amountOutMinimum;
        /// @notice The Unix timestamp (in seconds) when the quote expires.
        /// @dev This gets checked against block.timestamp.
        uint256 deadlineTimestamp;
        /// @notice Nonces are used to protect against replay.
        uint256 nonce;
        /// @notice Start time for price decay mechanism (Unix timestamp)Add commentMore actions
        uint256 decayStartTime;
        /// @notice Exponent controlling the steepness of decay curve
        uint256 decayExponent;
        /// @notice Maximum allowable slippage in basis points
        uint256 maxSlippageBps;
        /// @notice Unique identifier for the quote.
        /// @dev Generated off-chain via a distributed UUID generator.
        bytes16 quoteId;
        /// @dev  false if this quote is for the 1st hop of a multi-hop or a single-hop, in which case msg.sender is the payer.
        ///       true if this quote is for 2nd or later hop of a multi-hop, in which case router is the payer.
        bool multiHop;
        /// @notice Signature provided by the market maker (EIP-191).
        bytes signature;
        /// @notice Widget fee information
        WidgetFee widgetFee;
        /// @notice Widget fee signature
        bytes widgetFeeSignature;
    }

    /// @notice Execute a Request for Quote (RFQ) trade based on market maker's signed quote
    /// @param quote The RFQ quote containing trade details and signatures
    /// @param actualSellerAmount The actual amount of tokens to be sold, can be different from quote amount within deviation limit
    /// @param actualMinOutputAmount The minimum amount of tokens to be received, overrides quote's amountOutMinimum if provided
    function tradeRFQT(RFQTQuote memory quote, uint256 actualSellerAmount, uint256 actualMinOutputAmount)
        external
        payable;
}

abstract contract NativeV2 is SettlerAbstract {
    using SafeTransferLib for IERC20;
    using UnsafeMath for uint256;

    function sellToNativeV2(address router, uint256 bps, bytes memory tradeData) internal {
        bool isEth;
        IERC20 sellToken;
        assembly ("memory-safe") {
            // tradeData is (RFQTQuote quote, uint256 actualSellerAmount, uint256 actualMinOutputAmount)
            // Take sellToken from quote.sellerToken
            // not checking for dirty bits as it will be checked later on by nativeV2
            sellToken := mload(add(0xe0, tradeData))
            isEth := iszero(sellToken)
        }
        uint256 sellAmount;
        unchecked {
            sellAmount =
                ((isEth ? address(this).balance : sellToken.fastBalanceOf(address(this))) * bps).unsafeDiv(BASIS);
        }
        if (!isEth) {
            sellToken.safeApproveIfBelow(address(router), sellAmount);
        }

        // override actualSellerAmount and call nativeV2
        assembly ("memory-safe") {
            mstore(add(0x40, tradeData), sellAmount)

            // temporarly clobber tradeData length
            let length := mload(tradeData)
            mstore(tradeData, 0x69964e16) // selector for `tradeRFQT((address,address,address,address,address,uint256,uint256,uint256,uint256,uint256,uint256,uint256,uint256,bytes16,bool,bytes,(address,uint256),bytes),uint256,uint256)`
            // `tradeRFQT` doesn't clash with any relevant function of restricted targets so we can skip checking `router`
            if iszero(call(gas(), router, mul(isEth, sellAmount), add(0x1c, tradeData), length, 0x00, 0x00)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0, returndatasize())
                revert(ptr, returndatasize())
            }
            // retored clobbered memory
            mstore(tradeData, length)
        }
    }
}
