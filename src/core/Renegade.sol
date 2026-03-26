// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SettlerAbstract} from "../SettlerAbstract.sol";
import {revertTooMuchSlippage} from "./SettlerErrors.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";

// selector for `sponsorMalleableAtomicMatchSettleWithRefundOptions(uint256,uint256,address,bytes,bytes,bytes,bytes,address,uint256,bool,uint256,bytes)`
uint32 constant ARBITRUM_SELECTOR = 0x0f977971;
// selector for `sponsorMalleableAtomicMatchSettle(uint256,uint256,address,(((uint256,uint256,uint256)),(uint256,uint256,uint256)),((address,address,(uint256),uint256,uint256,uint8),((uint256),(uint256)),((uint256),(uint256)),uint256[],address),(((uint256,uint256)[5],(uint256,uint256),(uint256,uint256)[5],(uint256,uint256),(uint256,uint256),uint256[5],uint256[4],uint256),((uint256,uint256)[5],(uint256,uint256),(uint256,uint256)[5],(uint256,uint256),(uint256,uint256),uint256[5],uint256[4],uint256),((uint256,uint256)[5],(uint256,uint256),(uint256,uint256)[5],(uint256,uint256),(uint256,uint256),uint256[5],uint256[4],uint256)),(((uint256,uint256),(uint256,uint256)),((uint256,uint256),(uint256,uint256))),address,bool,uint256,uint256,bytes)`
uint32 constant BASE_SELECTOR = 0x322ef840;

abstract contract Renegade is SettlerAbstract {
    using SafeTransferLib for IERC20;
    using UnsafeMath for uint256;

    constructor() {
        uint32 selector = _renegadeSelector();
        assert(
            (block.chainid == 42161 && selector == ARBITRUM_SELECTOR)
                || (block.chainid == 8453 && selector == BASE_SELECTOR) || block.chainid == 31337
        );
    }

    function _renegadeSelector() internal pure virtual returns (uint32);

    /// @dev Extracts buyToken (quoteMint or baseMint) from GasSponsor calldata.
    /// Base: standard ABI encoding; quoteMint @ data+0x1080, baseMint @ data+0x10a0.
    /// Arbitrum: packed 20-byte addresses in statement blob; offset pointer @ data+0xa0.
    /// baseForQuote=true -> buyToken=quoteMint, else baseMint.
    function _extractBuyToken(bytes memory data, bool baseForQuote) internal pure returns (IERC20 buyToken) {
        uint32 selector = _renegadeSelector();
        assembly ("memory-safe") {
            switch selector
            case 0x322ef840 {
                // Base: quoteMint @ data+0x1080, baseMint @ data+0x10a0
                buyToken := mload(add(data, add(0x1080, shl(0x05, iszero(baseForQuote)))))
            }
            case 0x0f977971 {
                // Arbitrum: packed 20B addrs in statement blob (offset ptr @ data+0xa0)
                let stmtOffset := mload(add(0xa0, data))
                buyToken := shr(0x60, mload(add(data, add(mul(0x14, iszero(baseForQuote)), add(0x40, stmtOffset)))))
            }
        }
    }

    /// @param baseForQuote True if selling base for quote.
    function sellToRenegade(
        address target,
        IERC20 sellToken,
        bool baseForQuote,
        bytes memory data,
        uint256 minBuyAmount
    ) internal returns (uint256 buyAmount) {
        uint256 newSellAmount;
        uint256 value;
        if (sellToken == ETH_ADDRESS) {
            value = address(this).balance;
            newSellAmount = value;
        } else {
            newSellAmount = sellToken.fastBalanceOf(address(this));
            sellToken.safeApproveIfBelow(address(target), newSellAmount);
        }

        // word 0: quoteAmount, word 1: baseAmount
        uint256 originalQuoteAmount;
        uint256 originalBaseAmount;
        assembly ("memory-safe") {
            originalQuoteAmount := mload(add(0x20, data))
            originalBaseAmount := mload(add(0x40, data))
        }

        uint256 newQuoteAmount;
        uint256 newBaseAmount;
        if (baseForQuote) {
            newBaseAmount = newSellAmount;
            unchecked {
                newQuoteAmount = (originalQuoteAmount * newBaseAmount).unsafeDiv(originalBaseAmount);
            }
            buyAmount = newQuoteAmount;
        } else {
            newQuoteAmount = newSellAmount;
            unchecked {
                newBaseAmount = (originalBaseAmount * newQuoteAmount).unsafeDiv(originalQuoteAmount);
            }
            buyAmount = newBaseAmount;
        }

        if (buyAmount < minBuyAmount) {
            revertTooMuchSlippage(_extractBuyToken(data, baseForQuote), minBuyAmount, buyAmount);
        }

        uint32 selector = _renegadeSelector();
        assembly ("memory-safe") {
            // override quoteAmount and baseAmount
            mstore(add(0x20, data), newQuoteAmount)
            mstore(add(0x40, data), newBaseAmount)

            let len := mload(data)
            // temporarily clobber `data` size memory area
            mstore(data, selector)
            // Allowed selectors don't clash with any relevant function of restricted targets so we can skip checking `target`
            if iszero(call(gas(), target, value, add(0x1c, data), add(0x04, len), 0x00, 0x00)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            // restore clobbered memory
            mstore(data, len)
        }
    }
}
