// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "forge-std/interfaces/IERC20.sol";
import {SettlerAbstract} from "../SettlerAbstract.sol";
import {TooMuchSlippage} from "./SettlerErrors.sol";
import {FullMath} from "../vendor/FullMath.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";

interface IDodoV2 {
    function sellBase(address to) external returns (uint256 receiveQuoteAmount);
    function sellQuote(address to) external returns (uint256 receiveBaseAmount);

    function _BASE_TOKEN_() external view returns (IERC20);
    function _QUOTE_TOKEN_() external view returns (IERC20);
}

abstract contract DodoV2 is SettlerAbstract {
    using FullMath for uint256;
    using SafeTransferLib for IERC20;

    function sellToDodoV2(
        address recipient,
        IERC20 sellToken,
        uint256 bps,
        IDodoV2 dodo,
        bool quoteForBase,
        uint256 minBuyAmount
    ) internal returns (uint256 buyAmount) {
        if (bps != 0) {
            uint256 sellAmount = sellToken.balanceOf(address(this)).mulDiv(bps, BASIS);
            sellToken.safeTransfer(address(dodo), sellAmount);
        }
        if (quoteForBase) {
            buyAmount = dodo.sellQuote(recipient);
            if (buyAmount < minBuyAmount) {
                revert TooMuchSlippage(dodo._BASE_TOKEN_(), minBuyAmount, buyAmount);
            }
        } else {
            buyAmount = dodo.sellBase(recipient);
            if (buyAmount < minBuyAmount) {
                revert TooMuchSlippage(dodo._QUOTE_TOKEN_(), minBuyAmount, buyAmount);
            }
        }
    }
}
