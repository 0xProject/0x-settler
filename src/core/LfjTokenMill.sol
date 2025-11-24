// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {Panic} from "../utils/Panic.sol";
import {FastLogic} from "../utils/FastLogic.sol";
import {Ternary} from "../utils/Ternary.sol";
import {revertTooMuchSlippage} from "./SettlerErrors.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";

import {SettlerAbstract} from "../SettlerAbstract.sol";

interface ILfjTmMarket {
    function getSqrtRatiosBounds()
        external
        view
        returns (uint256 sqrtRatioAX96, uint256 sqrtRatioBX96, uint256 sqrtRatioMaxX96);

    // token0
    function getBaseToken() external view returns (address);

    // token1
    function getQuoteToken() external view returns (address);

    function getReserves() external view returns (uint256, uint256);

    function swap(address to, bool zeroForOne, int256 deltaAmount, uint256 sqrtRatioLimitX96)
        external
        returns (int256 amount0, int256 amount1);
}

abstract contract LfjTokenMill is SettlerAbstract {
    using SafeTransferLib for IERC20;
    using Ternary for bool;

    function sellToLfjTokenMill(
        address recipient,
        IERC20 sellToken,
        uint256 bps,
        address pool,
        bool zeroForOne,
        uint256 minBuyAmount
    ) internal returns (uint256 buyAmount) {
        uint256 sellAmount;
        if (bps != 0) {
            sellAmount = sellToken.fastBalanceOf(address(this)) * bps / BASIS;
            sellToken.safeTransfer(pool, sellAmount);
        } else {
            (uint256 reserve0, uint256 reserve1) = ILfjTmMarket(pool).getReserves();
            sellAmount = sellToken.fastBalanceOf(pool) - zeroForOne.ternary(reserve0, reserve1);
        }

        uint256 sqrtRatioLimitX96;
        if (zeroForOne) {
            (sqrtRatioLimitX96,,) = ILfjTmMarket(pool).getSqrtRatiosBounds();
        } else {
            sqrtRatioLimitX96 = 2 ** 127 - 1;
        }
        if (sellAmount != 0) {
            (int256 amount0, int256 amount1) =
                ILfjTmMarket(pool).swap(recipient, zeroForOne, int256(sellAmount), sqrtRatioLimitX96);
            buyAmount = uint256(-zeroForOne.ternary(amount1, amount0));
        }
        if (buyAmount < minBuyAmount) {
            revertTooMuchSlippage(
                zeroForOne ? ILfjTmMarket(pool).getQuoteToken() : ILfjTmMarket(pool).getBaseToken(),
                minBuyAmount,
                buyAmount
            );
        }
    }
}
