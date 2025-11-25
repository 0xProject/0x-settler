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

    function getCurrentSqrtRatio() external view returns (uint256);

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
        // If we haven't custody-optimized, transfer to the pool
        if (bps != 0) {
            sellToken.safeTransfer(pool, sellToken.fastBalanceOf(address(this)) * bps / BASIS);
        }

        // Compute the actual sell amount, after accounting for any potential
        // transfer tax
        uint256 sellAmount;
        {
            (uint256 reserve0, uint256 reserve1) = ILfjTmMarket(pool).getReserves();
            sellAmount = sellToken.fastBalanceOf(pool) - zeroForOne.ternary(reserve0, reserve1);
        }

        // Set the price limits to the maximum value; we don't care to cap them
        // because unlike a concentracted liquidity constant product AMM, there
        // is only one tick that can be crossed.
        uint256 sqrtRatioLimitX96;
        if (zeroForOne) {
            (sqrtRatioLimitX96,,) = ILfjTmMarket(pool).getSqrtRatiosBounds();
        } else {
            sqrtRatioLimitX96 = 2 ** 127 - 1;
        }

        // Perform the swap
        if (sellAmount != 0) {
            (int256 amount0, int256 amount1) =
                ILfjTmMarket(pool).swap(recipient, zeroForOne, int256(sellAmount), sqrtRatioLimitX96);
            buyAmount = uint256(-zeroForOne.ternary(amount1, amount0));
        }

        // Check slippage
        if (buyAmount < minBuyAmount) {
            revertTooMuchSlippage(
                IERC20(zeroForOne ? ILfjTmMarket(pool).getQuoteToken() : ILfjTmMarket(pool).getBaseToken()),
                minBuyAmount,
                buyAmount
            );
        }
    }
}
