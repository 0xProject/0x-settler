// SPDX-License-Identifier: GPL-2.0-or-later
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";

import {revertTooMuchSlippage} from "./SettlerErrors.sol";

import {SettlerSwapAbstract} from "../SettlerAbstract.sol";

interface IEulerSwap {
    function getAssets() external view returns (IERC20 asset0, IERC20 asset1);

    function getLimits(IERC20 tokenIn, IERC20 tokenOut) external view returns (uint256 limitIn, uint256 limitOut);

    function computeQuote(IERC20 tokenIn, IERC20 tokenOut, uint256 amount, bool exactIn) external view returns (uint256);

    function swap(uint256 amount0Out, uint256 amount1Out, address to, bytes calldata data) external;
}

abstract contract EulerSwap is SettlerSwapAbstract {
    using SafeTransferLib for IERC20;

    function sellToEulerSwap(
        address recipient,
        IERC20 sellToken,
        uint256 bps,
        IEulerSwap pool,
        bool zeroForOne,
        uint256 amountOutMin
    ) internal {
        (IERC20 asset0, IERC20 asset1) = pool.getAssets();
        IERC20 buyToken = zeroForOne ? asset1 : asset0;

        (uint256 inLimit,) = pool.getLimits(sellToken, buyToken);

        uint256 sellAmount;
        if (bps != 0) {
            unchecked {
                sellAmount = sellToken.fastBalanceOf(address(this)) * bps / BASIS;
            }
            // If the sell amount is over the limit, any excess will be retained by Settler and sold
            // to subsequent liquidities in the actions list. If `pool` is the last liquidity, this
            // will almost certainly result in a slippage revert.
            if (sellAmount > inLimit) {
                sellAmount = inLimit;
            }
            sellToken.safeTransfer(address(pool), sellAmount);
        }
        if (sellAmount == 0) {
            sellAmount = sellToken.fastBalanceOf(address(pool));
            // If the sell amount is over the limit, the excess is donated. Obviously, this may
            // result in a slippage revert.
            if (sellAmount > inLimit) {
                sellAmount = inLimit;
            }
        }

        uint256 amountOut = pool.computeQuote(sellToken, buyToken, sellAmount, true);

        if (amountOut < amountOutMin) {
            revertTooMuchSlippage(buyToken, amountOutMin, amountOut);
        }

        if (amountOut != 0) {
            uint256 balanceBefore = buyToken.fastBalanceOf(recipient);
            pool.swap(zeroForOne ? 0 : amountOut, zeroForOne ? amountOut : 0, recipient, "");

            uint256 actualBuyAmount = buyToken.fastBalanceOf(recipient) - balanceBefore;
            if (actualBuyAmount < amountOut) {
                revertTooMuchSlippage(buyToken, amountOut, actualBuyAmount);
            }
        }
    }
}
