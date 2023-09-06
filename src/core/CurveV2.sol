// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {ERC20} from "solmate/src/tokens/ERC20.sol";

import {SafeTransferLib} from "../utils/SafeTransferLib.sol";

interface ICurveV2Pool {
    function exchange(uint256 i, uint256 j, uint256 dx, uint256 min_dy) external payable;
    function exchange(uint256 i, uint256 j, uint256 dx, uint256 min_dy, bool use_eth) external payable;
}

abstract contract CurveV2 {
    using SafeTransferLib for ERC20;

    /// @dev Sell a token for another token directly against a curve pool.
    /// @param pool the Curve pool address.
    /// @param sellToken the token to sell to the pool.
    /// @param fromTokenIndex the index of the coin to sell.
    /// @param toTokenIndex the index of the coin to buy.
    /// @param sellAmount amount of sellToken to sell.
    /// @param minBuyAmount Minimum amount of token to buy.
    function sellTokenForTokenToCurve(
        address pool,
        ERC20 sellToken,
        uint256 fromTokenIndex,
        uint256 toTokenIndex,
        uint256 sellAmount,
        uint256 minBuyAmount
    ) internal {
        sellToken.safeApproveIfBelow(pool, type(uint256).max);
        // TODO balanceOf since there is no return amount on Curve
        ICurveV2Pool(pool).exchange(fromTokenIndex, toTokenIndex, sellAmount, minBuyAmount);
    }
}
