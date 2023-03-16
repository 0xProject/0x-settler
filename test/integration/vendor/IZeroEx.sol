// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

import {ERC20} from "solmate/src/tokens/ERC20.sol";

interface IZeroEx {
    function sellTokenForTokenToUniswapV3(
        bytes memory encodedPath,
        uint256 sellAmount,
        uint256 minBuyAmount,
        address recipient
    ) external returns (uint256 buyAmount);

    // Identifies the type of subcall.
    enum MultiplexSubcall {
        Invalid,
        RFQ,
        OTC,
        UniswapV2,
        UniswapV3,
        LiquidityProvider,
        TransformERC20,
        BatchSell,
        MultiHopSell
    }

    // Represents a constituent call of a batch sell.
    struct BatchSellSubcall {
        // The function to call.
        MultiplexSubcall id;
        // Amount of input token to sell. If the highest bit is 1,
        // this value represents a proportion of the total
        // `sellAmount` of the batch sell. See `_normalizeSellAmount`
        // for details.
        uint256 sellAmount;
        // ABI-encoded parameters needed to perform the call.
        bytes data;
    }

    function multiplexBatchSellTokenForToken(
        ERC20 inputToken,
        ERC20 outputToken,
        BatchSellSubcall[] calldata calls,
        uint256 sellAmount,
        uint256 minBuyAmount
    ) external returns (uint256 boughtAmount);
}
