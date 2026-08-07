// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {PancakeInfinityBase, PoolKey} from "../PancakeInfinity.sol";
import {BalanceDelta} from "../UniswapV4Types.sol";
import {revertUnknownPoolManagerId} from "../SettlerErrors.sol";

address constant orvexVault = 0xFe7E25dE55e5cBbEcCcb661F3679F873f72B9b0D;
address constant orvexClManager = 0xd01C774d4A66408326Bc65728Ac5Ae5aAf004032;

abstract contract OrvexCL is PancakeInfinityBase {
    function _PANCAKE_INFINITY_VAULT() internal pure override returns (address) {
        return orvexVault;
    }

    function _dispatchPancakeInfinity(
        uint8 poolManagerId,
        PoolKey memory poolKey,
        bool zeroForOne,
        int256 amountSpecified,
        uint160 sqrtPriceLimitX96,
        bytes calldata hookData
    ) internal override returns (BalanceDelta) {
        if (poolManagerId == 0) {
            return swapToClManager(orvexClManager, poolKey, zeroForOne, amountSpecified, sqrtPriceLimitX96, hookData);
        } else {
            revertUnknownPoolManagerId(poolManagerId);
        }
    }
}
