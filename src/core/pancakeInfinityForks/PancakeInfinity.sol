// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {PancakeInfinityBase, PoolKey} from "../PancakeInfinity.sol";
import {BalanceDelta} from "../UniswapV4Types.sol";
import {revertUnknownPoolManagerId} from "../SettlerErrors.sol";

address constant pancakeInfinityVault = 0x238a358808379702088667322f80aC48bAd5e6c4;
address constant pancakeInfinityClManager = 0xa0FfB9c1CE1Fe56963B0321B32E7A0302114058b;
address constant pancakeInfinityBinManager = 0xC697d2898e0D09264376196696c51D7aBbbAA4a9;

abstract contract PancakeInfinity is PancakeInfinityBase {
    function _PANCAKE_INFINITY_VAULT() internal pure override returns (address) {
        return pancakeInfinityVault;
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
            return swapToClManager(
                pancakeInfinityClManager, poolKey, zeroForOne, amountSpecified, sqrtPriceLimitX96, hookData
            );
        } else if (poolManagerId == 1) {
            return swapToBinManager(pancakeInfinityBinManager, poolKey, zeroForOne, amountSpecified, hookData);
        } else {
            revertUnknownPoolManagerId(poolManagerId);
        }
    }
}
