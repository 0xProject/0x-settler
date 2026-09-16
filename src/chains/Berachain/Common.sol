// SPDX-License-Identifier: MIT
pragma solidity =0.8.34;

import {SettlerBase} from "../../SettlerBase.sol";
import {FreeMemory} from "../../utils/FreeMemory.sol";

import {revertUnknownForkId} from "../../core/SettlerErrors.sol";

import {kodiakV3Factory, kodiakV3InitHash, kodiakV3ForkId} from "../../core/univ3forks/KodiakV3.sol";
import {IUniswapV3Callback} from "../../core/univ3forks/UniswapV3.sol";
import {bullaFactory, bullaForkId} from "../../core/univ3forks/Bulla.sol";
import {algebraV4InitHash, IAlgebraCallback} from "../../core/univ3forks/Algebra.sol";

abstract contract BerachainMixin is FreeMemory, SettlerBase {
    constructor() {
        assert(block.chainid == 80094 || block.chainid == 31337);
    }

    function _uniV3ForkInfo(uint8 forkId)
        internal
        pure
        override
        returns (address factory, bytes32 initHash, uint32 callbackSelector)
    {
        if (forkId == kodiakV3ForkId) {
            factory = kodiakV3Factory;
            initHash = kodiakV3InitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else if (forkId == bullaForkId) {
            factory = bullaFactory;
            initHash = algebraV4InitHash;
            callbackSelector = uint32(IAlgebraCallback.algebraSwapCallback.selector);
        } else {
            revertUnknownForkId(forkId);
        }
    }
}
