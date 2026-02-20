// SPDX-License-Identifier: MIT
pragma solidity =0.8.34;

import {SettlerBase} from "../../SettlerBase.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {FreeMemory} from "../../utils/FreeMemory.sol";

import {ISettlerActions} from "../../ISettlerActions.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {revertUnknownForkId} from "../../core/SettlerErrors.sol";

import {
    uniswapV3TaikoFactory,
    uniswapV3InitHash,
    uniswapV3ForkId,
    IUniswapV3Callback
} from "../../core/univ3forks/UniswapV3.sol";
import {swapsicleFactory, swapsicleForkId} from "../../core/univ3forks/Swapsicle.sol";
import {algebraV4InitHash, IAlgebraCallback} from "../../core/univ3forks/Algebra.sol";
import {pankoFactory, pankoInitHash, pankoForkId} from "../../core/univ3forks/Panko.sol";
import {IPancakeSwapV3Callback} from "../../core/univ3forks/PancakeSwapV3.sol";

abstract contract TaikoMixin is FreeMemory, SettlerBase {
    constructor() {
        assert(block.chainid == 167000 || block.chainid == 31337);
    }

    function _dispatch(uint256 i, uint256 action, bytes calldata data)
        internal
        virtual
        override(SettlerBase)
        DANGEROUS_freeMemory
        returns (bool)
    {
        if (super._dispatch(i, action, data)) {
            return true;
        } else {
            return false;
        }
        return true;
    }

    function _uniV3ForkInfo(uint8 forkId)
        internal
        pure
        override
        returns (address factory, bytes32 initHash, uint32 callbackSelector)
    {
        if (forkId == uniswapV3ForkId) {
            factory = uniswapV3TaikoFactory;
            initHash = uniswapV3InitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else if (forkId == swapsicleForkId) {
            factory = swapsicleFactory;
            initHash = algebraV4InitHash;
            callbackSelector = uint32(IAlgebraCallback.algebraSwapCallback.selector);
        } else if (forkId == pankoForkId) {
            factory = pankoFactory;
            initHash = pankoInitHash;
            callbackSelector = uint32(IPancakeSwapV3Callback.pancakeV3SwapCallback.selector);
        } else {
            revertUnknownForkId(forkId);
        }
    }
}
