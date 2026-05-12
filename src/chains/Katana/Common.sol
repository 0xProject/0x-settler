// SPDX-License-Identifier: MIT
pragma solidity =0.8.34;

import {SettlerBase} from "../../SettlerBase.sol";

import {FreeMemory} from "../../utils/FreeMemory.sol";

import {revertUnknownForkId} from "../../core/SettlerErrors.sol";

import {IUniswapV3Callback} from "../../core/univ3forks/UniswapV3.sol";
import {
    sushiswapV3KatanaFactory,
    sushiswapV3KatanaInitHash,
    sushiswapV3ForkId
} from "../../core/univ3forks/SushiswapV3.sol";

abstract contract KatanaMixin is FreeMemory, SettlerBase {
    constructor() {
        assert(block.chainid == 747474 || block.chainid == 31337);
    }

    function _dispatch(uint256 i, uint256 action, bytes calldata data, AllowedSlippage memory slippage)
        internal
        virtual
        override
        DANGEROUS_freeMemory
        returns (bool)
    {
        return super._dispatch(i, action, data, slippage);
    }

    function _uniV3ForkInfo(uint8 forkId)
        internal
        pure
        override
        returns (address factory, bytes32 initHash, uint32 callbackSelector)
    {
        if (forkId == sushiswapV3ForkId) {
            factory = sushiswapV3KatanaFactory;
            initHash = sushiswapV3KatanaInitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else {
            revertUnknownForkId(forkId);
        }
    }
}
