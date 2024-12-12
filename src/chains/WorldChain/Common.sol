// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

import {SettlerBase} from "../../SettlerBase.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {FreeMemory} from "../../utils/FreeMemory.sol";

import {ISettlerActions} from "../../ISettlerActions.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {UnknownForkId} from "../../core/SettlerErrors.sol";

import {
    uniswapV3WorldChainFactory,
    uniswapV3InitHash,
    uniswapV3ForkId,
    IUniswapV3Callback
} from "../../core/univ3forks/UniswapV3.sol";
import {dackieSwapV3WorldChainFactory, dackieSwapV3ForkId} from "../../core/univ3forks/DackieSwapV3.sol";
import {pancakeSwapV3InitHash, IPancakeSwapV3Callback} from "../../core/univ3forks/PancakeSwapV3.sol";

abstract contract WorldChainMixin is FreeMemory, SettlerBase {
    constructor() {
        assert(block.chainid == 480 || block.chainid == 31337);
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
            factory = uniswapV3WorldChainFactory;
            initHash = uniswapV3InitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else if (forkId == dackieSwapV3ForkId) {
            factory = dackieSwapV3WorldChainFactory;
            initHash = pancakeSwapV3InitHash;
            callbackSelector = uint32(IPancakeSwapV3Callback.pancakeV3SwapCallback.selector);
        } else {
            revert UnknownForkId(forkId);
        }
    }
}
