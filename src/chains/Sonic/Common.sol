// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

import {SettlerBase} from "../../SettlerBase.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {FreeMemory} from "../../utils/FreeMemory.sol";

import {ISettlerActions} from "../../ISettlerActions.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {UnknownForkId} from "../../core/SettlerErrors.sol";

import {
    uniswapV3SonicFactory,
    uniswapV3InitHash,
    uniswapV3ForkId,
    IUniswapV3Callback
} from "../../core/univ3forks/UniswapV3.sol";
import {
    solidlyV3SonicFactory,
    solidlyV3InitHash,
    solidlyV3ForkId,
    ISolidlyV3Callback
} from "../../core/univ3forks/SolidlyV3.sol";
import {spookySwapFactory, spookySwapForkId} from "../../core/univ3forks/SpookySwap.sol";
import {wagmiFactory, wagmiInitHash, wagmiForkId} from "../../core/univ3forks/Wagmi.sol";

// Solidity inheritance is stupid
import {SettlerAbstract} from "../../SettlerAbstract.sol";

abstract contract SonicMixin is FreeMemory, SettlerBase {
    constructor() {
        assert(block.chainid == 146 || block.chainid == 31337);
    }

    function _dispatch(uint256 i, uint256 action, bytes calldata data)
        internal
        virtual
        override(/* SettlerAbstract, */ SettlerBase)
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
            factory = uniswapV3SonicFactory;
            initHash = uniswapV3InitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else if (forkId == solidlyV3ForkId) {
            factory = solidlyV3SonicFactory;
            initHash = solidlyV3InitHash;
            callbackSelector = uint32(ISolidlyV3Callback.solidlyV3SwapCallback.selector);
        } else if (forkId == spookySwapForkId) {
            factory = spookySwapFactory;
            initHash = uniswapV3InitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else if (forkId == wagmiForkId) {
            factory = wagmiFactory;
            initHash = wagmiInitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else {
            revert UnknownForkId(forkId);
        }
    }
}