// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

import {SettlerBase} from "../../SettlerBase.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {UniswapV4} from "../../core/UniswapV4.sol";
import {IPoolManager} from "../../core/UniswapV4Types.sol";
import {FreeMemory} from "../../utils/FreeMemory.sol";

import {ISettlerActions} from "../../ISettlerActions.sol";
import {UnknownForkId} from "../../core/SettlerErrors.sol";

import {
    uniswapV3MainnetFactory,
    uniswapV3InitHash,
    uniswapV3ForkId,
    IUniswapV3Callback
} from "../../core/univ3forks/UniswapV3.sol";
import {pancakeSwapV3InitHash, IPancakeSwapV3Callback} from "../../core/univ3forks/PancakeSwapV3.sol";
import {sushiswapV3OptimismFactory, sushiswapV3ForkId} from "../../core/univ3forks/SushiswapV3.sol";
import {velodromeFactory, velodromeInitHash, velodromeForkId} from "../../core/univ3forks/VelodromeSlipstream.sol";
import {
    solidlyV3Factory,
    solidlyV3InitHash,
    solidlyV3ForkId,
    ISolidlyV3Callback
} from "../../core/univ3forks/SolidlyV3.sol";
import {dackieSwapV3OptimismFactory, dackieSwapV3ForkId} from "../../core/univ3forks/DackieSwapV3.sol";

import {OPTIMISM_POOL_MANAGER} from "../../core/UniswapV4Addresses.sol";

// Solidity inheritance is stupid
import {SettlerAbstract} from "../../SettlerAbstract.sol";

abstract contract OptimismMixin is FreeMemory, SettlerBase, UniswapV4 {
    constructor() {
        assert(block.chainid == 10 || block.chainid == 31337);
    }

    function _dispatch(uint256 i, uint256 action, bytes calldata data)
        internal
        virtual
        override(SettlerAbstract, SettlerBase)
        DANGEROUS_freeMemory
        returns (bool)
    {
        if (super._dispatch(i, action, data)) {
            return true;
        } else if (action == uint32(ISettlerActions.UNISWAPV4.selector)) {
            (
                address recipient,
                IERC20 sellToken,
                uint256 bps,
                bool feeOnTransfer,
                uint256 hashMul,
                uint256 hashMod,
                bytes memory fills,
                uint256 amountOutMin
            ) = abi.decode(data, (address, IERC20, uint256, bool, uint256, uint256, bytes, uint256));

            sellToUniswapV4(recipient, sellToken, bps, feeOnTransfer, hashMul, hashMod, fills, amountOutMin);
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
            factory = uniswapV3MainnetFactory;
            initHash = uniswapV3InitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else if (forkId == sushiswapV3ForkId) {
            factory = sushiswapV3OptimismFactory;
            initHash = uniswapV3InitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else if (forkId == solidlyV3ForkId) {
            factory = solidlyV3Factory;
            initHash = solidlyV3InitHash;
            callbackSelector = uint32(ISolidlyV3Callback.solidlyV3SwapCallback.selector);
        } else if (forkId == velodromeForkId) {
            factory = velodromeFactory;
            initHash = velodromeInitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else if (forkId == dackieSwapV3ForkId) {
            factory = dackieSwapV3OptimismFactory;
            initHash = pancakeSwapV3InitHash;
            callbackSelector = uint32(IPancakeSwapV3Callback.pancakeV3SwapCallback.selector);
        } else {
            revert UnknownForkId(forkId);
        }
    }

    function _POOL_MANAGER() internal pure override returns (IPoolManager) {
        return OPTIMISM_POOL_MANAGER;
    }
}
