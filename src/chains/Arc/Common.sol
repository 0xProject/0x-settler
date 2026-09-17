// SPDX-License-Identifier: MIT
pragma solidity =0.8.34;

import {SettlerBase} from "../../SettlerBase.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {FreeMemory} from "../../utils/FreeMemory.sol";

import {UniswapV4} from "../../core/UniswapV4.sol";
import {IPoolManager} from "../../core/UniswapV4Types.sol";
import {PancakeInfinity} from "../../core/PancakeInfinity.sol";

import {ISettlerActions} from "../../ISettlerActions.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {revertUnknownForkId, revertUnknownPoolManagerId} from "../../core/SettlerErrors.sol";

import {
    uniswapV3ArcFactory,
    uniswapV3InitHash,
    uniswapV3ForkId,
    IUniswapV3Callback
} from "../../core/univ3forks/UniswapV3.sol";
import {sushiswapV3ArcFactory, sushiswapV3ForkId} from "../../core/univ3forks/SushiswapV3.sol";
import {ARC_POOL_MANAGER} from "../../core/UniswapV4Addresses.sol";
import {sushiswapV4Vault, sushiswapV4ClManager} from "../../core/pancakeInfinityForks/SushiswapV4.sol";

import {FastLogic} from "../../utils/FastLogic.sol";

// Solidity inheritance is stupid
import {SettlerSwapAbstract} from "../../SettlerAbstract.sol";
import {Permit2PaymentAbstract} from "../../core/Permit2PaymentAbstract.sol";

abstract contract ArcMixin is FreeMemory, SettlerBase, UniswapV4, PancakeInfinity {
    using FastLogic for bool;

    constructor() {
        assert(block.chainid == 5042 || block.chainid == 31337);
    }

    function _dispatch(uint256 i, uint256 action, bytes calldata data, AllowedSlippage memory slippage)
        internal
        virtual
        override(SettlerSwapAbstract, SettlerBase)
        DANGEROUS_freeMemory
        returns (bool)
    {
        if (super._dispatch(i, action, data, slippage)) {
            return true;
        } else if ((action == uint32(ISettlerActions.UNISWAPV4.selector))
            .or(action == uint32(ISettlerActions.PANCAKE_INFINITY.selector))) {
            (
                address recipient,
                IERC20 sellToken,
                uint256 ppm,
                bool feeOnTransfer,
                uint256 hashMul,
                uint256 hashMod,
                bytes memory fills,
                uint256 amountOutMin
            ) = abi.decode(data, (address, IERC20, uint256, bool, uint256, uint256, bytes, uint256));

            if (action == uint32(ISettlerActions.UNISWAPV4.selector)) {
                sellToUniswapV4(recipient, sellToken, ppm, feeOnTransfer, hashMul, hashMod, fills, amountOutMin);
            } else {
                // if (action == uint32(ISettlerActions.PANCAKE_INFINITY.selector))
                sellToPancakeInfinity(recipient, sellToken, ppm, feeOnTransfer, hashMul, hashMod, fills, amountOutMin);
            }
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
            factory = uniswapV3ArcFactory;
            initHash = uniswapV3InitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else if (forkId == sushiswapV3ForkId) {
            factory = sushiswapV3ArcFactory;
            initHash = uniswapV3InitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else {
            revertUnknownForkId(forkId);
        }
    }

    function _POOL_MANAGER() internal pure override returns (IPoolManager) {
        return ARC_POOL_MANAGER;
    }

    function _PANCAKE_INFINITY_VAULT() internal pure override returns (address) {
        return sushiswapV4Vault;
    }

    function _PANCAKE_INFINITY_CL_MANAGER() internal pure override returns (address) {
        return sushiswapV4ClManager;
    }

    // SushiSwap V4 does not have a Bin pool manager.
    function _PANCAKE_INFINITY_BIN_MANAGER() internal pure override returns (address) {
        revertUnknownPoolManagerId(1);
    }

    // I hate Solidity inheritance
    function _fallback(bytes calldata data)
        internal
        virtual
        override(Permit2PaymentAbstract, UniswapV4)
        returns (bool success, bytes memory returndata)
    {
        return super._fallback(data);
    }
}
