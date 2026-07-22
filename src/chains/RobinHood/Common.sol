// SPDX-License-Identifier: MIT
pragma solidity =0.8.34;

import {SettlerBase} from "../../SettlerBase.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {FreeMemory} from "../../utils/FreeMemory.sol";
import {UniswapV4} from "../../core/UniswapV4.sol";
import {IPoolManager} from "../../core/UniswapV4Types.sol";
import {EkuboV3} from "../../core/EkuboV3.sol";

import {ISettlerActions} from "../../ISettlerActions.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {revertUnknownForkId} from "../../core/SettlerErrors.sol";

import {
    uniswapV3RobinhoodFactory,
    uniswapV3InitHash,
    uniswapV3ForkId,
    IUniswapV3Callback
} from "../../core/univ3forks/UniswapV3.sol";
import {
    pancakeSwapV3Factory,
    pancakeSwapV3InitHash,
    pancakeSwapV3ForkId,
    IPancakeSwapV3Callback
} from "../../core/univ3forks/PancakeSwapV3.sol";
import {sushiswapV3RobinhoodFactory, sushiswapV3ForkId} from "../../core/univ3forks/SushiswapV3.sol";
import {robinSwapV3Factory, robinSwapV3ForkId} from "../../core/univ3forks/RobinSwapV3.sol";
import {prjxV3InitHash} from "../../core/univ3forks/PrjxV3.sol";
import {upFactory, upInitHash, upForkId} from "../../core/univ3forks/Up.sol";
import {sheriffFactory, sheriffInitHash, sheriffForkId} from "../../core/univ3forks/Sheriff.sol";
import {swapHoodV3Factory, swapHoodV3InitHash, swapHoodV3ForkId} from "../../core/univ3forks/SwapHoodV3.sol";
import {gigaDexV3Factory, gigaDexV3InitHash, gigaDexV3ForkId} from "../../core/univ3forks/GigaDexV3.sol";
import {ramsesV3Factory, ramsesV3InitHash, ramsesV3ForkId} from "../../core/univ3forks/RamsesV3.sol";
import {IAlgebraCallback} from "../../core/univ3forks/Algebra.sol";
import {ROBINHOOD_POOL_MANAGER} from "../../core/UniswapV4Addresses.sol";

import {FastLogic} from "../../utils/FastLogic.sol";

// Solidity inheritance is stupid
import {SettlerSwapAbstract} from "../../SettlerAbstract.sol";
import {Permit2PaymentAbstract} from "../../core/Permit2PaymentAbstract.sol";

abstract contract RobinHoodMixin is FreeMemory, SettlerBase, UniswapV4, EkuboV3 {
    using FastLogic for bool;

    constructor() {
        assert(block.chainid == 4663 || block.chainid == 31337);
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
            .or(action == uint32(ISettlerActions.EKUBOV3.selector))) {
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

            if (action == uint32(ISettlerActions.UNISWAPV4.selector)) {
                sellToUniswapV4(recipient, sellToken, bps, feeOnTransfer, hashMul, hashMod, fills, amountOutMin);
            } else { // if (action == uint32(ISettlerActions.EKUBOV3.selector))
                sellToEkuboV3(recipient, sellToken, bps, feeOnTransfer, hashMul, hashMod, fills, amountOutMin);
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
            factory = uniswapV3RobinhoodFactory;
            initHash = uniswapV3InitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else if (forkId == sushiswapV3ForkId) {
            factory = sushiswapV3RobinhoodFactory;
            initHash = uniswapV3InitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else if (forkId == robinSwapV3ForkId) {
            factory = robinSwapV3Factory;
            initHash = prjxV3InitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else if (forkId == pancakeSwapV3ForkId) {
            factory = pancakeSwapV3Factory;
            initHash = pancakeSwapV3InitHash;
            callbackSelector = uint32(IPancakeSwapV3Callback.pancakeV3SwapCallback.selector);
        } else if (forkId == upForkId) {
            factory = upFactory;
            initHash = upInitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else if (forkId == sheriffForkId) {
            factory = sheriffFactory;
            initHash = sheriffInitHash;
            callbackSelector = uint32(IAlgebraCallback.algebraSwapCallback.selector);
        } else if (forkId == swapHoodV3ForkId) {
            factory = swapHoodV3Factory;
            initHash = swapHoodV3InitHash;
            callbackSelector = uint32(IPancakeSwapV3Callback.pancakeV3SwapCallback.selector);
        } else if (forkId == gigaDexV3ForkId) {
            factory = gigaDexV3Factory;
            initHash = gigaDexV3InitHash;
            callbackSelector = uint32(IPancakeSwapV3Callback.pancakeV3SwapCallback.selector);
        } else if (forkId == ramsesV3ForkId) {
            factory = ramsesV3Factory;
            initHash = ramsesV3InitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else {
            revertUnknownForkId(forkId);
        }
    }

    function _POOL_MANAGER() internal pure override returns (IPoolManager) {
        return ROBINHOOD_POOL_MANAGER;
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
