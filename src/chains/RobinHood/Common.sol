// SPDX-License-Identifier: MIT
pragma solidity =0.8.34;

import {SettlerBase} from "../../SettlerBase.sol";
import {Attest} from "../../core/Attest.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {FreeMemory} from "../../utils/FreeMemory.sol";
import {FastLogic} from "../../utils/FastLogic.sol";
import {UniswapV4} from "../../core/UniswapV4.sol";
import {IPoolManager} from "../../core/UniswapV4Types.sol";
import {Hanji} from "../../core/Hanji.sol";
import {Bebop} from "../../core/Bebop.sol";
import {FluxPool} from "../../core/FluxPool.sol";
import {PancakeInfinity} from "../../core/PancakeInfinity.sol";

import {ISettlerActions} from "../../ISettlerActions.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {revertUnknownForkId, revertUnknownPoolManagerId} from "../../core/SettlerErrors.sol";
import {aeroRobinHoodFactory, aeroInitHash, aeroForkId} from "../../core/univ3forks/Aero.sol";

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
import {alandaleFactory, alandaleInitHash, alandaleForkId} from "../../core/univ3forks/Alandale.sol";
import {namiRobinhoodFactory, namiInitHash, namiForkId} from "../../core/univ3forks/Nami.sol";
import {IAlgebraCallback} from "../../core/univ3forks/Algebra.sol";

import {uniswapV4RobinhoodPoolManager, uniswapV4ForkId} from "../../core/univ4forks/UniswapV4.sol";
import {
    pancakeInfinityForkId,
    pancakeInfinityRobinHoodVault,
    pancakeInfinityRobinHoodClManager
} from "../../core/pancakeInfinityForks/PancakeInfinity.sol";
import {orvexVault, orvexClManager, orvexForkId} from "../../core/pancakeInfinityForks/OrvexCL.sol";

// Solidity inheritance is stupid
import {SettlerSwapAbstract} from "../../SettlerAbstract.sol";
import {Permit2PaymentAbstract} from "../../core/Permit2PaymentAbstract.sol";

abstract contract RobinHoodMixin is
    FreeMemory,
    SettlerBase,
    UniswapV4,
    Hanji,
    PancakeInfinity,
    Bebop,
    FluxPool
{
    using FastLogic for bool;

    constructor() {
        assert(block.chainid == _chainId() || block.chainid == 31337);
    }

    function _chainId() internal pure override returns (uint256) {
        return 4663;
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
                uint8 forkId,
                bool feeOnTransfer,
                uint256 hashMul,
                uint256 hashMod,
                bytes memory fills,
                uint256 amountOutMin
            ) = abi.decode(data, (address, IERC20, uint256, uint8, bool, uint256, uint256, bytes, uint256));

            if (action == uint32(ISettlerActions.UNISWAPV4.selector)) {
                sellToUniswapV4(recipient, sellToken, ppm, forkId, feeOnTransfer, hashMul, hashMod, fills, amountOutMin);
            } else {
                // if (action == uint32(ISettlerActions.PANCAKE_INFINITY.selector))
                sellToPancakeInfinity(
                    recipient, sellToken, ppm, forkId, feeOnTransfer, hashMul, hashMod, fills, amountOutMin
                );
            }
        } else if (action == uint32(ISettlerActions.HANJI.selector)) {
            (
                IERC20 sellToken,
                uint256 ppm,
                address pool,
                uint256 sellScalingFactor,
                uint256 buyScalingFactor,
                bool isAsk,
                uint256 priceLimit,
                uint256 minBuyAmount
            ) = abi.decode(data, (IERC20, uint256, address, uint256, uint256, bool, uint256, uint256));

            sellToHanji(sellToken, ppm, pool, sellScalingFactor, buyScalingFactor, isAsk, priceLimit, minBuyAmount);
        } else if (action == uint32(ISettlerActions.DEEPSTATE.selector)) {
            revert("unimplemented");
        } else if (action == uint32(ISettlerActions.FLUXPOOL.selector)) {
            (IERC20 sellToken, uint256 ppm, bytes32 poolId, bool zeroForOne, uint256 minBuyAmount) =
                abi.decode(data, (IERC20, uint256, bytes32, bool, uint256));

            sellToFluxPool(sellToken, ppm, poolId, zeroForOne, minBuyAmount);
        } else if (action == uint32(ISettlerActions.BEBOP.selector)) {
            (
                address recipient,
                IERC20 sellToken,
                ISettlerActions.BebopOrder memory order,
                ISettlerActions.BebopMakerSignature memory makerSignature,
                uint256 amountOutMin
            ) = abi.decode(
                data, (address, IERC20, ISettlerActions.BebopOrder, ISettlerActions.BebopMakerSignature, uint256)
            );

            sellToBebop(payable(recipient), sellToken, order, makerSignature, amountOutMin);
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
        } else if (forkId == alandaleForkId) {
            factory = alandaleFactory;
            initHash = alandaleInitHash;
            callbackSelector = uint32(IAlgebraCallback.algebraSwapCallback.selector);
        } else if (forkId == namiForkId) {
            factory = namiRobinhoodFactory;
            initHash = namiInitHash;
            callbackSelector = uint32(IAlgebraCallback.algebraSwapCallback.selector);
        } else if (forkId == aeroForkId) {
            factory = aeroRobinHoodFactory;
            initHash = aeroInitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else {
            revertUnknownForkId(forkId);
        }
    }

    function _fluxSwap() internal pure override returns (address) {
        return 0x388e0D8f610a80C75e8a049C39DDc5816f56c012;
    }

    function _uniV4ForkInfo(uint8 forkId) internal pure override returns (IPoolManager poolManager) {
        if (forkId == uniswapV4ForkId) {
            poolManager = uniswapV4RobinhoodPoolManager;
        } else {
            revertUnknownForkId(forkId);
        }
    }

    function _pancakeInfinityForkInfo(uint8 forkId)
        internal
        pure
        override
        returns (address vault, address clManager, address binManager)
    {
        if (forkId == pancakeInfinityForkId) {
            vault = pancakeInfinityRobinHoodVault;
            clManager = pancakeInfinityRobinHoodClManager;
            binManager = address(0);
        } else if (forkId == orvexForkId) {
            vault = orvexVault;
            clManager = orvexClManager;
            // Orvex does not have a Bin pool manager
            binManager = address(0);
        } else {
            revertUnknownForkId(forkId);
        }
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

    function _isRestrictedTarget(address target)
        internal
        view
        virtual
        override(Bebop, Permit2PaymentAbstract)
        returns (bool)
    {
        return super._isRestrictedTarget(target);
    }
}

// `Attest` is listed last so that candidate selection sits above the chain actions in the
// linearization; see `Select`.
abstract contract RobinHoodCommon is RobinHoodMixin, Attest {
    function _dispatch(uint256 i, uint256 action, bytes calldata data, AllowedSlippage memory slippage)
        internal
        virtual
        override(RobinHoodMixin, Attest)
        returns (bool)
    {
        return super._dispatch(i, action, data, slippage);
    }

    function _isRestrictedTarget(address target)
        internal
        view
        virtual
        override(RobinHoodMixin, Permit2PaymentAbstract)
        returns (bool)
    {
        return super._isRestrictedTarget(target);
    }

    function _fallback(bytes calldata data)
        internal
        virtual
        override(RobinHoodMixin, Attest)
        returns (bool success, bytes memory returndata)
    {
        return super._fallback(data);
    }
}
