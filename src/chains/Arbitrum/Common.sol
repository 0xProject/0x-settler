// SPDX-License-Identifier: MIT
pragma solidity =0.8.34;

import {SettlerBase} from "../../SettlerBase.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {MaverickV2, IMaverickV2Pool} from "../../core/MaverickV2.sol";
import {CurveTricrypto} from "../../core/CurveTricrypto.sol";
import {DodoV1, IDodoV1} from "../../core/DodoV1.sol";
import {DodoV2, IDodoV2} from "../../core/DodoV2.sol";
import {UniswapV4} from "../../core/UniswapV4.sol";
import {IPoolManager} from "../../core/UniswapV4Types.sol";
import {BalancerV3} from "../../core/BalancerV3.sol";
import {FreeMemory} from "../../utils/FreeMemory.sol";
import {Renegade, ARBITRUM_SELECTOR} from "../../core/Renegade.sol";
import {Bebop} from "../../core/Bebop.sol";

import {ISettlerActions} from "../../ISettlerActions.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {revertUnknownForkId} from "../../core/SettlerErrors.sol";

import {
    uniswapV3MainnetFactory,
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
import {sushiswapV3ArbitrumFactory, sushiswapV3ForkId} from "../../core/univ3forks/SushiswapV3.sol";
import {
    solidlyV3Factory,
    solidlyV3InitHash,
    solidlyV3ForkId,
    ISolidlyV3Callback
} from "../../core/univ3forks/SolidlyV3.sol";
import {IAlgebraCallback} from "../../core/univ3forks/Algebra.sol";
import {camelotV3Factory, camelotV3InitHash, camelotV3ForkId} from "../../core/univ3forks/CamelotV3.sol";
import {dackieSwapV3ArbitrumFactory, dackieSwapV3ForkId} from "../../core/univ3forks/DackieSwapV3.sol";

import {ARBITRUM_POOL_MANAGER} from "../../core/UniswapV4Addresses.sol";

// Solidity inheritance is stupid
import {SettlerAbstract} from "../../SettlerAbstract.sol";
import {Permit2PaymentAbstract} from "../../core/Permit2PaymentAbstract.sol";

abstract contract ArbitrumMixin is
    FreeMemory,
    SettlerBase,
    MaverickV2,
    CurveTricrypto,
    DodoV1,
    DodoV2,
    UniswapV4,
    BalancerV3,
    Renegade,
    Bebop
{
    constructor() {
        assert(block.chainid == 42161 || block.chainid == 31337);
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
        } else if (action == uint32(ISettlerActions.BALANCERV3.selector)) {
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

            sellToBalancerV3(recipient, sellToken, bps, feeOnTransfer, hashMul, hashMod, fills, amountOutMin);
        } else if (action == uint32(ISettlerActions.MAVERICKV2.selector)) {
            (
                address recipient,
                IERC20 sellToken,
                uint256 bps,
                IMaverickV2Pool pool,
                bool tokenAIn,
                int32 tickLimit,
                uint256 minBuyAmount
            ) = abi.decode(data, (address, IERC20, uint256, IMaverickV2Pool, bool, int32, uint256));

            sellToMaverickV2(recipient, sellToken, bps, pool, tokenAIn, tickLimit, minBuyAmount);
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
        } else if (action == uint32(ISettlerActions.DODOV2.selector)) {
            (address recipient, IERC20 sellToken, uint256 bps, IDodoV2 dodo, bool quoteForBase, uint256 minBuyAmount) =
                abi.decode(data, (address, IERC20, uint256, IDodoV2, bool, uint256));

            sellToDodoV2(recipient, sellToken, bps, dodo, quoteForBase, minBuyAmount);
        } else if (action == uint32(ISettlerActions.DODOV1.selector)) {
            (IERC20 sellToken, uint256 bps, IDodoV1 dodo, bool quoteForBase, uint256 minBuyAmount) =
                abi.decode(data, (IERC20, uint256, IDodoV1, bool, uint256));

            sellToDodoV1(sellToken, bps, dodo, quoteForBase, minBuyAmount);
        } else if (action == uint32(ISettlerActions.RENEGADE.selector)) {
            (address target, IERC20 baseToken, bytes memory renegadeData) = abi.decode(data, (address, IERC20, bytes));

            sellToRenegade(target, baseToken, renegadeData);
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
        if (forkId < solidlyV3ForkId) {
            if (forkId == uniswapV3ForkId) {
                factory = uniswapV3MainnetFactory;
                initHash = uniswapV3InitHash;
                callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
            } else if (forkId == pancakeSwapV3ForkId) {
                factory = pancakeSwapV3Factory;
                initHash = pancakeSwapV3InitHash;
                callbackSelector = uint32(IPancakeSwapV3Callback.pancakeV3SwapCallback.selector);
            } else if (forkId == sushiswapV3ForkId) {
                factory = sushiswapV3ArbitrumFactory;
                initHash = uniswapV3InitHash;
                callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
            } else {
                revertUnknownForkId(forkId);
            }
        } else {
            if (forkId == solidlyV3ForkId) {
                factory = solidlyV3Factory;
                initHash = solidlyV3InitHash;
                callbackSelector = uint32(ISolidlyV3Callback.solidlyV3SwapCallback.selector);
            } else if (forkId == camelotV3ForkId) {
                factory = camelotV3Factory;
                initHash = camelotV3InitHash;
                callbackSelector = uint32(IAlgebraCallback.algebraSwapCallback.selector);
            } else if (forkId == dackieSwapV3ForkId) {
                factory = dackieSwapV3ArbitrumFactory;
                initHash = pancakeSwapV3InitHash;
                callbackSelector = uint32(IPancakeSwapV3Callback.pancakeV3SwapCallback.selector);
            } else {
                revertUnknownForkId(forkId);
            }
        }
    }

    function _curveFactory() internal pure override returns (address) {
        return 0xbC0797015fcFc47d9C1856639CaE50D0e69FbEE8;
    }

    function _POOL_MANAGER() internal pure override returns (IPoolManager) {
        return ARBITRUM_POOL_MANAGER;
    }

    function _renegadeSelector() internal pure override returns (uint32) {
        return ARBITRUM_SELECTOR;
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
