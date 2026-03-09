// SPDX-License-Identifier: MIT
pragma solidity =0.8.33;

import {SettlerBase} from "../../SettlerBase.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {DodoV2, IDodoV2} from "../../core/DodoV2.sol";
import {MaverickV2, IMaverickV2Pool} from "../../core/MaverickV2.sol";
import {UniswapV4} from "../../core/UniswapV4.sol";
import {IPoolManager} from "../../core/UniswapV4Types.sol";
import {EulerSwap, IEVC, IEulerSwap} from "../../core/EulerSwap.sol";
import {BalancerV3} from "../../core/BalancerV3.sol";
import {PancakeInfinity} from "../../core/PancakeInfinity.sol";
import {Renegade, BASE_SELECTOR} from "../../core/Renegade.sol";
import {Bebop} from "../../core/Bebop.sol";
import {Hanji} from "../../core/Hanji.sol";

import {IMsgSender} from "../../interfaces/IMsgSender.sol";
import {FreeMemory} from "../../utils/FreeMemory.sol";
import {FastLogic} from "../../utils/FastLogic.sol";

import {ISettlerActions} from "../../ISettlerActions.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {revertUnknownForkId} from "../../core/SettlerErrors.sol";

import {
    uniswapV3BaseFactory,
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
import {sushiswapV3Factory, sushiswapV3ForkId} from "../../core/univ3forks/SushiswapV3.sol";
import {
    solidlyV3Factory,
    solidlyV3InitHash,
    solidlyV3ForkId,
    ISolidlyV3Callback
} from "../../core/univ3forks/SolidlyV3.sol";
import {
    aerodromeFactoryV3_0,
    aerodromeFactoryV3_1,
    aerodromeInitHashV3_0,
    aerodromeInitHashV3_1,
    aerodromeForkIdV3_0,
    aerodromeForkIdV3_1
} from "../../core/univ3forks/AerodromeSlipstream.sol";
import {alienBaseV3Factory, alienBaseV3ForkId} from "../../core/univ3forks/AlienBaseV3.sol";
import {swapBasedV3Factory, swapBasedV3ForkId} from "../../core/univ3forks/SwapBasedV3.sol";

import {BASE_POOL_MANAGER} from "../../core/UniswapV4Addresses.sol";

// Solidity inheritance is stupid
import {SettlerAbstract} from "../../SettlerAbstract.sol";
import {Permit2PaymentAbstract} from "../../core/Permit2PaymentAbstract.sol";

abstract contract BaseMixin is
    FreeMemory,
    SettlerBase,
    MaverickV2,
    DodoV2,
    UniswapV4,
    BalancerV3,
    PancakeInfinity,
    //EulerSwap,
    Renegade,
    Bebop,
    Hanji
{
    using FastLogic for bool;

    constructor() {
        assert(block.chainid == 8453 || block.chainid == 31337);
    }

    function _dispatch(uint256 i, uint256 action, bytes calldata data)
        internal
        virtual
        override(SettlerBase, SettlerAbstract)
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
        /*
        } else if (action == uint32(ISettlerActions.EULERSWAP.selector)) {
            (address recipient, IERC20 sellToken, uint256 bps, IEulerSwap pool, bool zeroForOne, uint256 amountOutMin) =
                abi.decode(data, (address, IERC20, uint256, IEulerSwap, bool, uint256));

            sellToEulerSwap(recipient, sellToken, bps, pool, zeroForOne, amountOutMin);
        */
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
        } else if (action == uint32(ISettlerActions.PANCAKE_INFINITY.selector)) {
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

            sellToPancakeInfinity(recipient, sellToken, bps, feeOnTransfer, hashMul, hashMod, fills, amountOutMin);
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
        } else if (action == uint32(ISettlerActions.RENEGADE.selector)) {
            (address target, IERC20 baseToken, bytes memory renegadeData) = abi.decode(data, (address, IERC20, bytes));

            sellToRenegade(target, baseToken, renegadeData);
        } else if (action == uint32(ISettlerActions.HANJI.selector)) {
            (
                IERC20 sellToken,
                uint256 bps,
                address pool,
                uint256 sellScalingFactor,
                uint256 buyScalingFactor,
                bool isAsk,
                uint256 priceLimit,
                uint256 minBuyAmount
            ) = abi.decode(data, (IERC20, uint256, address, uint256, uint256, bool, uint256, uint256));

            sellToHanji(sellToken, bps, pool, sellScalingFactor, buyScalingFactor, isAsk, priceLimit, minBuyAmount);
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
        initHash = uniswapV3InitHash;
        callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        if (forkId < aerodromeForkIdV3_0) {
            if (forkId < sushiswapV3ForkId) {
                if (forkId == uniswapV3ForkId) {
                    factory = uniswapV3BaseFactory;
                } else if (forkId == pancakeSwapV3ForkId) {
                    factory = pancakeSwapV3Factory;
                    initHash = pancakeSwapV3InitHash;
                    callbackSelector = uint32(IPancakeSwapV3Callback.pancakeV3SwapCallback.selector);
                } else {
                    revertUnknownForkId(forkId);
                }
            } else {
                if (forkId == sushiswapV3ForkId) {
                    factory = sushiswapV3Factory;
                } else if (forkId == solidlyV3ForkId) {
                    factory = solidlyV3Factory;
                    initHash = solidlyV3InitHash;
                    callbackSelector = uint32(ISolidlyV3Callback.solidlyV3SwapCallback.selector);
                } else {
                    revertUnknownForkId(forkId);
                }
            }
        } else {
            if (forkId < swapBasedV3ForkId) {
                if (forkId == aerodromeForkIdV3_0) {
                    factory = aerodromeFactoryV3_0;
                    initHash = aerodromeInitHashV3_0;
                } else if (forkId == alienBaseV3ForkId) {
                    factory = alienBaseV3Factory;
                } else {
                    revertUnknownForkId(forkId);
                }
            } else {
                if (forkId == swapBasedV3ForkId) {
                    factory = swapBasedV3Factory;
                    initHash = pancakeSwapV3InitHash;
                    callbackSelector = uint32(IPancakeSwapV3Callback.pancakeV3SwapCallback.selector);
                } else if (forkId == aerodromeForkIdV3_1) {
                    factory = aerodromeFactoryV3_1;
                    initHash = aerodromeInitHashV3_1;
                } else {
                    revertUnknownForkId(forkId);
                }
            }
        }
    }

    function _POOL_MANAGER() internal pure override returns (IPoolManager) {
        return BASE_POOL_MANAGER;
    }

    /*
    function _EVC() internal pure override returns (IEVC) {
        return IEVC(0x5301c7dD20bD945D2013b48ed0DEE3A284ca8989);
    }
    */

    function _fallback(bytes calldata data)
        internal
        virtual
        override(Permit2PaymentAbstract, UniswapV4)
        returns (bool success, bytes memory returndata)
    {
        address msgSender = _msgSender();
        uint256 selector;
        assembly ("memory-safe") {
            selector := shr(0xe0, calldataload(data.offset))
        }
        uint256 msgSenderShifted = uint256(uint160(msgSender)) << 96;
        success = (selector == uint32(IMsgSender.msgSender.selector)).and(msgSenderShifted != 0);
        if (!success) {
            return super._fallback(data);
        }
        assembly ("memory-safe") {
            returndata := mload(0x40)
            mstore(0x40, add(0x40, returndata))
            mstore(returndata, 0x20)
            mstore(add(0x20, returndata), shr(0x60, msgSenderShifted))
        }
    }

    function _renegadeSelector() internal pure override returns (uint32) {
        return BASE_SELECTOR;
    }

    // I hate Solidity inheritance
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
