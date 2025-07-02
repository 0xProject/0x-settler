// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

import {SettlerBase} from "../../SettlerBase.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {DodoV2, IDodoV2} from "../../core/DodoV2.sol";
import {MaverickV2, IMaverickV2Pool} from "../../core/MaverickV2.sol";
import {UniswapV4} from "../../core/UniswapV4.sol";
import {IPoolManager} from "../../core/UniswapV4Types.sol";
import {EulerSwap, IEVC, IEulerSwap} from "../../core/EulerSwap.sol";
import {BalancerV3} from "../../core/BalancerV3.sol";
import {FreeMemory} from "../../utils/FreeMemory.sol";

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
import {aerodromeFactory, aerodromeInitHash, aerodromeForkId} from "../../core/univ3forks/AerodromeSlipstream.sol";
import {alienBaseV3Factory, alienBaseV3ForkId} from "../../core/univ3forks/AlienBaseV3.sol";
import {baseXFactory, baseXForkId} from "../../core/univ3forks/BaseX.sol";
import {swapBasedV3Factory, swapBasedV3ForkId} from "../../core/univ3forks/SwapBasedV3.sol";
import {dackieSwapV3BaseFactory, dackieSwapV3ForkId} from "../../core/univ3forks/DackieSwapV3.sol";
import {thickFactory, thickInitHash, thickForkId} from "../../core/univ3forks/Thick.sol";
import {kinetixV3BaseFactory, kinetixV3ForkId} from "../../core/univ3forks/KinetixV3.sol";

import {BASE_POOL_MANAGER} from "../../core/UniswapV4Addresses.sol";

// Solidity inheritance is stupid
import {SettlerAbstract} from "../../SettlerAbstract.sol";

abstract contract BaseMixin is FreeMemory, SettlerBase, MaverickV2, DodoV2, UniswapV4, BalancerV3, EulerSwap {
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
        } else if (action == uint32(ISettlerActions.EULERSWAP.selector)) {
            (address recipient, IERC20 sellToken, uint256 bps, IEulerSwap pool, bool zeroForOne, uint256 amountOutMin) =
                abi.decode(data, (address, IERC20, uint256, IEulerSwap, bool, uint256));

            sellToEulerSwap(recipient, sellToken, bps, pool, zeroForOne, amountOutMin);
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
                uint256 minBuyAmount
            ) = abi.decode(data, (address, IERC20, uint256, IMaverickV2Pool, bool, uint256));

            sellToMaverickV2(recipient, sellToken, bps, pool, tokenAIn, minBuyAmount);
        } else if (action == uint32(ISettlerActions.DODOV2.selector)) {
            (address recipient, IERC20 sellToken, uint256 bps, IDodoV2 dodo, bool quoteForBase, uint256 minBuyAmount) =
                abi.decode(data, (address, IERC20, uint256, IDodoV2, bool, uint256));

            sellToDodoV2(recipient, sellToken, bps, dodo, quoteForBase, minBuyAmount);
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
        if (forkId < alienBaseV3ForkId) {
            if (forkId < sushiswapV3ForkId) {
                if (forkId == uniswapV3ForkId) {
                    factory = uniswapV3BaseFactory;
                    initHash = uniswapV3InitHash;
                    callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
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
                    initHash = uniswapV3InitHash;
                    callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
                } else if (forkId == solidlyV3ForkId) {
                    factory = solidlyV3Factory;
                    initHash = solidlyV3InitHash;
                    callbackSelector = uint32(ISolidlyV3Callback.solidlyV3SwapCallback.selector);
                } else if (forkId == aerodromeForkId) {
                    factory = aerodromeFactory;
                    initHash = aerodromeInitHash;
                    callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
                } else {
                    revertUnknownForkId(forkId);
                }
            }
        } else {
            if (forkId < dackieSwapV3ForkId) {
                if (forkId == alienBaseV3ForkId) {
                    factory = alienBaseV3Factory;
                    initHash = uniswapV3InitHash;
                    callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
                } else if (forkId == baseXForkId) {
                    factory = baseXFactory;
                    initHash = uniswapV3InitHash;
                    callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
                } else if (forkId == swapBasedV3ForkId) {
                    factory = swapBasedV3Factory;
                    initHash = pancakeSwapV3InitHash;
                    callbackSelector = uint32(IPancakeSwapV3Callback.pancakeV3SwapCallback.selector);
                } else {
                    revertUnknownForkId(forkId);
                }
            } else {
                if (forkId == dackieSwapV3ForkId) {
                    factory = dackieSwapV3BaseFactory;
                    initHash = pancakeSwapV3InitHash;
                    callbackSelector = uint32(IPancakeSwapV3Callback.pancakeV3SwapCallback.selector);
                } else if (forkId == thickForkId) {
                    factory = thickFactory;
                    initHash = thickInitHash;
                    callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
                } else if (forkId == kinetixV3ForkId) {
                    factory = kinetixV3BaseFactory;
                    initHash = uniswapV3InitHash;
                    callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
                } else {
                    revertUnknownForkId(forkId);
                }
            }
        }
    }

    function _POOL_MANAGER() internal pure override returns (IPoolManager) {
        return BASE_POOL_MANAGER;
    }

    function _EVC() internal pure override returns (IEVC) {
        return IEVC(0x5301c7dD20bD945D2013b48ed0DEE3A284ca8989);
    }

    function msgSender() external view returns (address result) {
        result = _msgSender();
        require(result != address(0));
    }
}
