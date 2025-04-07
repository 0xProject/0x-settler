// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

import {SettlerBase} from "../../SettlerBase.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {IPSM, MakerPSM} from "../../core/MakerPSM.sol";
import {MaverickV2, IMaverickV2Pool} from "../../core/MaverickV2.sol";
// When these actions are reenabled, reenable the integration tests by setting `curveV2TricryptoPoolId()`
// import {CurveTricrypto} from "../../core/CurveTricrypto.sol";
import {DodoV1, IDodoV1} from "../../core/DodoV1.sol";
import {DodoV2, IDodoV2} from "../../core/DodoV2.sol";
import {UniswapV4} from "../../core/UniswapV4.sol";
import {IPoolManager} from "../../core/UniswapV4Types.sol";
import {BalancerV3} from "../../core/BalancerV3.sol";

import {SafeTransferLib} from "../../vendor/SafeTransferLib.sol";
import {FreeMemory} from "../../utils/FreeMemory.sol";

import {ISettlerActions} from "../../ISettlerActions.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {UnknownForkId} from "../../core/SettlerErrors.sol";

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
import {sushiswapV3MainnetFactory, sushiswapV3ForkId} from "../../core/univ3forks/SushiswapV3.sol";
import {
    solidlyV3Factory,
    solidlyV3InitHash,
    solidlyV3ForkId,
    ISolidlyV3Callback
} from "../../core/univ3forks/SolidlyV3.sol";

import {MAINNET_POOL_MANAGER} from "../../core/UniswapV4Addresses.sol";

// Solidity inheritance is stupid
import {SettlerAbstract} from "../../SettlerAbstract.sol";

abstract contract MainnetMixin is
    FreeMemory,
    SettlerBase,
    MakerPSM,
    MaverickV2,
    //CurveTricrypto,
    DodoV1,
    DodoV2,
    UniswapV4,
    BalancerV3
{
    using SafeTransferLib for IERC20;
    using SafeTransferLib for address payable;

    constructor() {
        assert(block.chainid == 1 || block.chainid == 31337);
    }

    function _dispatch(uint256 i, uint256 action, bytes calldata data)
        internal
        virtual
        override(SettlerAbstract, SettlerBase)
        DANGEROUS_freeMemory
        returns (bool)
    {
        //// NOTICE: we re-implement the base `_dispatch` implementation here so that we can remove
        //// the `VELODROME` action JUST on this chain because it does little-to-no volume.

        if (action == uint32(ISettlerActions.RFQ.selector)) {
            (
                address recipient,
                ISignatureTransfer.PermitTransferFrom memory permit,
                address maker,
                bytes memory makerSig,
                IERC20 takerToken,
                uint256 maxTakerAmount
            ) = abi.decode(data, (address, ISignatureTransfer.PermitTransferFrom, address, bytes, IERC20, uint256));

            fillRfqOrderSelfFunded(recipient, permit, maker, makerSig, takerToken, maxTakerAmount);
        } else if (action == uint32(ISettlerActions.UNISWAPV3.selector)) {
            (address recipient, uint256 bps, bytes memory path, uint256 amountOutMin) =
                abi.decode(data, (address, uint256, bytes, uint256));

            sellToUniswapV3(recipient, bps, path, amountOutMin);
        } else if (action == uint32(ISettlerActions.UNISWAPV2.selector)) {
            (address recipient, address sellToken, uint256 bps, address pool, uint24 swapInfo, uint256 amountOutMin) =
                abi.decode(data, (address, address, uint256, address, uint24, uint256));

            sellToUniswapV2(recipient, sellToken, bps, pool, swapInfo, amountOutMin);
        } else if (action == uint32(ISettlerActions.BASIC.selector)) {
            (IERC20 sellToken, uint256 bps, address pool, uint256 offset, bytes memory _data) =
                abi.decode(data, (IERC20, uint256, address, uint256, bytes));

            basicSellToPool(sellToken, bps, pool, offset, _data);
        } /* `VELODROME` is removed */
        else if (action == uint32(ISettlerActions.POSITIVE_SLIPPAGE.selector)) {
            (address recipient, IERC20 token, uint256 expectedAmount) = abi.decode(data, (address, IERC20, uint256));
            if (token == ETH_ADDRESS) {
                uint256 balance = address(this).balance;
                if (balance > expectedAmount) {
                    unchecked {
                        payable(recipient).safeTransferETH(balance - expectedAmount);
                    }
                }
            } else {
                uint256 balance = token.fastBalanceOf(address(this));
                if (balance > expectedAmount) {
                    unchecked {
                        token.safeTransfer(recipient, balance - expectedAmount);
                    }
                }
            }
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
        } else if (action == uint32(ISettlerActions.MAKERPSM.selector)) {
            (address recipient, uint256 bps, bool buyGem, uint256 amountOutMin) =
                abi.decode(data, (address, uint256, bool, uint256));

            sellToMakerPsm(recipient, bps, buyGem, amountOutMin);
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
        } else if (action == uint32(ISettlerActions.DODOV1.selector)) {
            (IERC20 sellToken, uint256 bps, IDodoV1 dodo, bool quoteForBase, uint256 minBuyAmount) =
                abi.decode(data, (IERC20, uint256, IDodoV1, bool, uint256));

            sellToDodoV1(sellToken, bps, dodo, quoteForBase, minBuyAmount);
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
        } else if (forkId == pancakeSwapV3ForkId) {
            factory = pancakeSwapV3Factory;
            initHash = pancakeSwapV3InitHash;
            callbackSelector = uint32(IPancakeSwapV3Callback.pancakeV3SwapCallback.selector);
        } else if (forkId == sushiswapV3ForkId) {
            factory = sushiswapV3MainnetFactory;
            initHash = uniswapV3InitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else if (forkId == solidlyV3ForkId) {
            factory = solidlyV3Factory;
            initHash = solidlyV3InitHash;
            callbackSelector = uint32(ISolidlyV3Callback.solidlyV3SwapCallback.selector);
        } else {
            revert UnknownForkId(forkId);
        }
    }

    /*
    function _curveFactory() internal pure override returns (address) {
        return 0x0c0e5f2fF0ff18a3be9b835635039256dC4B4963;
    }
    */

    function _POOL_MANAGER() internal pure override returns (IPoolManager) {
        return MAINNET_POOL_MANAGER;
    }
}
