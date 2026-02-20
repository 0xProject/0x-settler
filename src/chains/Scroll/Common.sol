// SPDX-License-Identifier: MIT
pragma solidity =0.8.34;

import {SettlerBase} from "../../SettlerBase.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {MaverickV2, IMaverickV2Pool} from "../../core/MaverickV2.sol";
import {DodoV1, IDodoV1} from "../../core/DodoV1.sol";
import {DodoV2, IDodoV2} from "../../core/DodoV2.sol";
import {FreeMemory} from "../../utils/FreeMemory.sol";

import {uint512} from "../../utils/512Math.sol";

import {ISettlerActions} from "../../ISettlerActions.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {revertUnknownForkId} from "../../core/SettlerErrors.sol";

import {
    uniswapV3ScrollFactory,
    uniswapV3InitHash,
    uniswapV3ForkId,
    IUniswapV3Callback
} from "../../core/univ3forks/UniswapV3.sol";
import {sushiswapV3ScrollFactory, sushiswapV3ForkId} from "../../core/univ3forks/SushiswapV3.sol";
import {zebraV3Factory, zebraV3InitHash, zebraV3ForkId, IZebraV3SwapCallback} from "../../core/univ3forks/ZebraV3.sol";
import {metavaultV3Factory, metavaultV3ForkId} from "../../core/univ3forks/MetavaultV3.sol";

// Solidity inheritance is stupid
import {SettlerAbstract} from "../../SettlerAbstract.sol";

abstract contract ScrollMixin is FreeMemory, SettlerBase, MaverickV2, DodoV1, DodoV2 {
    constructor() {
        assert(block.chainid == 534352 || block.chainid == 31337);
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
            factory = uniswapV3ScrollFactory;
            initHash = uniswapV3InitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else if (forkId == sushiswapV3ForkId) {
            factory = sushiswapV3ScrollFactory;
            initHash = uniswapV3InitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else if (forkId == zebraV3ForkId) {
            factory = zebraV3Factory;
            initHash = zebraV3InitHash;
            callbackSelector = uint32(IZebraV3SwapCallback.zebraV3SwapCallback.selector);
        } else if (forkId == metavaultV3ForkId) {
            factory = metavaultV3Factory;
            initHash = uniswapV3InitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else {
            revertUnknownForkId(forkId);
        }
    }

    function _div512to256(uint512 n, uint512 d)
        internal
        view
        virtual
        override(SettlerBase, SettlerAbstract)
        returns (uint256)
    {
        return n.divAlt(d);
    }
}
