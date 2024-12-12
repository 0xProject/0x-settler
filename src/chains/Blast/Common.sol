// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {SettlerBase} from "../../SettlerBase.sol";

import {FreeMemory} from "../../utils/FreeMemory.sol";

import {ISettlerActions} from "../../ISettlerActions.sol";
import {UnknownForkId} from "../../core/SettlerErrors.sol";

import {
    uniswapV3BlastFactory,
    uniswapV3InitHash,
    uniswapV3ForkId,
    IUniswapV3Callback
} from "../../core/univ3forks/UniswapV3.sol";
import {IPancakeSwapV3Callback} from "../../core/univ3forks/PancakeSwapV3.sol";
//import {sushiswapV3BlastFactory, sushiswapV3BlastInitHash, sushiswapV3ForkId} from "../../core/univ3forks/SushiswapV3.sol";
import {thrusterFactory, thrusterInitHash, thrusterForkId} from "../../core/univ3forks/Thruster.sol";
import {IAlgebraCallback} from "../../core/univ3forks/Algebra.sol";
import {bladeSwapFactory, bladeSwapInitHash, bladeSwapForkId} from "../../core/univ3forks/BladeSwap.sol";
import {fenixFactory, fenixInitHash, fenixForkId} from "../../core/univ3forks/Fenix.sol";
import {
    dackieSwapV3BlastFactory,
    dackieSwapV3BlastInitHash,
    dackieSwapV3ForkId
} from "../../core/univ3forks/DackieSwapV3.sol";
import {
    blasterV3Factory,
    blasterV3InitHash,
    blasterV3ForkId,
    IBlasterswapV3SwapCallback
} from "../../core/univ3forks/BlasterV3.sol";
import {monoSwapV3Factory, monoSwapV3InitHash, monoSwapV3ForkId} from "../../core/univ3forks/MonoSwapV3.sol";
import {
    rogueXV1Factory, rogueXV1InitHash, rogueXV1ForkId, IRoxSpotSwapCallback
} from "../../core/univ3forks/RogueXV1.sol";

import {IOwnable} from "../../deployer/TwoStepOwnable.sol";
import {BLAST, BLAST_USDB, BLAST_WETH, BlastYieldMode, BlastGasMode} from "./IBlast.sol";

// Solidity inheritance is stupid
import {Permit2PaymentAbstract} from "../../core/Permit2PaymentAbstract.sol";

abstract contract BlastMixin is FreeMemory, SettlerBase {
    constructor() {
        if (block.chainid != 31337) {
            assert(block.chainid == 81457);
            BLAST.configure(
                BlastYieldMode.AUTOMATIC,
                BlastGasMode.CLAIMABLE,
                IOwnable(0x00000000000004533Fe15556B1E086BB1A72cEae).owner()
            );
            BLAST_USDB.configure(BlastYieldMode.VOID);
            BLAST_WETH.configure(BlastYieldMode.VOID);
        }
    }

    function _isRestrictedTarget(address target)
        internal
        pure
        virtual
        override(Permit2PaymentAbstract)
        returns (bool)
    {
        return target == address(BLAST);
    }

    function _dispatch(uint256 i, uint256 action, bytes calldata data)
        internal
        virtual
        override
        DANGEROUS_freeMemory
        returns (bool)
    {
        return super._dispatch(i, action, data);
    }

    function _uniV3ForkInfo(uint8 forkId)
        internal
        pure
        override
        returns (address factory, bytes32 initHash, uint32 callbackSelector)
    {
        if (forkId < dackieSwapV3ForkId) {
            if (forkId == uniswapV3ForkId) {
                factory = uniswapV3BlastFactory;
                initHash = uniswapV3InitHash;
                callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
            //} else if (forkId == sushiswapV3ForkId) {
            //    factory = sushiswapV3BlastFactory;
            //    initHash = sushiswapV3BlastInitHash;
            //    callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
            } else if (forkId == thrusterForkId) {
                factory = thrusterFactory;
                initHash = thrusterInitHash;
                callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
            } else if (forkId == bladeSwapForkId) {
                factory = bladeSwapFactory;
                initHash = bladeSwapInitHash;
                callbackSelector = uint32(IAlgebraCallback.algebraSwapCallback.selector);
            } else if (forkId == fenixForkId) {
                factory = fenixFactory;
                initHash = fenixInitHash;
                callbackSelector = uint32(IAlgebraCallback.algebraSwapCallback.selector);
            } else {
                revert UnknownForkId(forkId);
            }
        } else {
            if (forkId == dackieSwapV3ForkId) {
                factory = dackieSwapV3BlastFactory;
                initHash = dackieSwapV3BlastInitHash;
                callbackSelector = uint32(IPancakeSwapV3Callback.pancakeV3SwapCallback.selector);
            } else if (forkId == blasterV3ForkId) {
                factory = blasterV3Factory;
                initHash = blasterV3InitHash;
                callbackSelector = uint32(IBlasterswapV3SwapCallback.blasterswapV3SwapCallback.selector);
            } else if (forkId == monoSwapV3ForkId) {
                factory = monoSwapV3Factory;
                initHash = monoSwapV3InitHash;
                callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
            } else if (forkId == rogueXV1ForkId) {
                factory = rogueXV1Factory;
                initHash = rogueXV1InitHash;
                callbackSelector = uint32(IRoxSpotSwapCallback.swapCallback.selector);
            } else {
                revert UnknownForkId(forkId);
            }
        }
    }
}