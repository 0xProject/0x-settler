// SPDX-License-Identifier: MIT
pragma solidity =0.8.33;

import {SettlerBase} from "../../SettlerBase.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {BalancerV3} from "../../core/BalancerV3.sol";
import {FreeMemory} from "../../utils/FreeMemory.sol";

import {ISettlerActions} from "../../ISettlerActions.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {revertUnknownForkId} from "../../core/SettlerErrors.sol";

import {
    uniswapV3GnosisFactory,
    uniswapV3InitHash,
    uniswapV3ForkId,
    IUniswapV3Callback
} from "../../core/univ3forks/UniswapV3.sol";
import {sushiswapV3GnosisFactory, sushiswapV3ForkId} from "../../core/univ3forks/SushiswapV3.sol";
import {swaprFactory, swaprInitHash, swaprForkId} from "../../core/univ3forks/Swapr.sol";
import {IAlgebraCallback} from "../../core/univ3forks/Algebra.sol";

// Solidity inheritance is stupid
import {SettlerSwapAbstract} from "../../SettlerAbstract.sol";

abstract contract GnosisMixin is FreeMemory, SettlerBase, BalancerV3 {
    constructor() {
        assert(block.chainid == 100 || block.chainid == 31337);
    }

    function _dispatch(uint256 i, uint256 action, bytes calldata data, AllowedSlippage memory slippage)
        internal
        virtual
        override(SettlerBase, SettlerSwapAbstract)
        DANGEROUS_freeMemory
        returns (bool)
    {
        if (super._dispatch(i, action, data, slippage)) {
            return true;
        } else if (action == uint32(ISettlerActions.BALANCERV3.selector)) {
            (
                address payable recipient,
                IERC20 sellToken,
                uint256 bps,
                bool feeOnTransfer,
                uint256 hashMul,
                uint256 hashMod,
                bytes memory fills,
                uint256 minAmountOut
            ) = abi.decode(data, (address, IERC20, uint256, bool, uint256, uint256, bytes, uint256));
            IERC20 buyToken;
            (recipient, buyToken, minAmountOut) = _maybeSetSlippage(slippage, recipient, minAmountOut);
            (IERC20 actualBuyToken, uint256 actualAmountOut) = sellToBalancerV3(recipient, sellToken, bps, feeOnTransfer, hashMul, hashMod, fills);
            _checkSlippage(buyToken, minAmountOut, actualBuyToken, actualAmountOut);
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
            factory = uniswapV3GnosisFactory;
            initHash = uniswapV3InitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else if (forkId == sushiswapV3ForkId) {
            factory = sushiswapV3GnosisFactory;
            initHash = uniswapV3InitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else if (forkId == swaprForkId) {
            factory = swaprFactory;
            initHash = swaprInitHash;
            callbackSelector = uint32(IAlgebraCallback.algebraSwapCallback.selector);
        } else {
            revertUnknownForkId(forkId);
        }
    }
}
