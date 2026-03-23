// SPDX-License-Identifier: MIT
pragma solidity =0.8.33;

import {SettlerBase} from "../../SettlerBase.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {BalancerV3} from "../../core/BalancerV3.sol";
import {EulerSwap, IEVC, IEulerSwap} from "../../core/EulerSwap.sol";
import {FreeMemory} from "../../utils/FreeMemory.sol";

import {ISettlerActions} from "../../ISettlerActions.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {revertUnknownForkId} from "../../core/SettlerErrors.sol";

import {
    uniswapV3PlasmaFactory,
    uniswapV3InitHash,
    uniswapV3ForkId,
    IUniswapV3Callback
} from "../../core/univ3forks/UniswapV3.sol";

// Solidity inheritance is stupid
import {SettlerSwapAbstract} from "../../SettlerAbstract.sol";

abstract contract PlasmaMixin is FreeMemory, SettlerBase, BalancerV3, EulerSwap {
    constructor() {
        assert(block.chainid == 9745 || block.chainid == 31337);
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
        } else if (action == uint32(ISettlerActions.EULERSWAP.selector)) {
            (
                address payable recipient,
                IERC20 sellToken,
                uint256 bps,
                IEulerSwap pool,
                bool zeroForOne,
                uint256 minAmountOut
            ) = abi.decode(data, (address, IERC20, uint256, IEulerSwap, bool, uint256));
            IERC20 buyToken;
            (recipient, buyToken, minAmountOut) = _maybeSetSlippage(slippage, recipient, minAmountOut);
            (IERC20 actualBuyToken, uint256 actualAmountOut) =
                sellToEulerSwap(recipient, sellToken, bps, pool, zeroForOne);
            _checkSlippage(buyToken, minAmountOut, actualBuyToken, actualAmountOut);
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
            (IERC20 actualBuyToken, uint256 actualAmountOut) =
                sellToBalancerV3(recipient, sellToken, bps, feeOnTransfer, hashMul, hashMod, fills);
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
            factory = uniswapV3PlasmaFactory;
            initHash = uniswapV3InitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else {
            revertUnknownForkId(forkId);
        }
    }

    function _EVC() internal pure override returns (IEVC) {
        return IEVC(0x7bdbd0A7114aA42CA957F292145F6a931a345583);
    }
}
