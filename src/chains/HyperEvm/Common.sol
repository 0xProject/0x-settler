// SPDX-License-Identifier: MIT
pragma solidity =0.8.34;

import {SettlerBase} from "../../SettlerBase.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {Bebop} from "../../core/Bebop.sol";
import {FreeMemory} from "../../utils/FreeMemory.sol";

import {ISettlerActions} from "../../ISettlerActions.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {revertUnknownForkId} from "../../core/SettlerErrors.sol";

import {IUniswapV3Callback} from "../../core/univ3forks/UniswapV3.sol";
import {kittenSwapFactory, kittenSwapInitHash, kittenSwapForkId} from "../../core/univ3forks/KittenSwap.sol";
import {hybraFactory, hybraInitHash, hybraForkId} from "../../core/univ3forks/Hybra.sol";
import {
    hyperSwapFactory,
    hyperSwapInitHash,
    hyperSwapForkId,
    IHyperswapV3SwapCallback
} from "../../core/univ3forks/HyperSwap.sol";

// Solidity inheritance is stupid
import {SettlerAbstract} from "../../SettlerAbstract.sol";
import {Permit2PaymentAbstract} from "../../core/Permit2PaymentAbstract.sol";

abstract contract HyperEvmMixin is FreeMemory, SettlerBase, Bebop {
    constructor() {
        assert(block.chainid == 999 || block.chainid == 31337);
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
        if (forkId == kittenSwapForkId) {
            factory = kittenSwapFactory;
            initHash = kittenSwapInitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else if (forkId == hybraForkId) {
            factory = hybraFactory;
            initHash = hybraInitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else if (forkId == hyperSwapForkId) {
            factory = hyperSwapFactory;
            initHash = hyperSwapInitHash;
            callbackSelector = uint32(IHyperswapV3SwapCallback.hyperswapV3SwapCallback.selector);
        } else {
            revertUnknownForkId(forkId);
        }
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
