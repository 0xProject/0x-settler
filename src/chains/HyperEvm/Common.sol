// SPDX-License-Identifier: MIT
pragma solidity =0.8.34;

import {SettlerBase} from "../../SettlerBase.sol";
import {Attest} from "../../core/Attest.sol";
import {BlockHyperEvmSystemContracts} from "./BlockHyperEvmSystemContracts.sol";

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
import {prjxV3Factory, prjxV3InitHash, prjxV3ForkId} from "../../core/univ3forks/PrjxV3.sol";

// Solidity inheritance is stupid
import {SettlerAbstract, SettlerSwapAbstract} from "../../SettlerAbstract.sol";
import {Permit2PaymentAbstract} from "../../core/Permit2PaymentAbstract.sol";

abstract contract HyperEvmMixin is FreeMemory, SettlerBase, BlockHyperEvmSystemContracts, Bebop {
    constructor() {
        assert(block.chainid == _chainId() || block.chainid == 31337);
    }

    function _chainId() internal pure override returns (uint256) {
        return 999;
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
        } else if (forkId == prjxV3ForkId) {
            factory = prjxV3Factory;
            initHash = prjxV3InitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else {
            revertUnknownForkId(forkId);
        }
    }

    // I hate Solidity inheritance
    function _hasRecipientCheck()
        internal
        pure
        virtual
        override(SettlerAbstract, SettlerBase, BlockHyperEvmSystemContracts)
        returns (bool)
    {
        return super._hasRecipientCheck();
    }

    function _checkRecipient(address sender, address recipient, IERC20 buyToken)
        internal
        view
        virtual
        override(SettlerAbstract, SettlerBase, BlockHyperEvmSystemContracts)
    {
        super._checkRecipient(sender, recipient, buyToken);
    }

    function _isRestrictedTarget(address target)
        internal
        view
        virtual
        override(Bebop, BlockHyperEvmSystemContracts, Permit2PaymentAbstract)
        returns (bool)
    {
        return super._isRestrictedTarget(target);
    }
}

// `Attest` is listed last so that candidate selection sits above the chain actions in the
// linearization; see `Select`.
abstract contract HyperEvmCommon is HyperEvmMixin, Attest {
    function _dispatch(uint256 i, uint256 action, bytes calldata data, AllowedSlippage memory slippage)
        internal
        virtual
        override(HyperEvmMixin, Attest)
        returns (bool)
    {
        return super._dispatch(i, action, data, slippage);
    }

    function _isRestrictedTarget(address target)
        internal
        view
        virtual
        override(HyperEvmMixin, Permit2PaymentAbstract)
        returns (bool)
    {
        return super._isRestrictedTarget(target);
    }

    function _fallback(bytes calldata data)
        internal
        virtual
        override(Permit2PaymentAbstract, Attest)
        returns (bool success, bytes memory returndata)
    {
        return super._fallback(data);
    }

    function _hasRecipientCheck() internal pure virtual override(HyperEvmMixin, SettlerBase) returns (bool) {
        return super._hasRecipientCheck();
    }

    function _checkRecipient(address sender, address recipient, IERC20 buyToken)
        internal
        view
        virtual
        override(HyperEvmMixin, SettlerBase)
    {
        super._checkRecipient(sender, recipient, buyToken);
    }
}
