// SPDX-License-Identifier: MIT
pragma solidity =0.8.34;

import {SettlerBase} from "../../SettlerBase.sol";
import {Select} from "../../core/Select.sol";
import {BlockTempoSystemContracts} from "./BlockTempoSystemContracts.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {FreeMemory} from "../../utils/FreeMemory.sol";

import {UniswapV4} from "../../core/UniswapV4.sol";
import {IPoolManager} from "../../core/UniswapV4Types.sol";

import {ISettlerActions} from "../../ISettlerActions.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {revertUnknownForkId} from "../../core/SettlerErrors.sol";

import {
    uniswapV3TempoFactory,
    uniswapV3InitHash,
    uniswapV3ForkId,
    IUniswapV3Callback
} from "../../core/univ3forks/UniswapV3.sol";

import {uniswapV4TempoPoolManager, uniswapV4ForkId} from "../../core/univ4forks/UniswapV4.sol";

// Solidity inheritance is stupid
import {SettlerAbstract, SettlerSwapAbstract} from "../../SettlerAbstract.sol";
import {SettlerBase} from "../../SettlerBase.sol";
import {Permit2PaymentAbstract} from "../../core/Permit2PaymentAbstract.sol";

abstract contract TempoMixin is FreeMemory, SettlerBase, BlockTempoSystemContracts, UniswapV4 {
    constructor() {
        assert(block.chainid == _chainId() || block.chainid == 31337);
    }

    function _chainId() internal pure override returns (uint256) {
        return 4217;
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
        } else if (action == uint32(ISettlerActions.UNISWAPV4.selector)) {
            (
                address recipient,
                IERC20 sellToken,
                uint256 ppm,
                uint8 forkId,
                bool feeOnTransfer,
                uint256 hashMul,
                uint256 hashMod,
                bytes memory fills,
                uint256 amountOutMin
            ) = abi.decode(data, (address, IERC20, uint256, uint8, bool, uint256, uint256, bytes, uint256));

            sellToUniswapV4(recipient, sellToken, ppm, forkId, feeOnTransfer, hashMul, hashMod, fills, amountOutMin);
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
            factory = uniswapV3TempoFactory;
            initHash = uniswapV3InitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else {
            revertUnknownForkId(forkId);
        }
    }

    function _uniV4ForkInfo(uint8 forkId) internal pure override returns (IPoolManager poolManager) {
        if (forkId == uniswapV4ForkId) {
            poolManager = uniswapV4TempoPoolManager;
        } else {
            revertUnknownForkId(forkId);
        }
    }

    // I hate Solidity inheritance
    function _hasRecipientCheck()
        internal
        pure
        virtual
        override(SettlerAbstract, SettlerBase, BlockTempoSystemContracts)
        returns (bool)
    {
        return super._hasRecipientCheck();
    }

    function _recipientCheckNeedsToken()
        internal
        pure
        virtual
        override(SettlerAbstract, SettlerBase, BlockTempoSystemContracts)
        returns (bool)
    {
        return super._recipientCheckNeedsToken();
    }

    function _checkRecipient(address sender, address recipient, IERC20 buyToken)
        internal
        view
        virtual
        override(SettlerAbstract, SettlerBase, BlockTempoSystemContracts)
    {
        super._checkRecipient(sender, recipient, buyToken);
    }

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
        override(Permit2PaymentAbstract, BlockTempoSystemContracts)
        returns (bool)
    {
        return super._isRestrictedTarget(target);
    }
}

// `Select` is listed last so that candidate selection sits above the chain actions in the
// linearization; see `Select`.
abstract contract TempoCommon is TempoMixin, Select {
    function _dispatch(uint256 i, uint256 action, bytes calldata data, AllowedSlippage memory slippage)
        internal
        virtual
        override(TempoMixin, Select)
        returns (bool)
    {
        return super._dispatch(i, action, data, slippage);
    }

    function _isRestrictedTarget(address target)
        internal
        view
        virtual
        override(TempoMixin, Permit2PaymentAbstract)
        returns (bool)
    {
        return super._isRestrictedTarget(target);
    }

    function _fallback(bytes calldata data)
        internal
        virtual
        override(TempoMixin, Permit2PaymentAbstract)
        returns (bool success, bytes memory returndata)
    {
        return super._fallback(data);
    }

    function _hasRecipientCheck() internal pure virtual override(TempoMixin, SettlerBase) returns (bool) {
        return super._hasRecipientCheck();
    }

    function _recipientCheckNeedsToken() internal pure virtual override(TempoMixin, SettlerBase) returns (bool) {
        return super._recipientCheckNeedsToken();
    }

    function _checkRecipient(address sender, address recipient, IERC20 buyToken)
        internal
        view
        virtual
        override(TempoMixin, SettlerBase)
    {
        super._checkRecipient(sender, recipient, buyToken);
    }
}
