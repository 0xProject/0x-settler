// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20, IERC20Meta} from "./IERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

import {Permit2PaymentBase} from "./core/Permit2Payment.sol";
import {Permit2PaymentAbstract} from "./core/Permit2PaymentAbstract.sol";

import {AbstractContext} from "./Context.sol";
import {AllowanceHolderContext} from "./allowanceholder/AllowanceHolderContext.sol";
import {CalldataDecoder, SettlerBase} from "./SettlerBase.sol";
import {UnsafeMath} from "./utils/UnsafeMath.sol";

import {ISettlerActions} from "./ISettlerActions.sol";
import {ActionInvalid} from "./core/SettlerErrors.sol";

abstract contract Settler is AllowanceHolderContext, SettlerBase {
    using UnsafeMath for uint256;
    using CalldataDecoder for bytes[];

    function _hasMetaTxn() internal pure override returns (bool) {
        return false;
    }

    function _isRestrictedTarget(address target)
        internal
        pure
        virtual
        override(Permit2PaymentAbstract, Permit2PaymentBase)
        returns (bool)
    {
        return target == address(_ALLOWANCE_HOLDER) || super._isRestrictedTarget(target);
    }

    function _allowanceHolderTransferFrom(address token, address owner, address recipient, uint256 amount)
        internal
        override
    {
        // `owner` is always `_msgSender()` here, but we leave it to Permit2Payment.sol to enforce that
        _ALLOWANCE_HOLDER.transferFrom(token, owner, recipient, amount);
    }

    function _operator() internal view override returns (address) {
        return AllowanceHolderContext._msgSender();
    }

    function _msgSender()
        internal
        view
        virtual
        // Solidity inheritance is so stupid
        override(Permit2PaymentBase, AllowanceHolderContext, AbstractContext)
        returns (address)
    {
        return Permit2PaymentBase._msgSender();
    }

    function _dispatchVIP(bytes4 action, bytes calldata data) internal virtual returns (bool) {
        if (action == ISettlerActions.RFQ_VIP.selector) {
            (
                address recipient,
                ISignatureTransfer.PermitTransferFrom memory makerPermit,
                address maker,
                bytes memory makerSig,
                ISignatureTransfer.PermitTransferFrom memory takerPermit,
                bytes memory takerSig
            ) = abi.decode(
                data,
                (
                    address,
                    ISignatureTransfer.PermitTransferFrom,
                    address,
                    bytes,
                    ISignatureTransfer.PermitTransferFrom,
                    bytes
                )
            );

            fillRfqOrderVIP(recipient, makerPermit, maker, makerSig, takerPermit, takerSig);
        } else if (action == ISettlerActions.UNISWAPV3_VIP.selector) {
            (
                address recipient,
                bytes memory path,
                ISignatureTransfer.PermitTransferFrom memory permit,
                bytes memory sig,
                uint256 amountOutMin
            ) = abi.decode(data, (address, bytes, ISignatureTransfer.PermitTransferFrom, bytes, uint256));

            sellToUniswapV3VIP(recipient, path, permit, sig, amountOutMin);
        } else {
            return false;
        }
        return true;
    }

    function execute(bytes[] calldata actions, AllowedSlippage calldata slippage) public payable takerSubmitted {
        for (uint256 i; i < actions.length; i = i.unsafeInc()) {
            (bytes4 action, bytes calldata data) = actions.decodeCall(i);
            if (!((i == 0 && _dispatchVIP(action, data)) || _dispatch(i, action, data))) {
                revert ActionInvalid(i, action, data);
            }
        }

        _checkSlippageAndTransfer(slippage);
    }
}
