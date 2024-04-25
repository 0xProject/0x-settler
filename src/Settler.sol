// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20, IERC20Meta} from "./IERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

import {Permit2PaymentBase} from "./core/Permit2Payment.sol";
import {Permit2PaymentAbstract} from "./core/Permit2PaymentAbstract.sol";

import {AllowanceHolderContext} from "./allowanceholder/AllowanceHolderContext.sol";
import {CalldataDecoder, SettlerBase} from "./SettlerBase.sol";
import {UnsafeMath} from "./utils/UnsafeMath.sol";

import {ISettlerActions} from "./ISettlerActions.sol";

/// @custom:security-contact security@0x.org
contract Settler is AllowanceHolderContext, SettlerBase {
    using UnsafeMath for uint256;
    using CalldataDecoder for bytes[];

    constructor(address uniFactory, address dai) SettlerBase(uniFactory, dai) {}

    function _hasMetaTxn() internal pure override returns (bool) {
        return false;
    }

    function isRestrictedTarget(address target)
        internal
        pure
        override(Permit2PaymentAbstract, Permit2PaymentBase)
        returns (bool)
    {
        return target == address(_ALLOWANCE_HOLDER) || super.isRestrictedTarget(target);
    }

    function _allowanceHolderTransferFrom(address token, address owner, address recipient, uint256 amount)
        internal
        override
    {
        _ALLOWANCE_HOLDER.transferFrom(token, owner, recipient, amount);
    }

    function _otcVIP(bytes calldata data) internal DANGEROUS_freeMemory {
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

        fillOtcOrder(recipient, makerPermit, maker, makerSig, takerPermit, takerSig);
    }

    function _uniV3VIP(bytes calldata data) internal DANGEROUS_freeMemory {
        (
            address recipient,
            uint256 amountOutMin,
            bytes memory path,
            ISignatureTransfer.PermitTransferFrom memory permit,
            bytes memory sig
        ) = abi.decode(data, (address, uint256, bytes, ISignatureTransfer.PermitTransferFrom, bytes));

        sellToUniswapV3VIP(recipient, path, amountOutMin, permit, sig);
    }

    function _curveTricryptoVIP(bytes calldata data) internal DANGEROUS_freeMemory {
        (
            address recipient,
            uint80 poolInfo,
            uint256 minBuyAmount,
            ISignatureTransfer.PermitTransferFrom memory permit,
            bytes memory sig
        ) = abi.decode(data, (address, uint80, uint256, ISignatureTransfer.PermitTransferFrom, bytes));
        sellToCurveTricryptoVIP(recipient, poolInfo, minBuyAmount, permit, sig);
    }

    function _pancakeSwapV3VIP(bytes calldata data) internal DANGEROUS_freeMemory {
        (
            address recipient,
            uint256 amountOutMin,
            bytes memory path,
            ISignatureTransfer.PermitTransferFrom memory permit,
            bytes memory sig
        ) = abi.decode(data, (address, uint256, bytes, ISignatureTransfer.PermitTransferFrom, bytes));

        sellToPancakeSwapV3VIP(recipient, path, amountOutMin, permit, sig);
    }

    function _solidlyV3VIP(bytes calldata data) internal DANGEROUS_freeMemory {
        (
            address recipient,
            uint256 amountOutMin,
            bytes memory path,
            ISignatureTransfer.PermitTransferFrom memory permit,
            bytes memory sig
        ) = abi.decode(data, (address, uint256, bytes, ISignatureTransfer.PermitTransferFrom, bytes));

        sellToSolidlyV3VIP(recipient, path, amountOutMin, permit, sig);
    }

    function execute(bytes[] calldata actions, AllowedSlippage calldata slippage) public payable {
        if (actions.length != 0) {
            (bytes4 action, bytes calldata data) = actions.decodeCall(0);
            if (action == ISettlerActions.OTC_VIP.selector) {
                _otcVIP(data);
            } else if (action == ISettlerActions.UNISWAPV3_VIP.selector) {
                _uniV3VIP(data);
            } else if (action == ISettlerActions.CURVE_TRICRYPTO_VIP.selector) {
                _curveTricryptoVIP(data);
            } else if (action == ISettlerActions.PANCAKESWAPV3_VIP.selector) {
                _pancakeSwapV3VIP(data);
            } else if (action == ISettlerActions.SOLIDLYV3_VIP.selector) {
                _solidlyV3VIP(data);
            } else {
                _dispatch(0, action, data, _msgSender());
            }
        }

        for (uint256 i = 1; i < actions.length; i = i.unsafeInc()) {
            (bytes4 action, bytes calldata data) = actions.decodeCall(i);
            _dispatch(i, action, data, _msgSender());
        }

        _checkSlippageAndTransfer(slippage);
    }
}
