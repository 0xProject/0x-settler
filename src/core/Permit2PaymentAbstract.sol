// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {AbstractContext} from "../Context.sol";

import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

abstract contract Permit2PaymentAbstract is AbstractContext {
    string internal constant TOKEN_PERMISSIONS_TYPE = "TokenPermissions(address token,uint256 amount)";

    function isRestrictedTarget(address) internal view virtual returns (bool);

    function _permitToTransferDetails(ISignatureTransfer.PermitTransferFrom memory permit, address recipient)
        internal
        pure
        virtual
        returns (ISignatureTransfer.SignatureTransferDetails memory transferDetails, address token, uint256 amount);

    function _transferFrom(
        ISignatureTransfer.PermitTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails memory transferDetails,
        address from,
        bytes32 witness,
        string memory witnessTypeString,
        bytes memory sig,
        bool isForwarded
    ) internal virtual;

    function _transferFrom(
        ISignatureTransfer.PermitTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails memory transferDetails,
        address from,
        bytes32 witness,
        string memory witnessTypeString,
        bytes memory sig
    ) internal virtual;

    function _transferFrom(
        ISignatureTransfer.PermitTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails memory transferDetails,
        address from,
        bytes memory sig,
        bool isForwarded
    ) internal virtual;

    function _transferFrom(
        ISignatureTransfer.PermitTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails memory transferDetails,
        address from,
        bytes memory sig
    ) internal virtual;

    function _setOperatorAndCall(
        address target,
        bytes memory data,
        uint32 selector,
        function (bytes calldata) internal returns (bytes memory) callback
    ) internal virtual returns (bytes memory);

    function _setCallbackAndCall(
        address target,
        bytes memory data,
        uint32 selector,
        function (bytes calldata) internal returns (bytes memory) callback
    ) internal virtual returns (bytes memory);

    modifier metaTx(address msgSender, bytes32 witness) virtual;

    function _allowanceHolderTransferFrom(address token, address owner, address recipient, uint256 amount)
        internal
        virtual;
}
