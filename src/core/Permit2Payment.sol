// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {ForwarderNotAllowed, InvalidSignatureLen} from "./SettlerErrors.sol";
import {ContextAbstract} from "../Context.sol";
import {AllowanceHolderContext} from "../AllowanceHolderContext.sol";
import {IAllowanceHolder} from "../IAllowanceHolder.sol";

import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {Panic} from "../utils/Panic.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";


library UnsafeArray {
    function unsafeGet(IAllowanceHolder.TransferDetails[] memory a, uint256 i)
        internal
        pure
        returns (IAllowanceHolder.TransferDetails memory r)
    {
        assembly ("memory-safe") {
            r := mload(add(add(a, 0x20), shl(5, i)))
        }
    }

    function unsafeGet(ISignatureTransfer.TokenPermissions[] memory a, uint256 i)
        internal
        pure
        returns (ISignatureTransfer.TokenPermissions memory r)
    {
        assembly ("memory-safe") {
            r := mload(add(add(a, 0x20), shl(5, i)))
        }
    }

    function unsafeGet(ISignatureTransfer.SignatureTransferDetails[] memory a, uint256 i)
        internal
        pure
        returns (ISignatureTransfer.SignatureTransferDetails memory r)
    {
        assembly ("memory-safe") {
            r := mload(add(add(a, 0x20), shl(5, i)))
        }
    }
}

abstract contract Permit2PaymentAbstract is ContextAbstract {
    string internal constant TOKEN_PERMISSIONS_TYPE = "TokenPermissions(address token,uint256 amount)";

    function isRestrictedTarget(address) internal view virtual returns (bool);

    function _permitToTransferDetails(ISignatureTransfer.PermitBatchTransferFrom memory permit, address recipient)
        internal
        view
        virtual
        returns (ISignatureTransfer.SignatureTransferDetails[] memory transferDetails, address token, uint256 amount);

    function _permitToTransferDetails(ISignatureTransfer.PermitTransferFrom memory permit, address recipient)
        internal
        pure
        virtual
        returns (ISignatureTransfer.SignatureTransferDetails memory transferDetails, address token, uint256 amount);

    function _transferFrom(
        ISignatureTransfer.PermitBatchTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails[] memory transferDetails,
        address from,
        bytes32 witness,
        string memory witnessTypeString,
        bytes memory sig,
        bool isForwarded
    ) internal virtual;

    function _transferFrom(
        ISignatureTransfer.PermitBatchTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails[] memory transferDetails,
        address from,
        bytes32 witness,
        string memory witnessTypeString,
        bytes memory sig
    ) internal virtual;

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
        ISignatureTransfer.PermitBatchTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails[] memory transferDetails,
        address from,
        bytes memory sig,
        bool isForwarded
    ) internal virtual;

    function _transferFrom(
        ISignatureTransfer.PermitBatchTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails[] memory transferDetails,
        address from,
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
}

abstract contract Permit2Payment is Permit2PaymentAbstract, AllowanceHolderContext {
    using UnsafeMath for uint256;
    using UnsafeArray for IAllowanceHolder.TransferDetails[];
    using UnsafeArray for ISignatureTransfer.TokenPermissions[];
    using UnsafeArray for ISignatureTransfer.SignatureTransferDetails[];

    /// @dev Permit2 address
    ISignatureTransfer private immutable _PERMIT2;
    address private immutable _FEE_RECIPIENT;

    function isRestrictedTarget(address target) internal view override returns (bool) {
        return target == address(_PERMIT2) || target == address(allowanceHolder);
    }

    constructor(address permit2, address feeRecipient, address allowanceHolder)
        AllowanceHolderContext(allowanceHolder)
    {
        _PERMIT2 = ISignatureTransfer(permit2);
        _FEE_RECIPIENT = feeRecipient;
    }

    error FeeTokenMismatch(address paymentToken, address feeToken);

    function _permitToTransferDetails(ISignatureTransfer.PermitBatchTransferFrom memory permit, address recipient)
        internal
        view
        override
        returns (ISignatureTransfer.SignatureTransferDetails[] memory transferDetails, address token, uint256 amount)
    {
        // TODO: allow multiple fees
        if (permit.permitted.length > 2) {
            Panic.panic(Panic.ARRAY_OUT_OF_BOUNDS);
        }
        transferDetails = new ISignatureTransfer.SignatureTransferDetails[](permit.permitted.length);
        {
            ISignatureTransfer.SignatureTransferDetails memory transferDetail = transferDetails.unsafeGet(0);
            transferDetail.to = recipient;
            ISignatureTransfer.TokenPermissions memory permitted = permit.permitted.unsafeGet(0);
            transferDetail.requestedAmount = amount = permitted.amount;
            token = permitted.token;
        }
        if (permit.permitted.length > 1) {
            ISignatureTransfer.TokenPermissions memory permitted = permit.permitted.unsafeGet(1);
            if (token != permitted.token) {
                revert FeeTokenMismatch(token, permitted.token);
            }
            ISignatureTransfer.SignatureTransferDetails memory transferDetail = transferDetails.unsafeGet(1);
            transferDetail.to = _FEE_RECIPIENT;
            transferDetail.requestedAmount = permitted.amount;
        }
    }

    function _permitToTransferDetails(ISignatureTransfer.PermitTransferFrom memory permit, address recipient)
        internal
        pure
        override
        returns (ISignatureTransfer.SignatureTransferDetails memory transferDetails, address token, uint256 amount)
    {
        transferDetails.to = recipient;
        transferDetails.requestedAmount = amount = permit.permitted.amount;
        token = permit.permitted.token;
    }

    function _formatForAllowanceHolder(
        ISignatureTransfer.PermitBatchTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails[] memory transferDetails
    ) private pure returns (IAllowanceHolder.TransferDetails[] memory result) {
        uint256 length;
        // TODO: allow multiple fees
        if ((length = permit.permitted.length) != transferDetails.length || length > 2) {
            Panic.panic(Panic.ARRAY_OUT_OF_BOUNDS);
        }
        result = new IAllowanceHolder.TransferDetails[](length);
        for (uint256 i; i < length; i = i.unsafeInc()) {
            ISignatureTransfer.TokenPermissions memory permitted = permit.permitted.unsafeGet(i);
            ISignatureTransfer.SignatureTransferDetails memory oldDetail = transferDetails.unsafeGet(i);
            IAllowanceHolder.TransferDetails memory newDetail = result.unsafeGet(i);

            newDetail.token = permitted.token;
            newDetail.recipient = oldDetail.to;
            newDetail.amount = oldDetail.requestedAmount;
        }
    }

    function _formatForAllowanceHolder(
        ISignatureTransfer.PermitTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails memory transferDetails
    ) private pure returns (IAllowanceHolder.TransferDetails[] memory result) {
        result = new IAllowanceHolder.TransferDetails[](1);
        IAllowanceHolder.TransferDetails memory newDetail = result.unsafeGet(0);
        newDetail.token = permit.permitted.token;
        newDetail.recipient = transferDetails.to;
        newDetail.amount = transferDetails.requestedAmount;
    }

    function _transferFrom(
        ISignatureTransfer.PermitBatchTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails[] memory transferDetails,
        address from,
        bytes32 witness,
        string memory witnessTypeString,
        bytes memory sig,
        bool isForwarded
    ) internal override {
        if (isForwarded) revert ForwarderNotAllowed();
        _PERMIT2.permitWitnessTransferFrom(permit, transferDetails, from, witness, witnessTypeString, sig);
    }

    function _transferFrom(
        ISignatureTransfer.PermitBatchTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails[] memory transferDetails,
        address from,
        bytes32 witness,
        string memory witnessTypeString,
        bytes memory sig
    ) internal override {
        _transferFrom(permit, transferDetails, from, witness, witnessTypeString, sig, _isForwarded());
    }

    function _transferFrom(
        ISignatureTransfer.PermitTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails memory transferDetails,
        address from,
        bytes32 witness,
        string memory witnessTypeString,
        bytes memory sig,
        bool isForwarded
    ) internal override {
        if (isForwarded) revert ForwarderNotAllowed();
        _PERMIT2.permitWitnessTransferFrom(permit, transferDetails, from, witness, witnessTypeString, sig);
    }

    function _transferFrom(
        ISignatureTransfer.PermitTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails memory transferDetails,
        address from,
        bytes32 witness,
        string memory witnessTypeString,
        bytes memory sig
    ) internal override {
        _transferFrom(permit, transferDetails, from, witness, witnessTypeString, sig, _isForwarded());
    }

    function _transferFrom(
        ISignatureTransfer.PermitBatchTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails[] memory transferDetails,
        address from,
        bytes memory sig,
        bool isForwarded
    ) internal override {
        if (isForwarded) {
            if (sig.length != 0) revert InvalidSignatureLen();
            allowanceHolder.holderTransferFrom(from, _formatForAllowanceHolder(permit, transferDetails));
        } else {
            _PERMIT2.permitTransferFrom(permit, transferDetails, from, sig);
        }
    }

    function _transferFrom(
        ISignatureTransfer.PermitBatchTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails[] memory transferDetails,
        address from,
        bytes memory sig
    ) internal override {
        _transferFrom(permit, transferDetails, from, sig, _isForwarded());
    }

    function _transferFrom(
        ISignatureTransfer.PermitTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails memory transferDetails,
        address from,
        bytes memory sig,
        bool isForwarded
    ) internal override {
        if (isForwarded) {
            if (sig.length != 0) revert InvalidSignatureLen();
            allowanceHolder.holderTransferFrom(from, _formatForAllowanceHolder(permit, transferDetails));
        } else {
            _PERMIT2.permitTransferFrom(permit, transferDetails, from, sig);
        }
    }

    function _transferFrom(
        ISignatureTransfer.PermitTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails memory transferDetails,
        address from,
        bytes memory sig
    ) internal override {
        _transferFrom(permit, transferDetails, from, sig, _isForwarded());
    }
}
