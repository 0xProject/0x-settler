// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {ForwarderNotAllowed, InvalidSignatureLen} from "./SettlerErrors.sol";
import {AbstractContext} from "../Context.sol";
import {AllowanceHolderContext} from "../allowanceholder/AllowanceHolderContext.sol";

import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {Panic} from "../utils/Panic.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";

library UnsafeArray {
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
}

/// @dev Batch support for Permit2 payments
/// === WARNING: UNUSED ===
abstract contract Permit2BatchPaymentAbstract is AbstractContext {
    string internal constant TOKEN_PERMISSIONS_TYPE = "TokenPermissions(address token,uint256 amount)";

    error FeeTokenMismatch(address paymentToken, address feeToken);

    function isRestrictedTarget(address) internal view virtual returns (bool);

    function _permitToTransferDetails(ISignatureTransfer.PermitBatchTransferFrom memory permit, address recipient)
        internal
        view
        virtual
        returns (ISignatureTransfer.SignatureTransferDetails[] memory transferDetails, address token, uint256 amount);

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
}

abstract contract Permit2PaymentBase is AllowanceHolderContext, Permit2PaymentAbstract {
    /// @dev Permit2 address
    ISignatureTransfer internal immutable _PERMIT2;

    function isRestrictedTarget(address target) internal view override returns (bool) {
        return target == address(_PERMIT2) || target == address(allowanceHolder);
    }

    constructor(address permit2, address allowanceHolder) AllowanceHolderContext(allowanceHolder) {
        _PERMIT2 = ISignatureTransfer(permit2);
    }
}

abstract contract Permit2BatchPaymentBase is AllowanceHolderContext, Permit2BatchPaymentAbstract {
    /// @dev Permit2 address
    ISignatureTransfer internal immutable _PERMIT2;

    function isRestrictedTarget(address target) internal view override returns (bool) {
        return target == address(_PERMIT2) || target == address(allowanceHolder);
    }

    constructor(address permit2, address allowanceHolder) AllowanceHolderContext(allowanceHolder) {
        _PERMIT2 = ISignatureTransfer(permit2);
    }
}

/// @dev Batch support for Permit2 payments
/// === WARNING: UNUSED ===
abstract contract Permit2BatchPayment is Permit2BatchPaymentBase {
    using UnsafeMath for uint256;
    using UnsafeArray for ISignatureTransfer.TokenPermissions[];
    using UnsafeArray for ISignatureTransfer.SignatureTransferDetails[];

    constructor(address permit2, address allowanceHolder) Permit2BatchPaymentBase(permit2, allowanceHolder) {}

    function _permitToTransferDetails(ISignatureTransfer.PermitBatchTransferFrom memory permit, address recipient)
        internal
        pure
        override
        returns (ISignatureTransfer.SignatureTransferDetails[] memory transferDetails, address token, uint256 amount)
    {
        // TODO: fees
        if (permit.permitted.length != 1) {
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
        ISignatureTransfer.PermitBatchTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails[] memory transferDetails,
        address from,
        bytes memory sig,
        bool isForwarded
    ) internal override {
        if (isForwarded) {
            if (sig.length != 0) revert InvalidSignatureLen();
            {
                uint256 length;
                if ((length = permit.permitted.length) != transferDetails.length) {
                    Panic.panic(Panic.ARRAY_OUT_OF_BOUNDS);
                }
                if (length != 1) {
                    Panic.panic(Panic.ARRAY_OUT_OF_BOUNDS);
                }
            }
            allowanceHolder.transferFrom(
                permit.permitted.unsafeGet(0).token,
                from,
                transferDetails.unsafeGet(0).to,
                transferDetails.unsafeGet(0).requestedAmount
            );
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
}

abstract contract Permit2Payment is Permit2PaymentBase {
    using UnsafeMath for uint256;
    using UnsafeArray for ISignatureTransfer.TokenPermissions[];
    using UnsafeArray for ISignatureTransfer.SignatureTransferDetails[];

    constructor(address permit2, address allowanceHolder) Permit2PaymentBase(permit2, allowanceHolder) {}

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
        ISignatureTransfer.PermitTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails memory transferDetails,
        address from,
        bytes memory sig,
        bool isForwarded
    ) internal override {
        if (isForwarded) {
            if (sig.length != 0) revert InvalidSignatureLen();
            allowanceHolder.transferFrom(
                permit.permitted.token, from, transferDetails.to, transferDetails.requestedAmount
            );
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
