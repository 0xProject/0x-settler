// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {Panic} from "../utils/Panic.sol";

abstract contract Permit2Payment {
    /// @dev Permit2 address
    ISignatureTransfer private immutable PERMIT2;
    address private immutable FEE_RECIPIENT;

    string internal constant TOKEN_PERMISSIONS_TYPE = "TokenPermissions(address token,uint256 amount)";

    constructor(address permit2, address feeRecipient) {
        PERMIT2 = ISignatureTransfer(permit2);
        FEE_RECIPIENT = feeRecipient;
    }

    error FeeTokenMismatch(address paymentToken, address feeToken);

    function _permitToTransferDetails(ISignatureTransfer.PermitBatchTransferFrom memory permit, address recipient)
        internal
        view
        returns (ISignatureTransfer.SignatureTransferDetails[] memory transferDetails, address token, uint256 amount)
    {
        // TODO: allow multiple fees
        if (permit.permitted.length > 2) {
            Panic.panic(Panic.ARRAY_OUT_OF_BOUNDS);
        }
        transferDetails = new ISignatureTransfer.SignatureTransferDetails[](permit.permitted.length);
        transferDetails[0] = ISignatureTransfer.SignatureTransferDetails({
            to: recipient,
            requestedAmount: amount = permit.permitted[0].amount
        });
        token = permit.permitted[0].token;
        if (permit.permitted.length > 1) {
            if (token != permit.permitted[1].token) {
                revert FeeTokenMismatch(token, permit.permitted[1].token);
            }
            transferDetails[1] = ISignatureTransfer.SignatureTransferDetails({
                to: FEE_RECIPIENT,
                requestedAmount: permit.permitted[1].amount
            });
        }
    }

    function _permitToTransferDetails(ISignatureTransfer.PermitTransferFrom memory permit, address recipient)
        internal
        pure
        returns (ISignatureTransfer.SignatureTransferDetails memory transferDetails, address token, uint256 amount)
    {
        transferDetails.to = recipient;
        transferDetails.requestedAmount = amount = permit.permitted.amount;
        token = permit.permitted.token;
    }

    function _permit2WitnessTransferFrom(
        ISignatureTransfer.PermitBatchTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails[] memory transferDetails,
        address from,
        bytes32 witness,
        string memory witnessTypeString,
        bytes memory sig
    ) internal {
        PERMIT2.permitWitnessTransferFrom(permit, transferDetails, from, witness, witnessTypeString, sig);
    }

    function _permit2WitnessTransferFrom(
        ISignatureTransfer.PermitTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails memory transferDetails,
        address from,
        bytes32 witness,
        string memory witnessTypeString,
        bytes memory sig
    ) internal {
        PERMIT2.permitWitnessTransferFrom(permit, transferDetails, from, witness, witnessTypeString, sig);
    }

    function _permit2TransferFrom(
        ISignatureTransfer.PermitBatchTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails[] memory transferDetails,
        address from,
        bytes memory sig
    ) internal {
        PERMIT2.permitTransferFrom(permit, transferDetails, from, sig);
    }

    function _permit2TransferFrom(
        ISignatureTransfer.PermitTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails memory transferDetails,
        address from,
        bytes memory sig
    ) internal {
        PERMIT2.permitTransferFrom(permit, transferDetails, from, sig);
    }
}
