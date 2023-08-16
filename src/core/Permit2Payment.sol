// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

abstract contract Permit2Payment {
    /// @dev Permit2 address
    ISignatureTransfer private immutable PERMIT2;

    constructor(address permit2) {
        PERMIT2 = ISignatureTransfer(permit2);
    }

    function permit2TransferFrom(
        ISignatureTransfer.PermitTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails memory transferDetails,
        address from,
        bytes memory sig
    ) internal {
        PERMIT2.permitTransferFrom(permit, transferDetails, from, sig);
    }

    function permit2WitnessTransferFrom(
        ISignatureTransfer.PermitTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails memory transferDetails,
        address from,
        bytes memory sig,
        bytes32 witness,
        string memory witnessTypeString
    ) internal {
        PERMIT2.permitWitnessTransferFrom(permit, transferDetails, from, witness, witnessTypeString, sig);
    }

    function permit2TransferFrom(
        ISignatureTransfer.PermitBatchTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails[] memory transferDetails,
        address from,
        bytes memory sig
    ) internal {
        PERMIT2.permitTransferFrom(permit, transferDetails, from, sig);
    }
}
