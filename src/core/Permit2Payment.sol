// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

abstract contract Permit2Payment {
    /// @dev Permit2 address
    ISignatureTransfer private immutable PERMIT2;

    string internal constant TOKEN_PERMISSIONS_TYPE = "TokenPermissions(address token,uint256 amount)";

    constructor(address permit2) {
        PERMIT2 = ISignatureTransfer(permit2);
    }

    function _permitToTransferDetails(ISignatureTransfer.PermitBatchTransferFrom memory permit, address recipient)
        internal
        pure
        returns (ISignatureTransfer.SignatureTransferDetails[] memory transferDetails, address token, uint256 amount)
    {
        // TODO: allow multiple fees
        require(permit.permitted.length <= 2, "Settler: Invalid batch Permit2 -- too many fees");
        transferDetails = new ISignatureTransfer.SignatureTransferDetails[](permit.permitted.length);
        transferDetails[0] = ISignatureTransfer.SignatureTransferDetails({
            to: recipient,
            requestedAmount: amount = permit.permitted[0].amount
        });
        token = permit.permitted[0].token;
        if (permit.permitted.length > 1) {
            require(token == permit.permitted[1].token, "Settler: Invalid batch Permit2 -- fee token address mismatch");
            // TODO fee recipient
            transferDetails[1] = ISignatureTransfer.SignatureTransferDetails({
                to: 0x2222222222222222222222222222222222222222,
                requestedAmount: permit.permitted[1].amount
            });
        }
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

    function _permit2TransferFrom(
        ISignatureTransfer.PermitBatchTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails[] memory transferDetails,
        address from,
        bytes memory sig
    ) internal {
        PERMIT2.permitTransferFrom(permit, transferDetails, from, sig);
    }
}
