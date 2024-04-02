// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {ForwarderNotAllowed, InvalidSignatureLen, ConfusedDeputy} from "./SettlerErrors.sol";
import {AllowanceHolderContext} from "../allowanceholder/AllowanceHolderContext.sol";
import {SettlerAbstract} from "../SettlerAbstract.sol";

import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {Revert} from "../utils/Revert.sol";

library TransientStorage {
    // uint256(keccak256("permit auth slot")) - 1
    bytes32 private constant _SLOT = 0xba3245f446772a2c27ba34a24b77f4068853bc993b7dde3ca1b2bcb6ca68ce6e;

    function set(bytes32 witness) internal {
        assembly ("memory-safe") {
            sstore(_SLOT, witness)
        }
    }

    function set(address addr) internal {
        assembly ("memory-safe") {
            sstore(_SLOT, and(0xffffffffffffffffffffffffffffffffffffffff, addr))
        }
    }

    function get() internal view returns (uint256 r) {
        assembly ("memory-safe") {
            r := sload(_SLOT)
        }
    }
}

abstract contract Permit2PaymentBase is AllowanceHolderContext, SettlerAbstract {
    using Revert for bool;

    /// @dev Permit2 address
    ISignatureTransfer internal constant _PERMIT2 = ISignatureTransfer(0x000000000022D473030F116dDEE9F6B43aC78BA3);

    function isRestrictedTarget(address target) internal pure override returns (bool) {
        return target == address(_PERMIT2) || target == address(_ALLOWANCE_HOLDER);
    }

    function _allowCallback(address payable target, uint256 value, bytes memory data)
        internal
        override
        returns (bytes memory)
    {
        TransientStorage.set(target);
        (bool success, bytes memory returndata) = target.call{value: value}(data);
        success.maybeRevert(returndata);
        /*
        if (TransientStorage.get() != 0) {
            revert ConfusedDeputy();
        }
        */
        return returndata;
    }

    function _allowCallback(address target, bytes memory data) internal override returns (bytes memory) {
        return _allowCallback(payable(target), 0, data);
    }

    function _setWitness(bytes32 witness) internal override {
        TransientStorage.set(witness);
    }
}

abstract contract Permit2Payment is Permit2PaymentBase {
    // `string.concat` isn't recognized by solc as compile-time constant, but `abi.encodePacked` is
    // This is defined here as `private` and not in `SettlerAbstract` as `internal` because no other
    // contract/file should reference it. The *ONLY* approved way to make a transfer using this
    // witness string is by setting the witness with `_setWitness`
    string private constant _ACTIONS_AND_SLIPPAGE_WITNESS = string(
        abi.encodePacked("ActionsAndSlippage actionsAndSlippage)", ACTIONS_AND_SLIPPAGE_TYPE, TOKEN_PERMISSIONS_TYPE)
    );

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

    // This function is provided *EXCLUSIVELY* for use here and in OtcOrderSettlement. Any other use
    // of this function is forbidden. You must use the overload that does *NOT* take a `witness`
    // argument.
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

    // See comment in above overload
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
        if (from != _msgSender()) {
            uint256 permitAuth = TransientStorage.get();
            TransientStorage.set(bytes32(0));
            if (permitAuth >> 160 == 0) {
                if (msg.sender != address(uint160(permitAuth))) {
                    revert ConfusedDeputy();
                }
            } else {
                return _transferFrom(
                    permit, transferDetails, from, bytes32(permitAuth), _ACTIONS_AND_SLIPPAGE_WITNESS, sig, isForwarded
                );
            }
        }
        if (isForwarded) {
            if (sig.length != 0) revert InvalidSignatureLen();
            _ALLOWANCE_HOLDER.transferFrom(
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
