// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {
    CallbackNotSpent,
    ConfusedDeputy,
    ForwarderNotAllowed,
    InvalidSignatureLen,
    OperatorNotSpent,
    ReentrantCallback,
    ReentrantMetatransaction,
    SignatureExpired,
    WitnessNotSpent
} from "./SettlerErrors.sol";

import {SettlerAbstract} from "../SettlerAbstract.sol";
import {Panic} from "../utils/Panic.sol";

import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {Revert} from "../utils/Revert.sol";

library TransientStorage {
    // bytes32(uint256(keccak256("operator slot")) - 1)
    bytes32 private constant _OPERATOR_SLOT = 0x009355806b743562f351db2e3726091207f49fa1cdccd5c65a7d4860ce3abbe9;
    // bytes32(uint256(keccak256("witness slot")) - 1)
    bytes32 private constant _WITNESS_SLOT = 0x1643bf8e9fdaef48c4abf5a998de359be44a235ac7aebfbc05485e093720deaa;
    // bytes32(uint256(keccak256("metatx signer slot")) - 1)
    bytes32 private constant _METATX_SIGNER_SLOT = 0xfc7be34027b4062d13b31d75182f37b703b5ad960f0e73236593535549bb277d;

    function setOperator(address operator, bool strict) internal {
        address currentSigner;
        assembly ("memory-safe") {
            currentSigner := tload(_METATX_SIGNER_SLOT)
        }
        if (operator == currentSigner) {
            revert ConfusedDeputy();
        }
        address currentOperator;
        assembly ("memory-safe") {
            currentOperator := tload(_OPERATOR_SLOT)
        }
        if ((strict || currentOperator != address(0)) && msg.sender != currentOperator) {
            revert ReentrantCallback(currentOperator);
        }
        assembly ("memory-safe") {
            tstore(_OPERATOR_SLOT, and(0xffffffffffffffffffffffffffffffffffffffff, operator))
        }
    }

    function setOperatorAndCallback(
        address operator,
        uint32 selector,
        function (bytes calldata) internal returns (bytes memory) callback,
        bool strict
    ) internal {
        address currentSigner;
        assembly ("memory-safe") {
            currentSigner := tload(_METATX_SIGNER_SLOT)
        }
        if (operator == currentSigner) {
            revert ConfusedDeputy();
        }
        address currentOperator;
        assembly ("memory-safe") {
            currentOperator := tload(_OPERATOR_SLOT)
        }
        if ((strict || currentOperator != address(0)) && msg.sender != currentOperator) {
            revert ReentrantCallback(currentOperator);
        }
        assembly ("memory-safe") {
            tstore(
                _OPERATOR_SLOT,
                or(
                    shl(0xe0, selector),
                    or(shl(0xa0, and(0xffff, callback)), and(0xffffffffffffffffffffffffffffffffffffffff, operator))
                )
            )
        }
    }

    function checkSpentOperator() internal view {
        uint256 currentOperator;
        assembly ("memory-safe") {
            currentOperator := tload(_OPERATOR_SLOT)
        }
        if (currentOperator != 0) {
            revert OperatorNotSpent(address(uint160(currentOperator)));
        }
    }

    function getAndClearOperator() internal returns (address operator) {
        assembly ("memory-safe") {
            operator := tload(_OPERATOR_SLOT)
            if operator {
                if shr(0xa0, operator) {
                    mstore(0x00, 0xe758b8d5) // selector for ConfusedDeputy()
                    revert(0x1c, 0x04)
                }
                tstore(_OPERATOR_SLOT, 0)
            }
        }
    }

    function setCallback(uint32 selector, function (bytes calldata) internal returns (bytes memory) callback)
        internal
    {
        assembly ("memory-safe") {
            let operator := tload(_OPERATOR_SLOT)
            if shr(0xa0, operator) {
                mstore(0x00, 0x77f94425) // selector for `ReentrantCallback(address)`
                mstore(0x00, and(0xffffffffffffffffffffffffffffffffffffffff, operator))
                revert(0x1c, 0x24)
            }
            tstore(_OPERATOR_SLOT, or(shl(0xe0, selector), or(shl(0xa0, and(0xffff, callback)), operator)))
        }
    }

    function checkSpentCallback() internal view {
        uint256 callbackInt;
        assembly ("memory-safe") {
            callbackInt := shr(0xa0, tload(_OPERATOR_SLOT))
        }
        if (callbackInt != 0) {
            revert CallbackNotSpent(callbackInt);
        }
    }

    function getAndClearCallback()
        internal
        returns (bytes4 selector, function (bytes calldata) internal returns (bytes memory) callback, address operator)
    {
        assembly ("memory-safe") {
            selector := tload(_OPERATOR_SLOT)
            callback := and(0xffff, shr(0xa0, selector))
            operator := and(0xffffffffffffffffffffffffffffffffffffffff, selector)
            tstore(_OPERATOR_SLOT, operator)
        }
    }

    function setWitness(bytes32 newWitness, address signer) internal {
        bytes32 currentWitness;
        assembly ("memory-safe") {
            currentWitness := tload(_WITNESS_SLOT)
        }
        if (currentWitness != bytes32(0)) {
            // It should be impossible to reach this error because the first thing a metatransaction
            // does on entry is to spend the `witness` (either directly or via a callback)
            revert ReentrantMetatransaction(currentWitness);
        }
        assembly ("memory-safe") {
            tstore(_WITNESS_SLOT, newWitness)
            tstore(_METATX_SIGNER_SLOT, and(0xffffffffffffffffffffffffffffffffffffffff, signer))
        }
    }

    function checkSpentWitness() internal view {
        bytes32 currentWitness;
        assembly ("memory-safe") {
            currentWitness := tload(_WITNESS_SLOT)
        }
        if (currentWitness != bytes32(0)) {
            revert WitnessNotSpent(currentWitness);
        }
    }

    function getAndClearWitness() internal returns (bytes32 witness, address signer) {
        assembly ("memory-safe") {
            witness := tload(_WITNESS_SLOT)
            if witness {
                signer := tload(_METATX_SIGNER_SLOT)
                tstore(_METATX_SIGNER_SLOT, 0)
                tstore(_WITNESS_SLOT, 0)
            }
        }
    }
}

abstract contract Permit2PaymentBase is SettlerAbstract {
    using Revert for bool;

    /// @dev Permit2 address
    ISignatureTransfer internal constant _PERMIT2 = ISignatureTransfer(0x000000000022D473030F116dDEE9F6B43aC78BA3);

    function isRestrictedTarget(address target) internal pure virtual override returns (bool) {
        return target == address(_PERMIT2);
    }

    /// @dev You must ensure that `target` is derived by hashing trusted initcode or another
    ///      equivalent mechanism that guarantees "reasonable"ness. `target` must not be
    ///      user-supplied or attacker-controlled. This is required for security and is not checked
    ///      here. For example, it must not do something weird like modifying the spender (possibly
    ///      setting it to itself). If the callback is expected to relay a
    ///      `ISignatureTransfer.PermitTransferFrom` struct, then the computation of `target` using
    ///      the trusted initcode (or equivalent) must ensure that that calldata is relayed
    ///      unmodified. The library function `AddressDerivation.deriveDeterministicContract` is
    ///      recommended.
    function _setOperatorAndCall(
        address payable target,
        uint256 value,
        bytes memory data,
        uint32 selector,
        function (bytes calldata) internal returns (bytes memory) callback
    ) internal returns (bytes memory) {
        // metatx-supporting `Settler` instances (`_hasMetaTxn() == true`) don't rely on
        // `_msgSender()` authentication, so a trusted `operator` being in transient storage is
        // mandatory. for non-metatx-supporting `Settler` instances (`_hasMetaTxn() == false`), we
        // allow an unset `operator` at top level.
        TransientStorage.setOperatorAndCallback(target, selector, callback, _hasMetaTxn());
        (bool success, bytes memory returndata) = target.call{value: value}(data);
        success.maybeRevert(returndata);
        TransientStorage.checkSpentOperator();
        return returndata;
    }

    function _setOperatorAndCall(
        address target,
        bytes memory data,
        uint32 selector,
        function (bytes calldata) internal returns (bytes memory) callback
    ) internal override returns (bytes memory) {
        return _setOperatorAndCall(payable(target), 0, data, selector, callback);
    }

    function _setCallbackAndCall(
        address payable target,
        uint256 value,
        bytes memory data,
        uint32 selector,
        function (bytes calldata) internal returns (bytes memory) callback
    ) internal returns (bytes memory) {
        TransientStorage.setCallback(selector, callback);
        (bool success, bytes memory returndata) = target.call{value: value}(data);
        success.maybeRevert(returndata);
        TransientStorage.checkSpentCallback();
        return returndata;
    }

    function _setCallbackAndCall(
        address target,
        bytes memory data,
        uint32 selector,
        function (bytes calldata) internal returns (bytes memory) callback
    ) internal override returns (bytes memory) {
        return _setCallbackAndCall(payable(target), 0, data, selector, callback);
    }

    modifier metaTx(address msgSender, bytes32 witness) override {
        assert(_hasMetaTxn());
        if (_isForwarded()) {
            revert ConfusedDeputy();
        }
        TransientStorage.setWitness(witness, msgSender);
        TransientStorage.setOperator(msg.sender, false);
        _;
        // It should not be possible for these checks to revert because the very first thing that a
        // metatransaction does is spend the operator/witness.
        TransientStorage.checkSpentOperator();
        TransientStorage.checkSpentWitness();
    }

    function _invokeCallback(bytes calldata data) internal returns (bytes memory) {
        (bytes4 selector, function (bytes calldata) internal returns (bytes memory) callback, address operator) =
            TransientStorage.getAndClearCallback();
        require(bytes4(data) == selector);
        // `operator == address(0)` implies that this context is unable to spend coupons (unless
        // `_msgSender()` wants to spend its own coupon for some insane reason; smart contract
        // takers are responsible for their own security/reentrancy guards)
        require(operator == address(0) || msg.sender == operator);
        return callback(data[4:]);
    }
}

abstract contract Permit2Payment is Permit2PaymentBase {
    // `string.concat` isn't recognized by solc as compile-time constant, but `abi.encodePacked` is
    // This is defined here as `private` and not in `SettlerAbstract` as `internal` because no other
    // contract/file should reference it. The *ONLY* approved way to make a transfer using this
    // witness string is by setting the witness with modifier `metaTx`
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

    // This function is provided *EXCLUSIVELY* for use here and in RfqOrderSettlement. Any other use
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

    // See comment in above overload; don't use this function
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
        // Because `_hasMetaTxn()` is `pure`, this `if` statement is branching on a compile-time
        // constant. The branch not taken is dead code and is eliminated by the compiler. Only one
        // branch is reachable from a given `Settler` instance.
        if (_hasMetaTxn()) {
            if (msg.sender != TransientStorage.getAndClearOperator()) {
                revert ConfusedDeputy();
            }
            (bytes32 witness, address signer) = TransientStorage.getAndClearWitness();
            if (witness == bytes32(0) || from != signer) {
                revert ConfusedDeputy();
            }
            _transferFrom(permit, transferDetails, from, witness, _ACTIONS_AND_SLIPPAGE_WITNESS, sig, isForwarded);
        } else {
            if (from != _msgSender() && msg.sender != TransientStorage.getAndClearOperator()) {
                revert ConfusedDeputy();
            }
            if (isForwarded) {
                if (sig.length != 0) revert InvalidSignatureLen();
                if (permit.nonce != 0) Panic.panic(Panic.ARITHMETIC_OVERFLOW);
                if (block.timestamp > permit.deadline) revert SignatureExpired(permit.deadline);
                // we don't check `requestedAmount` because it's copied in `_permitToTransferDetails`
                _allowanceHolderTransferFrom(
                    permit.permitted.token, from, transferDetails.to, transferDetails.requestedAmount
                );
            } else {
                _PERMIT2.permitTransferFrom(permit, transferDetails, from, sig);
            }
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
