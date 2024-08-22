// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {
    CallbackNotSpent,
    ConfusedDeputy,
    ForwarderNotAllowed,
    InvalidSignatureLen,
    PayerSpent,
    ReentrantCallback,
    ReentrantMetatransaction,
    ReentrantPayer,
    SignatureExpired,
    WitnessNotSpent
} from "./SettlerErrors.sol";

import {SettlerAbstract} from "../SettlerAbstract.sol";
import {Permit2PaymentAbstract} from "./Permit2PaymentAbstract.sol";
import {Panic} from "../utils/Panic.sol";
import {FullMath} from "../vendor/FullMath.sol";

import {IERC20} from "forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {Revert} from "../utils/Revert.sol";

import {Context} from "../Context.sol";
import {AllowanceHolderContext} from "../allowanceholder/AllowanceHolderContext.sol";

library TransientStorage {
    // bytes32(uint256(keccak256("operator slot")) - 1)
    bytes32 private constant _OPERATOR_SLOT = 0x009355806b743562f351db2e3726091207f49fa1cdccd5c65a7d4860ce3abbe9;
    // bytes32(uint256(keccak256("witness slot")) - 1)
    bytes32 private constant _WITNESS_SLOT = 0x1643bf8e9fdaef48c4abf5a998de359be44a235ac7aebfbc05485e093720deaa;
    // bytes32(uint256(keccak256("payer slot")) - 1)
    bytes32 private constant _PAYER_SLOT = 0x46bacb9b87ba1d2910347e4a3e052d06c824a45acd1e9517bb0cb8d0d5cde893;

    // We assume (and our CI enforces) that internal function pointers cannot be
    // greater than 2 bytes. On chains not supporting the ViaIR pipeline, not
    // supporting EOF, and where the Spurious Dragon size limit is not enforced,
    // it might be possible to violate this assumption. However, our
    // `foundry.toml` enforces the use of the IR pipeline, so the point is moot.
    //
    // `operator` must not be `address(0)`. This is not checked.
    // `callback` must not be zero. This is checked in `_invokeCallback`.
    function setOperatorAndCallback(
        address operator,
        uint32 selector,
        function (bytes calldata) internal returns (bytes memory) callback
    ) internal {
        address currentSigner;
        assembly ("memory-safe") {
            currentSigner := tload(_PAYER_SLOT)
        }
        if (operator == currentSigner) {
            revert ConfusedDeputy();
        }
        uint256 callbackInt;
        assembly ("memory-safe") {
            callbackInt := tload(_OPERATOR_SLOT)
        }
        if (callbackInt != 0) {
            // It should be impossible to reach this error because the first thing the fallback does
            // is clear the operator. It's also not possible to reenter the entrypoint function
            // because `_PAYER_SLOT` is an implicit reentrancy guard.
            revert ReentrantCallback(callbackInt);
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

    function checkSpentOperatorAndCallback() internal view {
        uint256 callbackInt;
        assembly ("memory-safe") {
            callbackInt := tload(_OPERATOR_SLOT)
        }
        if (callbackInt != 0) {
            revert CallbackNotSpent(callbackInt);
        }
    }

    function getAndClearOperatorAndCallback()
        internal
        returns (bytes4 selector, function (bytes calldata) internal returns (bytes memory) callback, address operator)
    {
        assembly ("memory-safe") {
            selector := tload(_OPERATOR_SLOT)
            callback := and(0xffff, shr(0xa0, selector))
            operator := selector
            tstore(_OPERATOR_SLOT, 0x00)
        }
    }

    // `newWitness` must not be `bytes32(0)`. This is not checked.
    function setWitness(bytes32 newWitness) internal {
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

    function getAndClearWitness() internal returns (bytes32 witness) {
        assembly ("memory-safe") {
            witness := tload(_WITNESS_SLOT)
            tstore(_WITNESS_SLOT, 0x00)
        }
    }

    function setPayer(address payer) internal {
        if (payer == address(0)) {
            revert ConfusedDeputy();
        }
        address oldPayer;
        assembly ("memory-safe") {
            oldPayer := tload(_PAYER_SLOT)
        }
        if (oldPayer != address(0)) {
            revert ReentrantPayer(oldPayer);
        }
        assembly ("memory-safe") {
            tstore(_PAYER_SLOT, and(0xffffffffffffffffffffffffffffffffffffffff, payer))
        }
    }

    function getPayer() internal view returns (address payer) {
        assembly ("memory-safe") {
            payer := tload(_PAYER_SLOT)
        }
    }

    function clearPayer(address expectedOldPayer) internal {
        address oldPayer;
        assembly ("memory-safe") {
            oldPayer := tload(_PAYER_SLOT)
        }
        if (oldPayer != expectedOldPayer) {
            revert PayerSpent();
        }
        assembly ("memory-safe") {
            tstore(_PAYER_SLOT, 0x00)
        }
    }
}

abstract contract Permit2PaymentBase is SettlerAbstract {
    using Revert for bool;

    /// @dev Permit2 address
    ISignatureTransfer internal constant _PERMIT2 = ISignatureTransfer(0x000000000022D473030F116dDEE9F6B43aC78BA3);

    function _isRestrictedTarget(address target) internal pure virtual override returns (bool) {
        return target == address(_PERMIT2);
    }

    function _msgSender() internal view virtual override returns (address) {
        return TransientStorage.getPayer();
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
        TransientStorage.setOperatorAndCallback(target, selector, callback);
        (bool success, bytes memory returndata) = target.call{value: value}(data);
        success.maybeRevert(returndata);
        TransientStorage.checkSpentOperatorAndCallback();
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

    function _invokeCallback(bytes calldata data) internal returns (bytes memory) {
        // Retrieve callback and perform call with untrusted calldata
        (bytes4 selector, function (bytes calldata) internal returns (bytes memory) callback, address operator) =
            TransientStorage.getAndClearOperatorAndCallback();
        require(bytes4(data) == selector);
        require(msg.sender == operator);
        return callback(data[4:]);
    }
}

abstract contract Permit2Payment is Permit2PaymentBase {
    using FullMath for uint256;

    fallback(bytes calldata data) external virtual returns (bytes memory) {
        return _invokeCallback(data);
    }

    function _permitToSellAmount(ISignatureTransfer.PermitTransferFrom memory permit)
        internal
        view
        override
        returns (uint256 sellAmount)
    {
        sellAmount = permit.permitted.amount;
        if (sellAmount > type(uint256).max - BASIS) {
            unchecked {
                sellAmount -= type(uint256).max - BASIS;
            }
            sellAmount = IERC20(permit.permitted.token).balanceOf(_msgSender()).mulDiv(sellAmount, BASIS);
        }
    }

    function _permitToTransferDetails(ISignatureTransfer.PermitTransferFrom memory permit, address recipient)
        internal
        view
        override
        returns (ISignatureTransfer.SignatureTransferDetails memory transferDetails, uint256 sellAmount)
    {
        transferDetails.to = recipient;
        transferDetails.requestedAmount = sellAmount = _permitToSellAmount(permit);
    }

    // This function is provided *EXCLUSIVELY* for use here and in RfqOrderSettlement. Any other use
    // of this function is forbidden. You must use the version that does *NOT* take a `from` or
    // `witness` argument.
    function _transferFromIKnowWhatImDoing(
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
    function _transferFromIKnowWhatImDoing(
        ISignatureTransfer.PermitTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails memory transferDetails,
        address from,
        bytes32 witness,
        string memory witnessTypeString,
        bytes memory sig
    ) internal override {
        _transferFromIKnowWhatImDoing(permit, transferDetails, from, witness, witnessTypeString, sig, _isForwarded());
    }

    function _transferFrom(
        ISignatureTransfer.PermitTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails memory transferDetails,
        bytes memory sig
    ) internal override {
        _transferFrom(permit, transferDetails, sig, _isForwarded());
    }
}

abstract contract Permit2PaymentTakerSubmitted is AllowanceHolderContext, Permit2Payment {
    constructor() {
        assert(!_hasMetaTxn());
    }

    function _isRestrictedTarget(address target) internal pure virtual override returns (bool) {
        return target == address(_ALLOWANCE_HOLDER) || super._isRestrictedTarget(target);
    }

    function _operator() internal view override returns (address) {
        return AllowanceHolderContext._msgSender();
    }

    function _msgSender()
        internal
        view
        virtual
        override(Permit2PaymentBase, AllowanceHolderContext)
        returns (address)
    {
        return Permit2PaymentBase._msgSender();
    }

    function _transferFrom(
        ISignatureTransfer.PermitTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails memory transferDetails,
        bytes memory sig,
        bool isForwarded
    ) internal override {
        if (isForwarded) {
            if (sig.length != 0) revert InvalidSignatureLen();
            if (permit.nonce != 0) Panic.panic(Panic.ARITHMETIC_OVERFLOW);
            if (block.timestamp > permit.deadline) revert SignatureExpired(permit.deadline);
            // we don't check `requestedAmount` because it's checked by AllowanceHolder itself
            _allowanceHolderTransferFrom(
                permit.permitted.token, _msgSender(), transferDetails.to, transferDetails.requestedAmount
            );
        } else {
            _PERMIT2.permitTransferFrom(permit, transferDetails, _msgSender(), sig);
        }
    }

    function _allowanceHolderTransferFrom(address token, address owner, address recipient, uint256 amount)
        internal
        override
    {
        // `owner` is always `_msgSender()`
        _ALLOWANCE_HOLDER.transferFrom(token, owner, recipient, amount);
    }

    modifier takerSubmitted() override {
        address msgSender = _operator();
        TransientStorage.setPayer(msgSender);
        _;
        TransientStorage.clearPayer(msgSender);
    }

    modifier metaTx(address, bytes32) override {
        revert();
        _;
    }
}

abstract contract Permit2PaymentMetaTxn is Context, Permit2Payment {
    constructor() {
        assert(_hasMetaTxn());
    }

    function _operator() internal view override returns (address) {
        return Context._msgSender();
    }

    function _msgSender() internal view virtual override(Permit2PaymentBase, Context) returns (address) {
        return Permit2PaymentBase._msgSender();
    }

    // `string.concat` isn't recognized by solc as compile-time constant, but `abi.encodePacked` is
    // This is defined here as `private` and not in `SettlerAbstract` as `internal` because no other
    // contract/file should reference it. The *ONLY* approved way to make a transfer using this
    // witness string is by setting the witness with modifier `metaTx`
    string private constant _SLIPPAGE_AND_ACTIONS_WITNESS = string(
        abi.encodePacked("SlippageAndActions slippageAndActions)", SLIPPAGE_AND_ACTIONS_TYPE, TOKEN_PERMISSIONS_TYPE)
    );

    function _transferFrom(
        ISignatureTransfer.PermitTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails memory transferDetails,
        bytes memory sig,
        bool isForwarded // must be false
    ) internal override {
        bytes32 witness = TransientStorage.getAndClearWitness();
        if (witness == bytes32(0)) {
            revert ConfusedDeputy();
        }
        _transferFromIKnowWhatImDoing(
            permit, transferDetails, _msgSender(), witness, _SLIPPAGE_AND_ACTIONS_WITNESS, sig, isForwarded
        );
    }

    function _allowanceHolderTransferFrom(address, address, address, uint256) internal pure override {
        revert ConfusedDeputy();
    }

    modifier takerSubmitted() override {
        revert();
        _;
    }

    modifier metaTx(address msgSender, bytes32 witness) override {
        if (_isForwarded()) {
            revert ForwarderNotAllowed();
        }
        TransientStorage.setWitness(witness);
        TransientStorage.setPayer(msgSender);
        _;
        TransientStorage.clearPayer(msgSender);
        // It should not be possible for this check to revert because the very first thing that a
        // metatransaction does is spend the witness.
        TransientStorage.checkSpentWitness();
    }
}
