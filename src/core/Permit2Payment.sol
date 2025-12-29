// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {
    CallbackNotSpent,
    revertConfusedDeputy,
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
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {FastLogic} from "../utils/FastLogic.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {Revert} from "../utils/Revert.sol";

import {AbstractContext, Context} from "../Context.sol";
import {AllowanceHolderContext, ALLOWANCE_HOLDER} from "../allowanceholder/AllowanceHolderContext.sol";

library FunctionPointerChecker {
    function isNull(function (bytes calldata) internal returns (bytes memory) callback) internal pure returns (bool r) {
        assembly ("memory-safe") {
            r := iszero(callback)
        }
    }
}

library TransientStorage {
    // bytes32((uint256(keccak256("operator slot")) - 1) & type(uint96).max)
    bytes32 private constant _OPERATOR_SLOT = 0x0000000000000000000000000000000000000000cdccd5c65a7d4860ce3abbe9;
    // bytes32((uint256(keccak256("witness slot")) - 1) & type(uint96).max)
    bytes32 private constant _WITNESS_SLOT = 0x0000000000000000000000000000000000000000c7aebfbc05485e093720deaa;
    // bytes32((uint256(keccak256("payer slot")) - 1) & type(uint96).max)
    bytes32 private constant _PAYER_SLOT = 0x0000000000000000000000000000000000000000cd1e9517bb0cb8d0d5cde893;

    // We assume (and our CI enforces) that internal function pointers cannot be
    // greater than 2 bytes. On chains not supporting the ViaIR pipeline, not
    // supporting EOF, and where the Spurious Dragon size limit is not enforced,
    // it might be possible to violate this assumption. However, our
    // `foundry.toml` enforces the use of the IR pipeline, so the point is moot.
    //
    // `operator` must not be `address(0)`. This is not checked.
    // `callback` must not be zero. This is checked in `fallback`.
    function setOperatorAndCallback(
        address operator,
        uint32 selector,
        function (bytes calldata) internal returns (bytes memory) callback
    ) internal {
        assembly ("memory-safe") {
            if iszero(shl(0x60, xor(tload(_PAYER_SLOT), operator))) {
                mstore(0x00, 0xe758b8d5) // selector for `ConfusedDeputy()`
                revert(0x1c, 0x04)
            }
            let slotValue := tload(_OPERATOR_SLOT)
            if slotValue {
                // It should be impossible to reach this error because the first thing the fallback
                // does is clear the operator. It's also not possible to reenter the entrypoint
                // function because `_PAYER_SLOT` is an implicit reentrancy guard.
                mstore(0x00, 0xab7646c4) // selector for `ReentrantCallback(uint256)`
                mstore(0x20, slotValue)
                revert(0x1c, 0x24)
            }

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
        assembly ("memory-safe") {
            let slotValue := tload(_OPERATOR_SLOT)
            if slotValue {
                mstore(0x00, 0xd66fcc38) // selector for `CallbackNotSpent(uint256)`
                mstore(0x20, slotValue)
                revert(0x1c, 0x24)
            }
        }
    }

    function getAndClearCallback()
        internal
        returns (function (bytes calldata) internal returns (bytes memory) callback)
    {
        assembly ("memory-safe") {
            let slotValue := tload(_OPERATOR_SLOT)
            let badCallerOrSelector := or(shr(0xe0, xor(calldataload(0x00), slotValue)), shl(0x60, xor(caller(), slotValue)))
            callback := and(0xffff, shr(0xa0, slotValue))
            callback := mul(iszero(badCallerOrSelector), callback)
            tstore(_OPERATOR_SLOT, 0x00)
        }
    }

    // `newWitness` must not be `bytes32(0)`. This is not checked.
    function setWitness(bytes32 newWitness) internal {
        assembly ("memory-safe") {
            let slotValue := tload(_WITNESS_SLOT)
            if slotValue {
                // It should be impossible to reach this error because the first thing a
                // metatransaction does on entry is to spend the `witness` (either directly or via a
                // callback)
                mstore(0x00, 0x9936cbab) // selector for `ReentrantMetatransaction(bytes32)`
                mstore(0x20, slotValue)
                revert(0x1c, 0x24)
            }

            tstore(_WITNESS_SLOT, newWitness)
        }
    }

    function checkSpentWitness() internal view {
        assembly ("memory-safe") {
            let slotValue := tload(_WITNESS_SLOT)
            if slotValue {
                mstore(0x00, 0xe25527c2) // selector for `WitnessNotSpent(bytes32)`
                mstore(0x20, slotValue)
                revert(0x1c, 0x24)
            }
        }
    }

    function getAndClearWitness() internal returns (bytes32 witness) {
        assembly ("memory-safe") {
            witness := tload(_WITNESS_SLOT)
            tstore(_WITNESS_SLOT, 0x00)
        }
    }

    function setPayer(address payer) internal {
        assembly ("memory-safe") {
            if iszero(shl(0x60, payer)) {
                mstore(0x00, 0xe758b8d5) // selector for `ConfusedDeputy()`
                revert(0x1c, 0x04)
            }
            let slotValue := tload(_PAYER_SLOT)
            if shl(0x60, slotValue) {
                mstore(0x14, slotValue)
                mstore(0x00, 0x7407c0f8000000000000000000000000) // selector for `ReentrantPayer(address)` with `oldPayer`'s padding
                revert(0x10, 0x24)
            }

            tstore(_PAYER_SLOT, and(0xffffffffffffffffffffffffffffffffffffffff, payer))
        }
    }

    function getPayer() internal view returns (address payer) {
        assembly ("memory-safe") {
            payer := tload(_PAYER_SLOT)
        }
    }

    function clearPayer(address expectedOldPayer) internal {
        assembly ("memory-safe") {
            if shl(0x60, xor(tload(_PAYER_SLOT), expectedOldPayer)) {
                mstore(0x00, 0x5149e795) // selector for `PayerSpent()`
                revert(0x1c, 0x04)
            }

            tstore(_PAYER_SLOT, 0x00)
        }
    }
}

abstract contract Permit2PaymentBase is Context, SettlerAbstract {
    using FastLogic for bool;
    using Revert for bool;

    /// @dev Permit2 address
    ISignatureTransfer internal constant _PERMIT2 = ISignatureTransfer(0x000000000022D473030F116dDEE9F6B43aC78BA3);

    function _isRestrictedTarget(address target) internal view virtual override returns (bool) {
        return (target == address(_PERMIT2)).or(super._isRestrictedTarget(target));
    }

    function _operator() internal view virtual override returns (address) {
        return super._msgSender();
    }

    function _msgSender() internal view virtual override(AbstractContext, Context) returns (address) {
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
}

abstract contract Permit2Payment is Permit2PaymentBase {
    using FunctionPointerChecker for function (bytes calldata) internal returns (bytes memory);

    function _chainSpecificFallback(bytes calldata) internal virtual returns (bytes memory) {
        revert();
    }

    fallback(bytes calldata) external virtual returns (bytes memory) {
        function (bytes calldata) internal returns (bytes memory) callback = TransientStorage.getAndClearCallback();
        bytes calldata data = _msgData();
        if (callback.isNull()) {
            return _chainSpecificFallback(data);
        } else {
            assembly ("memory-safe") {
                data.offset := add(0x04, data.offset)
                data.length := sub(data.length, 0x04)
            }
            return callback(data);
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
        if (isForwarded) {
            assembly ("memory-safe") {
                mstore(0x00, 0x1c500e5c) // selector for `ForwarderNotAllowed()`
                revert(0x1c, 0x04)
            }
        }

        // This is effectively
        /*
        _PERMIT2.permitWitnessTransferFrom(permit, transferDetails, from, witness, witnessTypeString, sig);
        */
        // but it's written in assembly for contract size reasons. This produces a non-strict ABI
        // encoding (https://docs.soliditylang.org/en/v0.8.25/abi-spec.html#strict-encoding-mode),
        // but it's fine because Solidity's ABI *decoder* will handle anything that is validly
        // encoded, strict or not.

        // Solidity won't let us reference the constant `_PERMIT2` in assembly, but this compiles
        // down to just a single PUSH opcode just before the CALL, with optimization turned on.
        ISignatureTransfer __PERMIT2 = _PERMIT2;
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(ptr, 0x137c29fe) // selector for `permitWitnessTransferFrom(((address,uint256),uint256,uint256),(address,uint256),address,bytes32,string,bytes)`

            // The layout of nested structs in memory is different from that in calldata. We have to
            // chase the pointer to `permit.permitted`.
            mcopy(add(0x20, ptr), mload(permit), 0x40)
            // The rest of the members of `permit` are laid out linearly,
            mcopy(add(0x60, ptr), add(0x20, permit), 0x40)
            // as are the members of `transferDetails.
            mcopy(add(0xa0, ptr), transferDetails, 0x40)
            // Because we're passing `from` on the stack, it must be cleaned.
            mstore(add(0xe0, ptr), and(0xffffffffffffffffffffffffffffffffffffffff, from))
            mstore(add(0x100, ptr), witness)
            mstore(add(0x120, ptr), 0x140) // Offset to `witnessTypeString` (the end of of the non-dynamic types)
            let witnessTypeStringLength := mload(witnessTypeString)
            mstore(add(0x140, ptr), add(0x160, witnessTypeStringLength)) // Offset to `sig` (past the end of `witnessTypeString`)

            // Now we encode the 2 dynamic objects, `witnessTypeString` and `sig`.
            mcopy(add(0x160, ptr), witnessTypeString, add(0x20, witnessTypeStringLength))
            let sigLength := mload(sig)
            mcopy(add(0x180, add(ptr, witnessTypeStringLength)), sig, add(0x20, sigLength))

            // We don't need to check that Permit2 has code, and it always signals failure by
            // reverting.
            if iszero(
                call(
                    gas(),
                    __PERMIT2,
                    0x00,
                    add(0x1c, ptr),
                    add(0x184, add(witnessTypeStringLength, sigLength)),
                    0x00,
                    0x00
                )
            ) {
                let ptr_ := mload(0x40)
                returndatacopy(ptr_, 0x00, returndatasize())
                revert(ptr_, returndatasize())
            }
        }
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

// DANGER: the order of the base contracts here is very significant for the use of `super` below
// (and in derived contracts). Do not change this order.
abstract contract Permit2PaymentTakerSubmitted is AllowanceHolderContext, Permit2Payment {
    using FullMath for uint256;
    using SafeTransferLib for IERC20;
    using FastLogic for bool;

    constructor() {
        assert(!_hasMetaTxn());
    }

    function _permitToSellAmountCalldata(ISignatureTransfer.PermitTransferFrom calldata permit)
        internal
        view
        override
        returns (uint256 sellAmount)
    {
        sellAmount = permit.permitted.amount;
        unchecked {
            if (~sellAmount < BASIS) {
                sellAmount = BASIS - ~sellAmount;
                sellAmount = IERC20(permit.permitted.token).fastBalanceOf(_msgSender()).unsafeMulDiv(sellAmount, BASIS);
            }
        }
    }

    function _permitToSellAmount(ISignatureTransfer.PermitTransferFrom memory permit)
        internal
        view
        override
        returns (uint256 sellAmount)
    {
        sellAmount = permit.permitted.amount;
        unchecked {
            if (~sellAmount < BASIS) {
                sellAmount = BASIS - ~sellAmount;
                sellAmount = IERC20(permit.permitted.token).fastBalanceOf(_msgSender()).unsafeMulDiv(sellAmount, BASIS);
            }
        }
    }

    function _isRestrictedTarget(address target) internal view virtual override returns (bool) {
        return (target == address(ALLOWANCE_HOLDER)).or(super._isRestrictedTarget(target));
    }

    function _transferFrom(
        ISignatureTransfer.PermitTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails memory transferDetails,
        bytes memory sig,
        bool isForwarded
    ) internal override {
        if (isForwarded) {
            if (sig.length != 0) {
                assembly ("memory-safe") {
                    mstore(0x00, 0xc321526c) // selector for `InvalidSignatureLen()`
                    revert(0x1c, 0x04)
                }
            }
            if (permit.nonce != 0) Panic.panic(Panic.ARITHMETIC_OVERFLOW);
            if (block.timestamp > permit.deadline) {
                assembly ("memory-safe") {
                    mstore(0x00, 0xcd21db4f) // selector for `SignatureExpired(uint256)`
                    mstore(0x20, mload(add(0x40, permit)))
                    revert(0x1c, 0x24)
                }
            }
            // we don't check `requestedAmount` because it's checked by AllowanceHolder itself
            _allowanceHolderTransferFrom(
                permit.permitted.token, _msgSender(), transferDetails.to, transferDetails.requestedAmount
            );
        } else {
            // This is effectively
            /*
            _PERMIT2.permitTransferFrom(permit, transferDetails, _msgSender(), sig);
            */
            // but it's written in assembly for contract size reasons. This produces a non-strict
            // ABI encoding
            // (https://docs.soliditylang.org/en/v0.8.25/abi-spec.html#strict-encoding-mode), but
            // it's fine because Solidity's ABI *decoder* will handle anything that is validly
            // encoded, strict or not.

            // Solidity won't let us reference the constant `_PERMIT2` in assembly, but this
            // compiles down to just a single PUSH opcode just before the CALL, with optimization
            // turned on.
            ISignatureTransfer __PERMIT2 = _PERMIT2;
            address from = _msgSender();
            assembly ("memory-safe") {
                let ptr := mload(0x40)
                mstore(ptr, 0x30f28b7a) // selector for `permitTransferFrom(((address,uint256),uint256,uint256),(address,uint256),address,bytes)`

                // The layout of nested structs in memory is different from that in calldata. We
                // have to chase the pointer to `permit.permitted`.
                mcopy(add(0x20, ptr), mload(permit), 0x40)
                // The rest of the members of `permit` are laid out linearly,
                mcopy(add(0x60, ptr), add(0x20, permit), 0x40)
                // as are the members of `transferDetails.
                mcopy(add(0xa0, ptr), transferDetails, 0x40)
                // Because we're passing `from` on the stack, it must be cleaned.
                mstore(add(0xe0, ptr), and(0xffffffffffffffffffffffffffffffffffffffff, from))
                mstore(add(0x100, ptr), 0x100) // Offset to `sig` (the end of the non-dynamic types)

                // Encode the dynamic object `sig`
                let sigLength := mload(sig)
                mcopy(add(0x120, ptr), sig, add(0x20, sigLength))

                // We don't need to check that Permit2 has code, and it always signals failure by
                // reverting.
                if iszero(call(gas(), __PERMIT2, 0x00, add(0x1c, ptr), add(0x124, sigLength), 0x00, 0x00)) {
                    let ptr_ := mload(0x40)
                    returndatacopy(ptr_, 0x00, returndatasize())
                    revert(ptr_, returndatasize())
                }
            }
        }
    }

    function _allowanceHolderTransferFrom(address token, address owner, address recipient, uint256 amount)
        internal
        override
    {
        // `owner` is always `_msgSender()`
        // This is effectively
        /*
        _ALLOWANCE_HOLDER.transferFrom(token, owner, recipient, amount);
        */
        // but it's written in assembly for contract size reasons.

        // Solidity won't let us reference the constant `_ALLOWANCE_HOLDER` in assembly, but this
        // compiles down to just a single PUSH opcode just before the CALL, with optimization turned
        // on.
        address _ALLOWANCE_HOLDER = address(ALLOWANCE_HOLDER);
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(add(0x80, ptr), amount)
            mstore(add(0x60, ptr), recipient)
            mstore(add(0x4c, ptr), shl(0x60, owner)) // clears `recipient`'s padding
            mstore(add(0x2c, ptr), shl(0x60, token)) // clears `owner`'s padding
            mstore(add(0x0c, ptr), 0x15dacbea000000000000000000000000) // selector for `transferFrom(address,address,address,uint256)` with `token`'s padding

            // Although `transferFrom` returns `bool`, we don't need to bother checking the return
            // value because `AllowanceHolder` always either reverts or returns `true`. We also
            // don't need to check that it has code.
            if iszero(call(gas(), _ALLOWANCE_HOLDER, 0x00, add(0x1c, ptr), 0x84, 0x00, 0x00)) {
                let ptr_ := mload(0x40)
                returndatacopy(ptr_, 0x00, returndatasize())
                revert(ptr_, returndatasize())
            }
        }
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

    // Solidity inheritance is stupid
    function _isForwarded()
        internal
        view
        virtual
        override(AbstractContext, Context, AllowanceHolderContext)
        returns (bool)
    {
        return super._isForwarded();
    }

    function _msgData()
        internal
        view
        virtual
        override(AbstractContext, Context, AllowanceHolderContext)
        returns (bytes calldata)
    {
        return super._msgData();
    }

    function _msgSender()
        internal
        view
        virtual
        override(AllowanceHolderContext, Permit2PaymentBase)
        returns (address)
    {
        return super._msgSender();
    }
}

// DANGER: the order of the base contracts here is very significant for the use of `super` below
// (and in derived contracts). Do not change this order.
abstract contract Permit2PaymentMetaTxn is Context, Permit2Payment {
    constructor() {
        assert(_hasMetaTxn());
        assert(
            keccak256(bytes(Permit2PaymentMetaTxn._witnessTypeSuffix()))
                == keccak256(
                    abi.encodePacked(
                        "SlippageAndActions slippageAndActions)", SLIPPAGE_AND_ACTIONS_TYPE, TOKEN_PERMISSIONS_TYPE
                    )
                )
        );
    }

    function _permitToSellAmountCalldata(ISignatureTransfer.PermitTransferFrom calldata permit)
        internal
        view
        virtual
        override
        returns (uint256)
    {
        return permit.permitted.amount;
    }

    function _permitToSellAmount(ISignatureTransfer.PermitTransferFrom memory permit)
        internal
        view
        virtual
        override
        returns (uint256)
    {
        return permit.permitted.amount;
    }

    function _witnessTypeSuffix() internal pure virtual returns (string memory) {
        return
        "SlippageAndActions slippageAndActions)SlippageAndActions(address recipient,address buyToken,uint256 minAmountOut,bytes[] actions)TokenPermissions(address token,uint256 amount)";
    }

    function _transferFrom(
        ISignatureTransfer.PermitTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails memory transferDetails,
        bytes memory sig,
        bool isForwarded // must be false
    ) internal override {
        bytes32 witness = TransientStorage.getAndClearWitness();
        if (witness == bytes32(0)) {
            revertConfusedDeputy();
        }
        _transferFromIKnowWhatImDoing(
            permit, transferDetails, _msgSender(), witness, _witnessTypeSuffix(), sig, isForwarded
        );
    }

    function _allowanceHolderTransferFrom(address, address, address, uint256) internal pure override {
        revertConfusedDeputy();
    }

    modifier takerSubmitted() override {
        revert();
        _;
    }

    modifier metaTx(address msgSender, bytes32 witness) override {
        if (_isForwarded()) {
            assembly ("memory-safe") {
                mstore(0x00, 0x1c500e5c) // selector for `ForwarderNotAllowed()`
                revert(0x1c, 0x04)
            }
        }
        if (_operator() == msgSender) {
            revertConfusedDeputy();
        }
        TransientStorage.setWitness(witness);
        TransientStorage.setPayer(msgSender);
        _;
        TransientStorage.clearPayer(msgSender);
        // It should not be possible for this check to revert because the very first thing that a
        // metatransaction does is spend the witness.
        TransientStorage.checkSpentWitness();
    }

    // Solidity inheritance is stupid
    function _msgSender() internal view virtual override(Context, Permit2PaymentBase) returns (address) {
        return super._msgSender();
    }
}

abstract contract Permit2PaymentIntent is Permit2PaymentMetaTxn {
    using FullMath for uint256;
    using SafeTransferLib for IERC20;

    constructor() {
        assert(
            keccak256(bytes(Permit2PaymentIntent._witnessTypeSuffix()))
                == keccak256(abi.encodePacked("Slippage slippage)", SLIPPAGE_TYPE, TOKEN_PERMISSIONS_TYPE))
        );
    }

    function _witnessTypeSuffix() internal pure virtual override returns (string memory) {
        return
        "Slippage slippage)Slippage(address recipient,address buyToken,uint256 minAmountOut)TokenPermissions(address token,uint256 amount)";
    }

    bytes32 private constant _BRIDGE_WALLET_CODEHASH =
        0xe98f46388916ca2f096ea767dc04dddb45d2ca2c2f44e7bcc529d6aded9c11f0;

    function _toCanonicalSellAmount(IERC20 token, uint256 sellAmount) private view returns (uint256) {
        unchecked {
            if (~sellAmount < BASIS) {
                if (_msgSender().codehash == _BRIDGE_WALLET_CODEHASH) {
                    sellAmount = BASIS - ~sellAmount;
                    sellAmount = token.fastBalanceOf(_msgSender()).unsafeMulDiv(sellAmount, BASIS);
                }
            }
        }
        return sellAmount;
    }

    function _permitToSellAmountCalldata(ISignatureTransfer.PermitTransferFrom calldata permit)
        internal
        view
        virtual
        override
        returns (uint256 sellAmount)
    {
        sellAmount = _toCanonicalSellAmount(IERC20(permit.permitted.token), permit.permitted.amount);
    }

    function _permitToSellAmount(ISignatureTransfer.PermitTransferFrom memory permit)
        internal
        view
        virtual
        override
        returns (uint256 sellAmount)
    {
        sellAmount = _toCanonicalSellAmount(IERC20(permit.permitted.token), permit.permitted.amount);
    }
}
