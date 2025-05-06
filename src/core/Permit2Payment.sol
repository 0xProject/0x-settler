// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {
    ConfusedDeputy,
    ForwarderNotAllowed,
    InvalidSignatureLen,
    SignatureExpired
} from "./SettlerErrors.sol";

import {SettlerAbstract} from "../SettlerAbstract.sol";
import {Panic} from "../utils/Panic.sol";
import {FullMath} from "../vendor/FullMath.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";

import {AbstractContext, Context} from "../Context.sol";
import {AllowanceHolderContext, ALLOWANCE_HOLDER} from "../allowanceholder/AllowanceHolderContext.sol";
import {TransientStorage, PaymentBase} from "./PaymentBase.sol";

abstract contract Permit2PaymentBase is SettlerAbstract, PaymentBase {
    /// @dev Permit2 address
    ISignatureTransfer internal constant _PERMIT2 = ISignatureTransfer(0x000000000022D473030F116dDEE9F6B43aC78BA3);

    function _isRestrictedTarget(address target) internal pure virtual override returns (bool) {
        return target == address(_PERMIT2);
    }
}

abstract contract Permit2Payment is Permit2PaymentBase {
    fallback(bytes calldata) external virtual returns (bytes memory) {
        return _invokeCallback(_msgData());
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
            if iszero(call(gas(), __PERMIT2, 0x00, add(0x1c, ptr), add(0x184, add(witnessTypeStringLength, sigLength)), 0x00, 0x00)) {
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
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
        if (sellAmount > type(uint256).max - BASIS) {
            unchecked {
                sellAmount -= type(uint256).max - BASIS;
            }
            sellAmount = IERC20(permit.permitted.token).fastBalanceOf(_msgSender()).mulDiv(sellAmount, BASIS);
        }
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
            sellAmount = IERC20(permit.permitted.token).fastBalanceOf(_msgSender()).mulDiv(sellAmount, BASIS);
        }
    }

    function _isRestrictedTarget(address target) internal pure virtual override returns (bool) {
        return target == address(ALLOWANCE_HOLDER) || super._isRestrictedTarget(target);
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
                    returndatacopy(ptr, 0x00, returndatasize())
                    revert(ptr, returndatasize())
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

        // Solidity won't let us reference the constant `ALLOWANCE_HOLDER` in assembly, but this
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
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
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
    function _isForwarded() internal view virtual override(AbstractContext, Context, AllowanceHolderContext) returns (bool) {
        return super._isForwarded();
    }

    function _msgData() internal view virtual override(AbstractContext, Context, AllowanceHolderContext) returns (bytes calldata) {
        return super._msgData();
    }

    function _msgSender()
        internal
        view
        virtual
        override(AbstractContext, AllowanceHolderContext, PaymentBase)
        returns (address)
    {
        return super._msgSender();
    }
}

// DANGER: the order of the base contracts here is very significant for the use of `super` below
// (and in derived contracts). Do not change this order.
abstract contract Permit2PaymentMetaTxn is Permit2Payment {
    constructor() {
        assert(_hasMetaTxn());
    }

    function _permitToSellAmountCalldata(ISignatureTransfer.PermitTransferFrom calldata permit)
        internal
        pure
        override
        returns (uint256)
    {
        return permit.permitted.amount;
    }

    function _permitToSellAmount(ISignatureTransfer.PermitTransferFrom memory permit)
        internal
        pure
        virtual
        override
        returns (uint256)
    {
        return permit.permitted.amount;
    }

    function _witnessTypeSuffix() internal pure virtual returns (string memory) {
        return string(
            abi.encodePacked(
                "SlippageAndActions slippageAndActions)", SLIPPAGE_AND_ACTIONS_TYPE, TOKEN_PERMISSIONS_TYPE
            )
        );
    }

    function _transferFrom(
        ISignatureTransfer.PermitTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails memory transferDetails,
        bytes memory sig,
        bool isForwarded // must be false
    ) internal override {
        bytes32 witness = TransientStorage.getAndClearWitness();
        if (witness == bytes32(0)) {
            assembly ("memory-safe") {
                mstore(0x00, 0xe758b8d5) // selector for `ConfusedDeputy()`
                revert(0x1c, 0x04)
            }
        }
        _transferFromIKnowWhatImDoing(
            permit, transferDetails, _msgSender(), witness, _witnessTypeSuffix(), sig, isForwarded
        );
    }

    function _allowanceHolderTransferFrom(address, address, address, uint256) internal pure override {
        assembly ("memory-safe") {
            mstore(0x00, 0xe758b8d5) // selector for `ConfusedDeputy()`
            revert(0x1c, 0x04)
        }
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
        TransientStorage.setWitness(witness);
        TransientStorage.setPayer(msgSender);
        _;
        TransientStorage.clearPayer(msgSender);
        // It should not be possible for this check to revert because the very first thing that a
        // metatransaction does is spend the witness.
        TransientStorage.checkSpentWitness();
    }
}

abstract contract Permit2PaymentIntent is Permit2PaymentMetaTxn {
    function _witnessTypeSuffix() internal pure virtual override returns (string memory) {
        return string(abi.encodePacked("Slippage slippage)", SLIPPAGE_TYPE, TOKEN_PERMISSIONS_TYPE));
    }
}
