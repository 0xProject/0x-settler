// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {
    CallbackNotSpent,
    ConfusedDeputy,
    PayerSpent,
    ReentrantCallback,
    ReentrantMetatransaction,
    ReentrantPayer,
    WitnessNotSpent
} from "./SettlerErrors.sol";

import {PaymentAbstract} from "./PaymentAbstract.sol";
import {AbstractContext, Context} from "../Context.sol";

import {Revert} from "../utils/Revert.sol";

library TransientStorage {
    // bytes32((uint256(keccak256("operator slot")) - 1) & type(uint128).max)
    bytes32 private constant _OPERATOR_SLOT = 0x0000000000000000000000000000000007f49fa1cdccd5c65a7d4860ce3abbe9;
    // bytes32((uint256(keccak256("witness slot")) - 1) & type(uint128).max)
    bytes32 private constant _WITNESS_SLOT = 0x00000000000000000000000000000000e44a235ac7aebfbc05485e093720deaa;
    // bytes32((uint256(keccak256("payer slot")) - 1) & type(uint128).max)
    bytes32 private constant _PAYER_SLOT = 0x00000000000000000000000000000000c824a45acd1e9517bb0cb8d0d5cde893;

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
            assembly ("memory-safe") {
                mstore(0x00, 0xe758b8d5) // selector for `ConfusedDeputy()`
                revert(0x1c, 0x04)
            }
        }
        uint256 callbackInt;
        assembly ("memory-safe") {
            callbackInt := tload(_OPERATOR_SLOT)
        }
        if (callbackInt != 0) {
            // It should be impossible to reach this error because the first thing the fallback does
            // is clear the operator. It's also not possible to reenter the entrypoint function
            // because `_PAYER_SLOT` is an implicit reentrancy guard.
            assembly ("memory-safe") {
                mstore(0x00, 0xab7646c4) // selector for `ReentrantCallback(uint256)`
                mstore(0x20, callbackInt)
                revert(0x1c, 0x24)
            }
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
            assembly ("memory-safe") {
                mstore(0x00, 0xd66fcc38) // selector for `CallbackNotSpent(uint256)`
                mstore(0x20, callbackInt)
                revert(0x1c, 0x24)
            }
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
            assembly ("memory-safe") {
                mstore(0x00, 0x9936cbab) // selector for `ReentrantMetatransaction(bytes32)`
                mstore(0x20, currentWitness)
                revert(0x1c, 0x24)
            }
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
            assembly ("memory-safe") {
                mstore(0x00, 0xe25527c2) // selector for `WitnessNotSpent(bytes32)`
                mstore(0x20, currentWitness)
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
        if (payer == address(0)) {
            assembly ("memory-safe") {
                mstore(0x00, 0xe758b8d5) // selector for `ConfusedDeputy()`
                revert(0x1c, 0x04)
            }
        }
        address oldPayer;
        assembly ("memory-safe") {
            oldPayer := tload(_PAYER_SLOT)
        }
        if (oldPayer != address(0)) {
            assembly ("memory-safe") {
                mstore(0x14, oldPayer)
                mstore(0x00, 0x7407c0f8000000000000000000000000) // selector for `ReentrantPayer(address)` with `oldPayer`'s padding
                revert(0x10, 0x24)
            }
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
            assembly ("memory-safe") {
                mstore(0x00, 0x5149e795) // selector for `PayerSpent()`
                revert(0x1c, 0x04)
            }
        }
        assembly ("memory-safe") {
            tstore(_PAYER_SLOT, 0x00)
        }
    }
}

abstract contract PaymentBase is Context, PaymentAbstract {
    using Revert for bool;

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

    function _invokeCallback(bytes calldata data) internal returns (bytes memory) {
        // Retrieve callback and perform call with untrusted calldata
        (bytes4 selector, function (bytes calldata) internal returns (bytes memory) callback, address operator) =
            TransientStorage.getAndClearOperatorAndCallback();
        require(bytes4(data) == selector);
        require(msg.sender == operator);
        return callback(data[4:]);
    }
}
