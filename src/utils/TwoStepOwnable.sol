// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC165} from "@forge-std/interfaces/IERC165.sol";
import {AbstractContext} from "../Context.sol";
import {IOwnable} from "../interfaces/IOwnable.sol";

abstract contract AbstractOwnable is IOwnable, AbstractContext {
    // This looks stupid (and it is), but this is required due to the glaring
    // deficiencies in Solidity's inheritance system.

    function _requireOwner() internal view virtual;

    /// This function should be overridden exactly once. This provides the base
    /// implementation. Mixin classes may modify `owner`.
    function _ownerImpl() internal view virtual returns (address);

    function owner() public view virtual override returns (address) {
        return _ownerImpl();
    }

    function _setOwner(address) internal virtual;

    function _permissionDenied() internal pure {
        assembly ("memory-safe") {
            mstore(0x00, 0x1e092104) // selector for `PermissionDenied()`
            revert(0x1c, 0x04)
        }
    }

    function _zeroAddress() internal pure {
        assembly ("memory-safe") {
            mstore(0x00, 0xd92e233d) // selector for `ZeroAddress()`
            revert(0x1c, 0x04)
        }
    }

    constructor() {
        assert(type(IOwnable).interfaceId == 0x7f5828d0);
        assert(type(IERC165).interfaceId == 0x01ffc9a7);
    }

    /// @inheritdoc IERC165
    function supportsInterface(bytes4 interfaceId) public view virtual override returns (bool) {
        return interfaceId == type(IERC165).interfaceId || interfaceId == type(IOwnable).interfaceId;
    }

    /// This modifier is not virtual on purpose; override `_requireOwner` instead.
    modifier onlyOwner() {
        _requireOwner();
        _;
    }
}

abstract contract AddressSlotStorage {
    type AddressSlot is bytes32;

    function _get(AddressSlot s) internal view returns (address r) {
        assembly ("memory-safe") {
            r := sload(s)
        }
    }

    function _set(AddressSlot s, address v) internal {
        assembly ("memory-safe") {
            sstore(
                s,
                or(
                    and(0xffffffffffffffffffffffffffffffffffffffff, v),
                    and(0xffffffffffffffffffffffff0000000000000000000000000000000000000000, sload(s))
                )
            )
        }
    }
}

abstract contract OwnableStorageBase is AddressSlotStorage {
    function _ownerSlot() internal pure virtual returns (AddressSlot);
}

abstract contract OwnableStorage is OwnableStorageBase {
    address private _owner;

    function _ownerSlot() internal pure override returns (AddressSlot r) {
        assembly ("memory-safe") {
            r := _owner.slot
        }
    }

    constructor() {
        assert(AddressSlot.unwrap(_ownerSlot()) == bytes32(0));
    }
}

abstract contract OwnableBase is AbstractOwnable {
    function renounceOwnership() public virtual returns (bool);
}

abstract contract OwnableImpl is OwnableStorageBase, OwnableBase {
    function _ownerImpl() internal view override returns (address) {
        return _get(_ownerSlot());
    }

    function _setOwner(address newOwner) internal virtual override {
        emit OwnershipTransferred(_ownerImpl(), newOwner);
        _set(_ownerSlot(), newOwner);
    }

    function _requireOwner() internal view virtual override {
        if (owner() != _msgSender()) {
            _permissionDenied();
        }
    }

    function renounceOwnership() public virtual override onlyOwner returns (bool) {
        _setOwner(address(0));
        return true;
    }

    function transferOwnership(address newOwner) public virtual override onlyOwner returns (bool) {
        if (newOwner == address(0)) {
            _zeroAddress();
        }
        _setOwner(newOwner);
        return true;
    }
}

abstract contract Ownable is OwnableStorage, OwnableImpl {}

abstract contract AbstractTwoStepOwnable is AbstractOwnable {
    function _requirePendingOwner() internal view virtual;

    /// This function should be overridden exactly once. This provides the base
    /// implementation. Mixin classes may modify `pendingOwner`.
    function _pendingOwnerImpl() internal view virtual returns (address);

    function pendingOwner() public view virtual returns (address) {
        return _pendingOwnerImpl();
    }

    function _setPendingOwner(address) internal virtual;

    /// This modifier is not virtual on purpose; override `_requirePendingOwner`
    /// instead.
    modifier onlyPendingOwner() {
        _requirePendingOwner();
        _;
    }

    event OwnershipPending(address indexed);
}

abstract contract TwoStepOwnableStorageBase is AddressSlotStorage {
    function _pendingOwnerSlot() internal pure virtual returns (AddressSlot);
}

abstract contract TwoStepOwnableStorage is TwoStepOwnableStorageBase {
    address private _pendingOwner;

    function _pendingOwnerSlot() internal pure override returns (AddressSlot r) {
        assembly ("memory-safe") {
            r := _pendingOwner.slot
        }
    }

    constructor() {
        assert(AddressSlot.unwrap(_pendingOwnerSlot()) == bytes32(uint256(1)));
    }
}

abstract contract TwoStepOwnableBase is OwnableBase, AbstractTwoStepOwnable {}

abstract contract TwoStepOwnableImpl is TwoStepOwnableStorageBase, TwoStepOwnableBase {
    function _pendingOwnerImpl() internal view override returns (address) {
        return _get(_pendingOwnerSlot());
    }

    function _setPendingOwner(address newPendingOwner) internal override {
        emit OwnershipPending(newPendingOwner);
        _set(_pendingOwnerSlot(), newPendingOwner);
    }

    function renounceOwnership() public virtual override onlyOwner returns (bool) {
        if (pendingOwner() != address(0)) {
            _setPendingOwner(address(0));
        }
        _setOwner(address(0));
        return true;
    }

    function transferOwnership(address newOwner) public virtual override onlyOwner returns (bool) {
        if (newOwner == address(0)) {
            _zeroAddress();
        }
        _setPendingOwner(newOwner);
        return true;
    }

    function _requirePendingOwner() internal view override {
        if (pendingOwner() != _msgSender()) {
            _permissionDenied();
        }
    }

    function acceptOwnership() public onlyPendingOwner returns (bool) {
        _setOwner(_msgSender());
        _setPendingOwner(address(0));
        return true;
    }

    function rejectOwnership() public onlyPendingOwner returns (bool) {
        _setPendingOwner(address(0));
        return true;
    }
}

abstract contract TwoStepOwnable is OwnableStorage, OwnableImpl, TwoStepOwnableStorage, TwoStepOwnableImpl {
    function renounceOwnership() public override(OwnableImpl, TwoStepOwnableImpl) returns (bool) {
        return TwoStepOwnableImpl.renounceOwnership();
    }

    function transferOwnership(address newOwner) public override(OwnableImpl, TwoStepOwnableImpl) returns (bool) {
        return TwoStepOwnableImpl.transferOwnership(newOwner);
    }
}
