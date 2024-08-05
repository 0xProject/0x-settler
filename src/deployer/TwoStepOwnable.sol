// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {AbstractContext} from "../Context.sol";
import {IERC165} from "forge-std/interfaces/IERC165.sol";

interface IOwnable is IERC165 {
    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    function owner() external view returns (address);

    function transferOwnership(address) external returns (bool);

    error PermissionDenied();
    error ZeroAddress();
}

abstract contract AbstractOwnable is IOwnable {
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

    constructor() {
        assert(type(IOwnable).interfaceId == 0x7f5828d0);
        assert(type(IERC165).interfaceId == 0x01ffc9a7);
    }

    function supportsInterface(bytes4 interfaceId) public view virtual override returns (bool) {
        return interfaceId == type(IERC165).interfaceId || interfaceId == type(IOwnable).interfaceId;
    }

    /// This modifier is not virtual on purpose; override _requireOwner instead.
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
            sstore(s, v)
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

abstract contract OwnableBase is AbstractContext, AbstractOwnable {
    function renounceOwnership() public virtual returns (bool);
}

abstract contract OwnableImpl is OwnableStorageBase, OwnableBase {
    function _ownerImpl() internal view override returns (address) {
        return _get(_ownerSlot());
    }

    function _setOwner(address newOwner) internal virtual override {
        emit OwnershipTransferred(owner(), newOwner);
        _set(_ownerSlot(), newOwner);
    }

    function _requireOwner() internal view override {
        if (_msgSender() != owner()) {
            revert PermissionDenied();
        }
    }

    function renounceOwnership() public virtual override onlyOwner returns (bool) {
        _setOwner(address(0));
        return true;
    }

    function transferOwnership(address newOwner) public virtual override onlyOwner returns (bool) {
        if (newOwner == address(0)) {
            revert ZeroAddress();
        }
        _setOwner(newOwner);
        return true;
    }
}

abstract contract Ownable is OwnableStorage, OwnableImpl {}

abstract contract AbstractTwoStepOwnable is AbstractOwnable {
    function _requirePendingOwner() internal view virtual;

    function pendingOwner() public view virtual returns (address);

    function _setPendingOwner(address) internal virtual;

    /// This modifier is not virtual on purpose; override _requirePendingOwner
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
    function pendingOwner() public view override returns (address) {
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
            revert ZeroAddress();
        }
        _setPendingOwner(newOwner);
        return true;
    }

    function _requirePendingOwner() internal view override {
        if (_msgSender() != pendingOwner()) {
            revert PermissionDenied();
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
