// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {Context} from "../Context.sol";

interface IERC165 {
    function supportsInterface(bytes4) external view returns (bool);
}

interface IOwnable is IERC165 {
    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    function owner() external view returns (address);

    function transferOwnership(address) external returns (bool);
}

abstract contract AbstractOwnable is IOwnable {
    // This looks stupid (and it is), but this is required due to the glaring
    // deficiencies in Solidity's inheritance system.

    /// This function should be overridden exactly once. This provides the base
    /// implementation. Mixin classes may modify `_requireOwner`.
    function _requireOwnerImpl() internal view virtual;

    function _requireOwner() internal view virtual {
        return _requireOwnerImpl();
    }

    /// This function should be overridden exactly once. This provides the base
    /// implementation. Mixin classes may modify `owner`.
    function _ownerImpl() internal view virtual returns (address);

    function owner() public view virtual override returns (address) {
        return _ownerImpl();
    }

    function _setOwner(address) internal virtual;

    constructor() {
        assert(type(IOwnable).interfaceId == 0x7f5828d0);
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

abstract contract OwnableStorageBase {
    type AddressSlot is bytes32;

    function _ownerSlot() internal pure virtual returns (AddressSlot);

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

abstract contract OwnableImpl is OwnableStorageBase, AbstractOwnable, Context {
    function _ownerImpl() internal view override returns (address) {
        return _get(_ownerSlot());
    }

    function _setOwner(address newOwner) internal virtual override {
        emit OwnershipTransferred(_ownerImpl(), newOwner);
        _set(_ownerSlot(), newOwner);
    }

    error PermissionDenied();
    error ZeroAddress();

    function _requireOwnerImpl() internal view override {
        if (_msgSender() != owner()) {
            revert PermissionDenied();
        }
    }

    function renounceOwnership() public virtual onlyOwner returns (bool) {
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

contract Ownable is OwnableStorage, OwnableImpl {}

abstract contract AbstractTwoStepOwnable is AbstractOwnable {
    /// This function should be overridden exactly once. This provides the base
    /// implementation. Mixin classes may modify `_requirePendingOwner`.
    function _requirePendingOwnerImpl() internal view virtual;

    function _requirePendingOwner() internal view virtual {
        return _requirePendingOwnerImpl();
    }

    /// This function should be overridden exactly once. This provides the base
    /// implementation. Mixin classes may modify `pendingOwner`.
    function _pendingOwnerImpl() internal view virtual returns (address);

    function pendingOwner() public view returns (address) {
        return _pendingOwnerImpl();
    }

    function _setPendingOwner(address) internal virtual;

    /// This modifier is not virtual on purpose; override _requirePendingOwner
    /// instead.
    modifier onlyPendingOwner() {
        _requirePendingOwner();
        _;
    }
}

abstract contract TwoStepOwnableStorageBase is OwnableStorageBase {
    function _pendingOwnerSlot() internal pure virtual returns (AddressSlot);
}

abstract contract TwoStepOwnableStorage is TwoStepOwnableStorageBase, OwnableStorage {
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

abstract contract TwoStepOwnableImpl is AbstractTwoStepOwnable, TwoStepOwnableStorageBase, OwnableImpl {
    function _pendingOwnerImpl() internal view override returns (address) {
        return _get(_pendingOwnerSlot());
    }

    event OwnershipPending(address indexed);

    function _setPendingOwner(address newPendingOwner) internal override {
        emit OwnershipPending(newPendingOwner);
        _set(_pendingOwnerSlot(), newPendingOwner);
    }

    function renounceOwnership() public override returns (bool) {
        if (pendingOwner() != address(0)) {
            _setPendingOwner(address(0));
        }
        return super.renounceOwnership();
    }

    function transferOwnership(address newOwner) public override(IOwnable, OwnableImpl) onlyOwner returns (bool) {
        if (newOwner == address(0)) {
            revert ZeroAddress();
        }
        _setPendingOwner(newOwner);
        return true;
    }

    function _requirePendingOwnerImpl() internal view override {
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

contract TwoStepOwnable is TwoStepOwnableStorage, TwoStepOwnableImpl {}
