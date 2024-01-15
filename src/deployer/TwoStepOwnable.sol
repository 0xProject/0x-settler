// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

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

    function owner() public view virtual returns (address) {
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

abstract contract Ownable is AbstractOwnable {
    address private _owner;

    function _ownerImpl() internal view override returns (address) {
        return _owner;
    }

    function _setOwner(address newOwner) internal override {
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }

    error PermissionDenied();
    error ZeroAddress();

    function _requireOwnerImpl() internal view override {
        if (msg.sender != owner()) {
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

abstract contract AbstractTwoStepOwnable is AbstractOwnable {
    event OwnershipPending(address indexed);

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

abstract contract TwoStepOwnable is AbstractTwoStepOwnable, Ownable {
    address private _pendingOwner;

    function _pendingOwnerImpl() internal view override returns (address) {
        return _pendingOwner;
    }

    function _setPendingOwner(address newPendingOwner) internal override {
        emit OwnershipPending(newPendingOwner);
        _pendingOwner = newPendingOwner;
    }

    function renounceOwnership() public override returns (bool) {
        if (pendingOwner() != address(0)) {
            _setPendingOwner(address(0));
        }
        return super.renounceOwnership();
    }

    function transferOwnership(address newOwner) public override(IOwnable, Ownable) onlyOwner returns (bool) {
        if (newOwner == address(0)) {
            revert ZeroAddress();
        }
        _setPendingOwner(newOwner);
        return true;
    }

    function _requirePendingOwnerImpl() internal view override {
        if (msg.sender != pendingOwner()) {
            revert PermissionDenied();
        }
    }

    function acceptOwnership() public onlyPendingOwner returns (bool) {
        _setOwner(msg.sender);
        _setPendingOwner(address(0));
        return true;
    }

    function rejectOwnership() public onlyPendingOwner returns (bool) {
        _setPendingOwner(address(0));
        return true;
    }
}
