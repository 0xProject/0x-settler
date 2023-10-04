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

abstract contract Ownable is IOwnable {
    address public override owner;

    function supportsInterface(bytes4 interfaceId) public view virtual override returns (bool) {
        return interfaceId == type(IERC165).interfaceId || interfaceId == type(IOwnable).interfaceId;
    }

    error PermissionDenied();
    error ZeroAddress();

    function _requireOwner() private view {
        if (msg.sender != owner) {
            revert PermissionDenied();
        }
    }

    modifier onlyOwner() {
        _requireOwner();
        _;
    }

    function renounceOwnership() public virtual onlyOwner returns (bool) {
        emit OwnershipTransferred(owner, address(0));
        owner = address(0);
        return true;
    }

    function transferOwnership(address newOwner) public virtual override onlyOwner returns (bool) {
        if (newOwner == address(0)) {
            revert ZeroAddress();
        }
        emit OwnershipTransferred(owner, newOwner);
        owner = newOwner;
        return true;
    }
}

abstract contract TwoStepOwnable is Ownable {
    address public pendingOwner;

    event OwnershipPending(address indexed);

    function renounceOwnership() public override returns (bool) {
        if (pendingOwner != address(0)) {
            emit OwnershipPending(address(0));
            pendingOwner = address(0);
        }
        return super.renounceOwnership();
    }

    function transferOwnership(address newOwner) public override onlyOwner returns (bool) {
        if (newOwner == address(0)) {
            revert ZeroAddress();
        }
        emit OwnershipPending(newOwner);
        pendingOwner = newOwner;
        return true;
    }

    function _requirePendingOwner() private view {
        if (msg.sender != pendingOwner) {
            revert PermissionDenied();
        }
    }

    function acceptOwnership() public returns (bool) {
        _requirePendingOwner();
        emit OwnershipTransferred(owner, msg.sender);
        owner = msg.sender;
        emit OwnershipPending(address(0));
        pendingOwner = address(0);
        return true;
    }

    function rejectOwnership() public returns (bool) {
        _requirePendingOwner();
        emit OwnershipPending(address(0));
        pendingOwner = address(0);
        return true;
    }
}
