// SPDX-License-Identifier: MIT
pragma solidity 0.8.24;

import {AbstractContext} from "../Context.sol";
import {
    AbstractOwnable,
    OwnableImpl,
    OwnableStorageBase,
    TwoStepOwnableImpl,
    TwoStepOwnableStorageBase
} from "../deployer/TwoStepOwnable.sol";

import {Revert} from "../utils/Revert.sol";
import {ItoA} from "../utils/ItoA.sol";

interface IERC1967Proxy {
    event Upgraded(address indexed implementation);

    function implementation() external view returns (address);

    function version() external view returns (string memory);

    function upgrade(address newImplementation) external payable returns (bool);

    function upgradeAndCall(address newImplementation, bytes calldata data) external payable returns (bool);
}

abstract contract AbstractUUPSUpgradeable {
    address internal immutable _implementation;
    uint256 internal immutable _implVersion;

    constructor(uint256 newVersion) {
        _implementation = address(this);
        _implVersion = newVersion;
    }

    error OnlyProxy();

    function _requireProxy() private view {
        address impl = _implementation;
        if (implementation() != impl || address(this) == impl) {
            revert OnlyProxy();
        }
    }

    modifier onlyProxy() {
        _requireProxy();
        _;
    }

    function implementation() public view virtual returns (address);
}

/// The upgrade mechanism for this proxy is slightly more convoluted than the
/// previously-standard rollback-checking ERC1967 UUPS proxy. The standard
/// rollback check uses the value of the ERC1967 rollback slot to avoid infinite
/// recursion. The old implementation's `upgrade` or `upgradeAndCall` sets the
/// ERC1967 implementation slot to the new implementation, then calls `upgrade`
/// on the new implementation to attempt to set the value of the implementation
/// slot *back to the old implementation*. This is checked, and the value of the
/// implementation slot is re-set to the new implementation.
///
/// This proxy abuses the ERC1967 rollback slot to store a version number which
/// must be incremented on each upgrade. This mechanism follows the same general
/// outline as the previously-standard version. The old implementation's
/// `upgrade` or `upgradeAndCall` sets the ERC1967 implementation slot to the
/// new implementation, then calls `upgrade` on the new implementation. The new
/// implementation's `upgrade` sets the implementation slot back to the old
/// implementation *and* advances the rollback slot to the new version
/// number. The old implementation then checks the value of both the
/// implementation and rollback slots before re-setting the implementation slot
/// to the new implementation.
abstract contract ERC1967UUPSUpgradeable is AbstractContext, AbstractOwnable, IERC1967Proxy, AbstractUUPSUpgradeable {
    using Revert for bytes;

    error VersionMismatch(uint256 oldVersion, uint256 newVersion);
    error InterferedWithImplementation(address expected, address actual);
    error InterferedWithVersion(uint256 expected, uint256 actual);
    error DidNotIncrementVersion(uint256 current, uint256 next);
    error RollbackFailed(address expected, address actual);
    error InitializationFailed();

    uint256 private constant _IMPLEMENTATION_SLOT = 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc;
    uint256 private constant _ROLLBACK_SLOT = 0x4910fdfa16fed3260ed0e7147f7cc6da11a60208b5b9406d12a635614ffd9143;

    constructor(uint256 newVersion) AbstractUUPSUpgradeable(newVersion) {
        assert(_IMPLEMENTATION_SLOT == uint256(keccak256("eip1967.proxy.implementation")) - 1);
        assert(_ROLLBACK_SLOT == uint256(keccak256("eip1967.proxy.rollback")) - 1);
    }

    function implementation()
        public
        view
        virtual
        override(IERC1967Proxy, AbstractUUPSUpgradeable)
        returns (address result)
    {
        assembly ("memory-safe") {
            result := sload(_IMPLEMENTATION_SLOT)
        }
    }

    function version() public view virtual override returns (string memory) {
        return ItoA.itoa(_storageVersion());
    }

    function _setImplementation(address newImplementation) private {
        assembly ("memory-safe") {
            sstore(_IMPLEMENTATION_SLOT, and(0xffffffffffffffffffffffffffffffffffffffff, newImplementation))
        }
    }

    function _storageVersion() private view returns (uint256 result) {
        assembly ("memory-safe") {
            result := sload(_ROLLBACK_SLOT)
        }
    }

    function _setVersion(uint256 newVersion) private {
        assembly ("memory-safe") {
            sstore(_ROLLBACK_SLOT, newVersion)
        }
    }

    function supportsInterface(bytes4 interfaceId) public view virtual override onlyProxy returns (bool) {
        return super.supportsInterface(interfaceId);
    }

    // This makes `onlyOwner` imply `onlyProxy`
    function owner() public view virtual override onlyProxy returns (address) {
        return super.owner();
    }

    function _initialize() internal virtual onlyProxy {
        if (_storageVersion() + 1 != _implVersion) {
            revert VersionMismatch(_storageVersion(), _implVersion);
        }
    }

    function _delegateCall(address impl, bytes memory data, bytes memory err) private returns (bytes memory) {
        (bool success, bytes memory returnData) = impl.delegatecall(_encodeDelegateCall(data));
        if (!success) {
            if (returnData.length > 0) {
                returnData._revert();
            } else {
                err._revert();
            }
        }
        return returnData;
    }

    function _checkRollback(address newImplementation, uint256 oldVersion, uint256 implVersion) private {
        if (oldVersion == implVersion) {
            _delegateCall(
                newImplementation,
                abi.encodeCall(IERC1967Proxy.upgrade, (_implementation)),
                abi.encodeWithSelector(RollbackFailed.selector, _implementation, newImplementation)
            );
            if (implementation() != _implementation) {
                revert RollbackFailed(_implementation, implementation());
            }
            if (_storageVersion() <= implVersion) {
                revert DidNotIncrementVersion(implVersion, _storageVersion());
            }
            _setImplementation(newImplementation);
            emit Upgraded(newImplementation);
        }
    }

    /// @notice attempting to upgrade to a new implementation with a version
    ///         number that does not increase will result in infinite recursion
    ///         and a revert
    function upgrade(address newImplementation) public payable virtual override onlyOwner returns (bool) {
        uint256 oldVersion = _storageVersion();
        uint256 implVersion = _implVersion;
        _setImplementation(newImplementation);
        _setVersion(implVersion);
        _checkRollback(newImplementation, oldVersion, implVersion);
        return true;
    }

    /// @notice attempting to upgrade to a new implementation with a version
    ///         number that does not increase will result in infinite recursion
    ///         and a revert
    function upgradeAndCall(address newImplementation, bytes calldata data)
        public
        payable
        virtual
        override
        onlyOwner
        returns (bool)
    {
        uint256 oldVersion = _storageVersion();
        uint256 implVersion = _implVersion;
        _setImplementation(newImplementation);
        _delegateCall(newImplementation, data, abi.encodeWithSelector(InitializationFailed.selector));
        if (implementation() != newImplementation) {
            revert InterferedWithImplementation(newImplementation, implementation());
        }
        if (_storageVersion() != oldVersion) {
            revert InterferedWithVersion(oldVersion, _storageVersion());
        }
        _setVersion(implVersion);
        _checkRollback(newImplementation, oldVersion, implVersion);
        return true;
    }
}

abstract contract ERC1967OwnableStorage is OwnableStorageBase {
    uint256 private constant _ADMIN_SLOT = 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103;

    function _ownerSlot() internal pure override returns (AddressSlot r) {
        assembly ("memory-safe") {
            r := _ADMIN_SLOT
        }
    }

    constructor() {
        assert(AddressSlot.unwrap(_ownerSlot()) == bytes32(uint256(keccak256("eip1967.proxy.admin")) - 1));
    }
}

abstract contract ERC1967Ownable is OwnableImpl, ERC1967OwnableStorage {
    event AdminChanged(address indexed prev, address indexed curr);

    function _setOwner(address newOwner) internal override {
        emit AdminChanged(_ownerImpl(), newOwner);
        super._setOwner(newOwner);
    }
}

abstract contract ERC1967TwoStepOwnableStorage is ERC1967OwnableStorage, TwoStepOwnableStorageBase {
    // This slot is nonstandard, but follows a similar pattern to ERC1967
    uint256 private constant _PENDING_ADMIN_SLOT = 0x6ed8ad4e485c433a46d43a225e2ebe6a14259468c9e0ee3a0c38eefca7d49f56;

    function _pendingOwnerSlot() internal pure override returns (AddressSlot r) {
        assembly ("memory-safe") {
            r := _PENDING_ADMIN_SLOT
        }
    }

    constructor() {
        assert(
            AddressSlot.unwrap(_pendingOwnerSlot()) == bytes32(uint256(keccak256("eip1967.proxy.admin.pending")) - 1)
        );
    }
}

abstract contract ERC1967TwoStepOwnable is TwoStepOwnableImpl, ERC1967TwoStepOwnableStorage {}
