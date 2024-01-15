// SPDX-License-Identifier: MIT
pragma solidity 0.8.21;

import {AbstractOwnable} from "../deployer/TwoStepOwnable.sol";

import {Revert} from "../utils/Revert.sol";

interface IERC1967Proxy {
    event Upgraded(address indexed implementation);

    function implementation() external view returns (address);

    function upgrade(address newImplementation) external payable;

    function upgradeAndCall(address newImplementation, bytes calldata data) external payable;
}

abstract contract ERC1967UUPSUpgradeable is AbstractOwnable, IERC1967Proxy {
    error OnlyProxy();
    error InterferedWithImplementation(address expected, address actual);
    error InterferedWithRollback(bool expected, bool actual);
    error RollbackFailed();
    error InitializationFailed();

    using Revert for bytes;

    address private immutable _thisCopy;

    uint256 private constant _IMPLEMENTATION_SLOT = 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc;
    uint256 private constant _ROLLBACK_SLOT = 0x4910fdfa16fed3260ed0e7147f7cc6da11a60208b5b9406d12a635614ffd9143;

    uint256 private constant _NO_ROLLBACK = 2;
    uint256 private constant _ROLLBACK_IN_PROGRESS = 3;

    constructor() {
        _thisCopy = address(this);
        assert(_IMPLEMENTATION_SLOT == uint256(keccak256("eip1967.proxy.implementation")) - 1);
        assert(_ROLLBACK_SLOT == uint256(keccak256("eip1967.proxy.rollback")) - 1);
    }

    function implementation() public view virtual override returns (address result) {
        assembly ("memory-safe") {
            result := sload(_IMPLEMENTATION_SLOT)
        }
    }

    function _setImplementation(address newImplementation) private {
        assembly ("memory-safe") {
            sstore(_IMPLEMENTATION_SLOT, newImplementation)
        }
    }

    function _isRollback() internal view returns (bool) {
        uint256 slotValue;
        assembly ("memory-safe") {
            slotValue := sload(_ROLLBACK_SLOT)
        }
        return slotValue == _ROLLBACK_IN_PROGRESS;
    }

    function _setRollback(bool rollback) private {
        uint256 slotValue = rollback ? _ROLLBACK_IN_PROGRESS : _NO_ROLLBACK;
        assembly ("memory-safe") {
            sstore(_ROLLBACK_SLOT, slotValue)
        }
    }

    function _requireProxy() internal view {
        if (implementation() != _thisCopy || address(this) == _thisCopy) {
            revert OnlyProxy();
        }
    }

    modifier onlyProxy() {
        _requireProxy();
        _;
    }

    function supportsInterface(bytes4 interfaceId) public view virtual override onlyProxy returns (bool) {
        return super.supportsInterface(interfaceId);
    }

    function _requireOwner() internal view virtual override onlyProxy {
        super._requireOwner();
    }

    function owner() public view virtual override onlyProxy returns (address) {
        return super.owner();
    }

    function _initialize() internal virtual onlyProxy {
        _setRollback(false);
    }

    // This hook exists for schemes that append authenticated metadata to calldata
    // (e.g. ERC2771). If msg.sender during the upgrade call is the authenticator,
    // the metadata must be copied from the outer calldata into the delegatecall
    // calldata to ensure that any logic in the new implementation that inspects
    // msg.sender and decodes the authenticated metadata gets the correct result.
    function _encodeDelegateCall(bytes memory callData) internal view virtual returns (bytes memory) {
        return callData;
    }

    function _delegateCall(address impl, bytes memory data, bytes memory err) internal returns (bytes memory) {
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

    function _checkImplementation(address newImplementation, bool rollback) internal virtual {
        if (newImplementation != implementation()) {
            revert InterferedWithImplementation(newImplementation, implementation());
        }
        if (rollback != _isRollback()) {
            revert InterferedWithRollback(rollback, _isRollback());
        }
    }

    function _checkRollback(bool rollback) private {
        if (!rollback) {
            _setRollback(true);
            address newImplementation = implementation();
            _delegateCall(
                newImplementation,
                abi.encodeCall(this.upgrade, (_thisCopy)),
                abi.encodeWithSelector(RollbackFailed.selector)
            );
            _setRollback(false);
            if (implementation() != _thisCopy) {
                revert RollbackFailed();
            }
            emit Upgraded(newImplementation);
            _setImplementation(newImplementation);
        }
    }

    function upgrade(address newImplementation) public payable virtual override onlyOwner {
        bool rollback = _isRollback();
        _setImplementation(newImplementation);
        _checkRollback(rollback);
    }

    function upgradeAndCall(address newImplementation, bytes calldata data) public payable virtual override onlyOwner {
        bool rollback = _isRollback();
        _setImplementation(newImplementation);
        _delegateCall(newImplementation, data, abi.encodeWithSelector(InitializationFailed.selector));
        _checkImplementation(newImplementation, rollback);
        _checkRollback(rollback);
    }
}
