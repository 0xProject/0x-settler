// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

abstract contract ReentrancyGuard {
    uint256 private constant _UNLOCKED = 1;
    uint256 private constant _LOCKED = 2;

    uint256 private _lock;

    function _initialize() internal {
        _lock = _UNLOCKED;
    }

    error Reentrancy();

    function _checkLock() private view {
        if (_lock == _LOCKED) {
            revert Reentrancy();
        }
    }

    function _lockLock() private {
        _lock = _LOCKED;
    }

    function _unlockLock() private {
        _lock = _UNLOCKED;
    }

    modifier nonReentrant() {
        _checkLock();
        _lockLock();
        _;
        _unlockLock();
    }
}
