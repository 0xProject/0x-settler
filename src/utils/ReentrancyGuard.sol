// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {ContextAbstract} from "../Context.sol";

abstract contract ReentrancyGuard is ContextAbstract {
    uint256 private constant _UNLOCKED = 1;
    uint256 private constant _LOCKED = 2;

    uint256 private _lock;

    function _initialize() internal {
        _lock = _UNLOCKED;
    }

    error Reentrancy();

    modifier nonReentrant() {
        bool isForwarded = _isForwarded();
        if (!isForwarded) {
            if (_lock == _LOCKED) {
                revert Reentrancy();
            }
            _lock = _LOCKED;
        }
        _;
        if (!isForwarded) {
            _lock = _UNLOCKED;
        }
    }
}
