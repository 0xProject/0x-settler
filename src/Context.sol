// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

/// @title AbstractContext
/// @notice Abstract contract providing context for message sender and data
abstract contract AbstractContext {
    function _msgSender() internal view virtual returns (address);

    function _msgData() internal view virtual returns (bytes calldata);

    function _isForwarded() internal view virtual returns (bool);
}

abstract contract Context is AbstractContext {
    function _msgSender() internal view virtual override returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual override returns (bytes calldata) {
        return msg.data;
    }

    function _isForwarded() internal view virtual override returns (bool) {
        return false;
    }
}
