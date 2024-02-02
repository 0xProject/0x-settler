// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

abstract contract TransientStorageBase {
    type TSlot is bytes32;

    function _get(TSlot s) internal view virtual returns (uint256);

    function _set(TSlot s, uint256 v) internal virtual;
}
