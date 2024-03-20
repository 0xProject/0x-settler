// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {TransientStorageBase} from "./TransientStorageBase.sol";

abstract contract TransientStorage is TransientStorageBase {
    function _get(TSlot s) internal view override returns (uint256 r) {
        assembly ("memory-safe") {
            r := tload(s)
        }
    }

    function _set(TSlot s, uint256 v) internal override {
        assembly ("memory-safe") {
            tstore(s, v)
        }
    }
}
