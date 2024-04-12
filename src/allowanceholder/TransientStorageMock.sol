// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {TransientStorageBase} from "./TransientStorageBase.sol";

abstract contract TransientStorageMock is TransientStorageBase {
    function _get(TSlot s) internal view override returns (uint256 r) {
        assembly ("memory-safe") {
            r := sload(s)
        }
    }

    function _set(TSlot s, uint256 v) internal override {
        assembly ("memory-safe") {
            sstore(s, v)
        }
    }

    bytes32 private _sentinel;

    constructor() {
        uint256 _sentinelSlot;
        assembly ("memory-safe") {
            _sentinelSlot := _sentinel.slot
        }
        assert(_sentinelSlot == 0);
    }
}
