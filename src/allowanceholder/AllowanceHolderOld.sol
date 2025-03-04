// SPDX-License-Identifier: MIT
pragma solidity =0.8.28;

import {AllowanceHolderBase} from "./AllowanceHolderBase.sol";
import {TransientStorageMock} from "./TransientStorageMock.sol";

/// @custom:security-contact security@0x.org
contract AllowanceHolder is TransientStorageMock, AllowanceHolderBase {
    // This is here as a deploy-time check that AllowanceHolder doesn't have any
    // state. If it did, it would interfere with TransientStorageMock.
    bytes32 private _sentinel;

    constructor() {
        require(address(this) == 0x0000000000005E88410CcDFaDe4a5EfaE4b49562 || block.chainid == 31337);
        uint256 _sentinelSlot;
        assembly ("memory-safe") {
            _sentinelSlot := _sentinel.slot
        }
        assert(_sentinelSlot == 1);
    }
}
