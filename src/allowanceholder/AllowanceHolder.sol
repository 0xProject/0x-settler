// SPDX-License-Identifier: MIT
pragma solidity =0.8.28;

import {AllowanceHolderBase} from "./AllowanceHolderBase.sol";
import {TransientStorage} from "./TransientStorage.sol";

/// @custom:security-contact security@0x.org
contract AllowanceHolder is TransientStorage, AllowanceHolderBase {
    constructor() {
        // Check that we're on a chain with transient storage support
        assembly ("memory-safe") {
            tstore(0x00, 0x00)
        }
    }
}
