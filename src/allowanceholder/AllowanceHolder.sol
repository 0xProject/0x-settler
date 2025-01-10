// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

import {AllowanceHolderBase} from "./AllowanceHolderBase.sol";
import {TransientStorage} from "./TransientStorage.sol";

/// @custom:security-contact security@0x.org
contract AllowanceHolder is TransientStorage, AllowanceHolderBase {
    constructor() {
        require(address(this) == 0x0000000000001fF3684f28c67538d4D072C22734 || block.chainid == 31337);
    }
}
