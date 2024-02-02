// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {AllowanceHolderBase} from "./AllowanceHolderBase.sol";
import {TransientStorageMock} from "./TransientStorageMock.sol";

contract AllowanceHolder is TransientStorageMock, AllowanceHolderBase {
    function exec(address operator, address token, uint256 amount, address payable target, bytes calldata data)
        internal
        override
        returns (bytes memory)
    {
        (bytes memory result, address sender) = _exec(operator, token, amount, target, data);
        _setAllowed(operator, sender, token, 0);
        return result;
    }

    // This is here as a deploy-time check that AllowanceHolder doesn't have any
    // state. If it did, it would interfere with TransientStorageMock.
    bytes32 private _sentinel;

    constructor() {
        uint256 _sentinelSlot;
        assembly ("memory-safe") {
            _sentinelSlot := _sentinel.slot
        }
        assert(_sentinelSlot == 1);
    }
}
