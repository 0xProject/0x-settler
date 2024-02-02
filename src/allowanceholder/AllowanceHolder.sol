// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {AllowanceHolderBase} from "./AllowanceHolderBase.sol";

// EVM version is set to shanghai which does not support TLOAD/TSTORE
/*
import {TransientStorage} from "./TransientStorage.sol";

contract AllowanceHolder is TransientStorage, AllowanceHolderBase {
    function exec(address operator, address token, uint256 amount, address payable target, bytes calldata data)
        internal
        override
        returns (bytes memory result)
    {
        address sender;
        (result, sender) = _exec(operator, token, amount, target, data);
        // EIP-3074 seems unlikely
        if (sender != tx.origin) {
            _setAllowed(operator, sender, token, 0);
        }
    }
}
*/
