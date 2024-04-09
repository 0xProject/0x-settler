// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {AllowanceHolderBase} from "./AllowanceHolderBase.sol";
import {TransientStorage} from "./TransientStorage.sol";

/// @custom:security-contact security@0x.org
contract AllowanceHolder is TransientStorage, AllowanceHolderBase {
    /// @inheritdoc AllowanceHolderBase
    function exec(address operator, address token, uint256 amount, address payable target, bytes calldata data)
        internal
        override
        returns (bytes memory)
    {
        (bytes memory result, address sender, TSlot allowance) = _exec(operator, token, amount, target, data);
        // EIP-3074 seems unlikely; ERC-4337 unfriendly
        if (sender != tx.origin) {
            _set(allowance, 0);
        }
        return result;
    }
}
