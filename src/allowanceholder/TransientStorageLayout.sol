// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {TransientStorageBase} from "./TransientStorageBase.sol";

abstract contract TransientStorageLayout is TransientStorageBase {
    /// @dev The key for this ephemeral allowance is keccak256(abi.encodePacked(operator, owner, token)).
    function _ephemeralAllowance(address operator, address owner, address token) internal pure returns (TSlot r) {
        assembly ("memory-safe") {
            // This dirties the upper 8 bytes of the free memory pointer. These bytes must always be
            // zero, otherwise we would OOM.
            mstore(0x28, token)
            mstore(0x14, owner)
            mstore(0x00, operator)
            // allowance slot is keccak256(abi.encodePacked(operator, owner, token))
            r := keccak256(0x0c, 0x3c)
            // restore dirtied free pointer
            mstore(0x28, 0x00)
        }
    }
}
