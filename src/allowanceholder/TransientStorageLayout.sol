// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {TransientStorageBase} from "./TransientStorageBase.sol";

abstract contract TransientStorageLayout is TransientStorageBase {
    /// @dev The key for this ephemeral allowance is keccak256(abi.encodePacked(operator, owner, token)).
    function _ephemeralAllowance(address operator, address owner, address token) internal pure returns (TSlot r) {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(0x00, shl(0x60, operator))
            mstore(0x14, shl(0x60, owner)) // store owner at 0x14
            mstore(0x28, shl(0x60, token)) // store token at 0x28
            // allowance slot is keccak256(abi.encodePacked(operator, owner, token))
            r := keccak256(0x00, 0x3c)
            // restore dirtied free pointer
            mstore(0x40, ptr)
        }
    }
}
