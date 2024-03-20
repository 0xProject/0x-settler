// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

abstract contract FreeMemory {
    modifier DANGEROUS_freeMemory() {
        uint256 freeMemPtr;
        assembly ("memory-safe") {
            freeMemPtr := mload(0x40)
        }
        _;
        assembly ("memory-safe") {
            mstore(0x40, freeMemPtr)
        }
    }
}
