// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

// A target whose fallback returns a single KNOWN 32-byte word (0xbeef)
contract MockConstReturnTarget {
    fallback() external payable {
        assembly ("memory-safe") {
            mstore(0x00, 0xbeef)
            return(0x00, 0x20)
        }
    }

}
