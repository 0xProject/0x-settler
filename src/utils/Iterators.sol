// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

type CalldataBytesIterator is uint256;

library LibCalldataBytesIterator {
    function iter(bytes[] calldata data) internal pure returns (CalldataBytesIterator i) {
        assembly ("memory-safe") {
            i := data.offset
        }
    }

    function next(CalldataBytesIterator i) internal pure returns (CalldataBytesIterator j) {
        assembly ("memory-safe") {
            j := add(0x20, i)
        }
    }

    function get(bytes[] calldata data, CalldataBytesIterator i) internal pure returns (bytes calldata r) {
        assembly ("memory-safe") {
            // initially, we set `r.offset` to the pointer to the length. this is 32 bytes before the actual start of data
            r.offset := 
                add(
                    data.offset,
                    // We allow the indirection/offset to `data[i]` to be negative
                    calldataload(i)
                )
            // now we load `r.length` and set `r.offset` to the start of data
            r.length := calldataload(r.offset)
            r.offset := add(0x20, r.offset)
        }
    }
}
