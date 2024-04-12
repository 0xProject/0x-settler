// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

library AtoI {
    function atoi(string memory x) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            for {
                let i := add(x, 0x01)
                let end := add(i, mload(x))
            } lt(i, end) { i := add(0x01, i) } {
                let c := sub(and(0xff, mload(i)), 0x30)
                if gt(c, 0x09) {
                    mstore(0x00, 0x4e487b71) // selector for `Panic(uint256)`
                    mstore(0x20, 0x21) // out of range enum
                    revert(0x1c, 0x24)
                }
                let r_new := add(c, mul(0x0a, r))
                if lt(r_new, r) {
                    mstore(0x00, 0x4e487b71) // selector for `Panic(uint256)`
                    mstore(0x20, 0x11) // arithmetic overflow
                    revert(0x1c, 0x24)
                }
                r := r_new
            }
        }
    }
}
