// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

// Solidity `bool` may be any nonzero value for truthy. Bitwise `or` preserves truthiness so
// `or(a, b)` is safe. `and`/`andNot` are rewritten using `iszero` (always 0/1) to implement
// correct logical semantics. `toUint` normalizes with `lt(0x00, b)` (PUSH0 + LT = 5 gas).
library FastLogic {
    function or(bool a, bool b) internal pure returns (bool r) {
        assembly ("memory-safe") {
            r := or(a, b)
        }
    }

    function and(bool a, bool b) internal pure returns (bool r) {
        // De Morgan: a ∧ b ≡ ¬(¬a ∨ ¬b)
        assembly ("memory-safe") {
            r := iszero(or(iszero(a), iszero(b)))
        }
    }

    function andNot(bool a, bool b) internal pure returns (bool r) {
        // a ∧ ¬b: normalize via iszero then compare
        assembly ("memory-safe") {
            r := gt(iszero(b), iszero(a))
        }
    }

    function toUint(bool b) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := lt(0x00, b)
        }
    }
}
