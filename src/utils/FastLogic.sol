// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

// All functions accept dirty bools (any nonzero value is truthy) and return dirty bools (the
// result is truthy/falsy but not necessarily 0/1). `toUint` is the exception: it normalizes to
// exactly 0 or 1. `lt(0x00, x)` normalizes a dirty bool to 0/1 for 5 gas (PUSH0 + LT). On
// London (no PUSH0), it costs 6 gas and 1 extra byte; `iszero(iszero(x))` is equivalent there.
library FastLogic {
    // `or(nonzero, anything)` is nonzero; truthiness is preserved without normalization
    function or(bool a, bool b) internal pure returns (bool r) {
        assembly ("memory-safe") {
            r := or(a, b)
        }
    }

    // Normalize `b` to 0/1, multiply by `a`. No overflow since one factor is always 0 or 1.
    // Dirty `a` in the output is fine (truthy iff both inputs truthy).
    function and(bool a, bool b) internal pure returns (bool r) {
        assembly ("memory-safe") {
            r := mul(a, lt(0x00, b))
        }
    }

    // `iszero(b)` is 0/1; multiply by `a`. Result is truthy iff `a` truthy and `b` falsy.
    function andNot(bool a, bool b) internal pure returns (bool r) {
        assembly ("memory-safe") {
            r := mul(a, iszero(b))
        }
    }

    function toUint(bool b) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := lt(0x00, b)
        }
    }
}
