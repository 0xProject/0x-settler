// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

library FastLogic {
    function or(bool a, bool b) internal pure returns (bool r) {
        assembly ("memory-safe") {
            r := iszero(iszero(or(a, b)))
        }
    }

    function and(bool a, bool b) internal pure returns (bool r) {
        assembly ("memory-safe") {
            r := iszero(or(iszero(a), iszero(b)))
        }
    }

    function andNot(bool a, bool b) internal pure returns (bool r) {
        assembly ("memory-safe") {
            r := iszero(or(iszero(a), b))
        }
    }

    function toUint(bool b) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := iszero(iszero(b))
        }
    }
}
