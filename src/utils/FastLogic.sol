// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

library FastLogic {
    function or(bool a, bool b) internal pure returns (bool r) {
        assembly ("memory-safe") {
            r := or(a, b)
        }
    }

    function and(bool a, bool b) internal pure returns (bool r) {
        assembly ("memory-safe") {
            r := and(a, b)
        }
    }
}
