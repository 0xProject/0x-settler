// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

library UnsafeMath {
    function unsafeInc(uint256 x) internal pure returns (uint256) {
        unchecked {
            return x + 1;
        }
    }

    function unsafeInc(int256 x) internal pure returns (int256) {
        unchecked {
            return x + 1;
        }
    }

    function unsafeDec(uint256 x) internal pure returns (uint256) {
        unchecked {
            return x - 1;
        }
    }

    function unsafeDec(int256 x) internal pure returns (int256) {
        unchecked {
            return x - 1;
        }
    }

    function unsafeNeg(int256 x) internal pure returns (int256) {
        unchecked {
            return -x;
        }
    }

    function unsafeDiv(uint256 numerator, uint256 denominator) internal pure returns (uint256 quotient) {
        assembly ("memory-safe") {
            quotient := div(numerator, denominator)
        }
    }

    function unsafeDiv(int256 numerator, int256 denominator) internal pure returns (int256 quotient) {
        assembly ("memory-safe") {
            quotient := sdiv(numerator, denominator)
        }
    }

    function unsafeMod(uint256 numerator, uint256 denominator) internal pure returns (uint256 remainder) {
        assembly ("memory-safe") {
            remainder := mod(numerator, denominator)
        }
    }

    function unsafeMod(int256 numerator, int256 denominator) internal pure returns (int256 remainder) {
        assembly ("memory-safe") {
            remainder := smod(numerator, denominator)
        }
    }

    function unsafeMulMod(uint256 a, uint256 b, uint256 m) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := mulmod(a, b, m)
        }
    }

    function unsafeAddMod(uint256 a, uint256 b, uint256 m) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := addmod(a, b, m)
        }
    }

    function unsafeDivUp(uint256 n, uint256 d) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := add(gt(mod(n, d), 0x00), div(n, d))
        }
    }
}
