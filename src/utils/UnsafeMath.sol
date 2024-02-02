// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

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
}
