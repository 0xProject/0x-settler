// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Panic} from "./Panic.sol";

library UnsafeMath {
    function unsafeInc(uint256 x) internal pure returns (uint256) {
        unchecked {
            return x + 1;
        }
    }

    function unsafeInc(uint256 x, bool b) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := add(x, b)
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

    function unsafeDec(uint256 x, bool b) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := sub(x, b)
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

    function unsafeAbs(int256 x) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := mul(or(0x01, sar(0xff, x)), x)
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

    /// rounds away from zero
    function unsafeDivUp(int256 n, int256 d) internal pure returns (int256 r) {
        assembly ("memory-safe") {
            r := add(mul(lt(0x00, smod(n, d)), or(0x01, sar(0xff, xor(n, d)))), sdiv(n, d))
        }
    }

    function unsafeAdd(uint256 a, uint256 b) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := add(a, b)
        }
    }
}

library Math {
    function inc(uint256 x, bool c) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := add(x, c)
        }
        if (r < x) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
    }

    function dec(uint256 x, bool c) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := sub(x, c)
        }
        if (r > x) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
    }

    function toInt(bool c) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := c
        }
    }

    function saturatingAdd(uint256 x, uint256 y) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := add(x, y)
            r := or(r, sub(0x00, lt(r, y)))
        }
    }

    function saturatingSub(uint256 x, uint256 y) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := mul(gt(x, y), sub(x, y))
        }
    }

    function absDiff(uint256 x, uint256 y) internal pure returns (uint256 r, bool sign) {
        assembly ("memory-safe") {
            sign := lt(x, y)
            let m := sub(0x00, sign)
            r := sub(xor(sub(x, y), m), m)
        }
    }
}
