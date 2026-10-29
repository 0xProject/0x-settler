// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Clz} from "../vendor/Clz.sol";

library Cuid {
    using Clz for uint256;

    // CUIDv1: https://github.com/paralleldrive/cuid/blob/master/index.js
    // The integer encodes the base-36 text after `c`. The timestamp has no leading zeros;
    // the counter, fingerprint, and random suffix occupy exactly 16 characters.
    function decode(uint128 packed) internal pure returns (string memory result) {
        uint256 digits;
        // Assembly converts independent groups of base-36 digits in one word without temporary memory.
        // result = "c" + base36(packed, minDigits=17).
        assembly ("memory-safe") {
            packed := and(0xffffffffffffffffffffffffffffffff, packed)
            // 0x81bf1000 = 36**6 fits in 32 bits; 64-bit lanes also hold each reciprocal product below.
            // Four lanes take 24 digits. The remainder is at most floor(2**128 / 36**24) = 15: one digit.
            let sextets := mod(packed, 0x81bf1000)
            packed := div(packed, 0x81bf1000)
            sextets := or(shl(0x40, mod(packed, 0x81bf1000)), sextets)
            packed := div(packed, 0x81bf1000)
            sextets := or(shl(0x80, mod(packed, 0x81bf1000)), sextets)
            packed := div(packed, 0x81bf1000)
            sextets := or(shl(0xc0, mod(packed, 0x81bf1000)), sextets)
            packed := div(packed, 0x81bf1000)

            // floor(x / d) = (x * ceil(2**s / d)) >> s when (d * ceil(2**s / d) - 2**s) * x < 2**s.
            // For x < 36**6, d = 36**3, s = 46: 0x59e60383 = ceil(2**46 / 36**3) and the error factor is
            // 704. Products fit in 64 bits. Each quotient is below 36**3 < 2**16, so 0xffff separates it
            // from the next lane's product.
            let upperTriples :=
                and(mul(0xffff, div(not(0x00), 0xffffffffffffffff)), shr(0x2e, mul(0x59e60383, sextets)))
            // Adding (2**32 - 36**3) * quotient splits each 64-bit lane into two 32-bit lanes of three digits.
            let triples := add(mul(0xffff49c0, upperTriples), sextets)

            // For x < 36**3, d = 36, s = 21: 0xe38f = ceil(2**21 / 36) and the error factor is 28.
            // Products fit in 32 bits. Each quotient is below 36**2 < 2**11, so 0x7ff separates it from
            // the next lane's product.
            let mask := mul(0x7ff, div(not(0x00), 0xffffffff))
            let highPairs := and(mask, shr(0x15, mul(0xe38f, triples)))
            let highDigits := and(mask, shr(0x15, mul(0xe38f, highPairs)))
            // x + (256 - 36) * (x / 36 + 256 * (x / 36**2)) places each base-36 digit in one byte.
            digits := add(mul(0xdc, add(shl(0x08, highDigits), highPairs)), triples)

            // Each 32-bit lane holds three digit bytes under a zero byte. Three merges drop the zero
            // bytes: lanes of 3+1 bytes become 6+2, then 12+4, then 24+8.
            mask := mul(0xffffff, div(not(0x00), 0xffffffffffffffff))
            digits := or(and(mask, digits), shr(0x08, and(not(mask), digits)))
            mask := 0xffffffffffff00000000000000000000ffffffffffff
            digits := or(and(mask, digits), shr(0x10, and(not(mask), digits)))
            mask := 0xffffffffffffffffffffffff
            digits := or(and(mask, digits), shr(0x20, and(not(mask), digits)))
            digits := or(shl(0xc0, packed), digits)
        }

        uint256 length;
        unchecked {
            // 17 digits minimum, plus every byte up to the highest nonzero one above them.
            length = 17 + (((digits >> 136).bitLength() + 7) >> 3);
        }

        assembly ("memory-safe") {
            let ones := div(not(0x00), 0xff)
            // Digits are at most 35: adding 118 sets bit 7 exactly for letters, without byte carries.
            let letters := and(ones, shr(0x07, add(mul(0x76, ones), digits)))
            digits := add(mul(0x30, ones), add(mul(0x27, letters), digits))
            // The byte before the first digit is '0'; 0x30 ^ 0x53 = 'c'.
            digits := xor(shl(shl(0x03, length), 0x53), digits)
            length := add(0x01, length)
            result := mload(0x40)
            mstore(result, length)
            mstore(add(0x20, result), shl(sub(0x100, shl(0x03, length)), digits))
            mstore(0x40, add(0x40, result))
        }
    }
}
