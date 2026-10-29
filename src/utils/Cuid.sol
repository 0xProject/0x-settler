// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

library Cuid {
    // CUIDv1: https://github.com/paralleldrive/cuid/blob/master/index.js
    // The integer encodes the base-36 text after `c`. The timestamp has no leading zeros;
    // the counter, fingerprint, and random suffix occupy exactly 16 characters.
    function decode(uint128 packed) internal pure returns (string memory result) {
        // Assembly converts independent groups of base-36 digits in one word without temporary memory.
        // result = "c" + base36(packed, minDigits=17).
        assembly ("memory-safe") {
            packed := and(0xffffffffffffffffffffffffffffffff, packed)
            // 36**6 fits in 32 bits; 64-bit spacing also accommodates each reciprocal product.
            let groups := mod(packed, 0x81bf1000)
            packed := div(packed, 0x81bf1000)
            groups := or(shl(0x40, mod(packed, 0x81bf1000)), groups)
            packed := div(packed, 0x81bf1000)
            groups := or(shl(0x80, mod(packed, 0x81bf1000)), groups)
            packed := div(packed, 0x81bf1000)
            groups := or(shl(0xc0, mod(packed, 0x81bf1000)), groups)
            packed := div(packed, 0x81bf1000)

            // floor(x / d) = (x * ceil(2**s / d)) >> s when (d * ceil(2**s / d) - 2**s) * x < 2**s.
            // For x < 36**6, d = 36**3, s = 46, the error factor is 704. Products fit in 64 bits.
            let quotients :=
                and(0xffff000000000000ffff000000000000ffff000000000000ffff, shr(0x2e, mul(0x59e60383, groups)))
            // Adding (2**32 - 36**3) * quotient separates each pair of three-digit groups by 32 bits.
            groups := add(mul(0xffff49c0, quotients), groups)

            // For x < 36**3, d = 36, s = 21, the error factor is 28. Products fit in 32 bits.
            let mask := 0x7ff000007ff000007ff000007ff000007ff000007ff000007ff000007ff
            quotients := and(mask, shr(0x15, mul(0xe38f, groups)))
            let leading := and(mask, shr(0x15, mul(0xe38f, quotients)))
            // x + (256 - 36) * (x / 36 + 256 * (x / 36**2)) places each base-36 digit in one byte.
            let digits := add(mul(0xdc, add(shl(0x08, leading), quotients)), groups)

            mask := 0xffffff0000000000ffffff0000000000ffffff0000000000ffffff
            digits := or(and(mask, digits), shr(0x08, and(not(mask), digits)))
            mask := 0xffffffffffff00000000000000000000ffffffffffff
            digits := or(and(mask, digits), shr(0x10, and(not(mask), digits)))
            mask := 0xffffffffffffffffffffffff
            digits := or(and(mask, digits), shr(0x20, and(not(mask), digits)))
            digits := or(shl(0xc0, packed), digits)

            let length := shr(0x03, sub(0x107, clz(digits)))
            if lt(length, 0x11) { length := 0x11 }

            // Digits are at most 35: adding 118 sets bit 7 exactly for letters, without byte carries.
            let letters :=
                and(
                    0x0101010101010101010101010101010101010101010101010101010101010101,
                    shr(0x07, add(0x7676767676767676767676767676767676767676767676767676767676767676, digits))
                )
            digits := add(
                0x3030303030303030303030303030303030303030303030303030303030303030,
                add(mul(0x27, letters), digits)
            )
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
