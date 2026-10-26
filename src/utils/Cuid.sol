// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

library Cuid {
    // CUIDv1: https://github.com/paralleldrive/cuid/blob/master/index.js
    // The integer encodes the base-36 text after `c`. The timestamp has no leading zeros;
    // the counter, fingerprint, and random suffix occupy exactly 16 characters.
    function decode(uint128 packed) internal pure returns (string memory result) {
        // Assembly avoids allocating a buffer for reversed digits: result = "c" + base36(packed, minDigits=17).
        assembly ("memory-safe") {
            packed := and(0xffffffffffffffffffffffffffffffff, packed)
            let digits := 0x00
            let length := 0x00
            for {} or(packed, lt(length, 0x11)) {} {
                let digit := mod(packed, 0x24)
                let character := add(0x30, add(digit, mul(0x27, gt(digit, 0x09))))
                digits := or(shl(shl(0x03, length), character), digits)
                length := add(0x01, length)
                packed := div(packed, 0x24)
            }
            digits := or(shl(shl(0x03, length), 0x63), digits)
            length := add(0x01, length)
            result := mload(0x40)
            mstore(result, length)
            mstore(add(0x20, result), shl(sub(0x100, shl(0x03, length)), digits))
            mstore(0x40, add(0x40, result))
        }
    }
}
