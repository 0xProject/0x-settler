// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

// @author Modified from Solady by Vectorized https://github.com/Vectorized/solady/blob/701406e8126cfed931645727b274df303fbcd94d/src/utils/LibBit.sol#L30-L45 under the MIT license
library Clz {
    /// @dev Count leading zeros.
    /// Returns the number of zeros preceding the most significant one bit.
    /// If `x` is zero, returns 256.
    function clz(uint256 x) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := shl(7, lt(0xffffffffffffffffffffffffffffffff, x))
            r := or(r, shl(6, lt(0xffffffffffffffff, shr(r, x))))
            r := or(r, shl(5, lt(0xffffffff, shr(r, x))))
            r := or(r, shl(4, lt(0xffff, shr(r, x))))
            r := or(r, shl(3, lt(0xff, shr(r, x))))
            // We use a 5-bit deBruijn Sequence to convert `x`'s 8
            // most-significant bits into an index. We then index the lookup
            // table (bytewise) by the deBruijn symbol to obtain the bitwise
            // inverse of its logarithm.
            r :=
                add(
                    xor(
                        r,
                        byte(
                            and(0x1f, shr(shr(r, x), 0x8421084210842108cc6318c6db6d54be)),
                            0xf8f9f9faf9fdfafbf9fdfcfdfafbfcfef9fafdfafcfcfbfefafafcfbffffffff
                        )
                    ),
                    iszero(x)
                )
        }
    }

    function bitLength(uint256 x) internal pure returns (uint256) {
        unchecked {
            return 256 - clz(x);
        }
    }
}
