// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

// @author Modified from Solady by Vectorized https://github.com/Vectorized/solady/blob/90db92ce173856605d24a554969f2c67cadbc7e9/src/utils/FixedPointMathLib.sol#L831-L857 under the MIT license.
library Cbrt {
    /// @dev Returns the cube root of `x`, rounded to within 1ulp.
    /// Credit to bout3fiddy and pcaversaccio under AGPLv3 license:
    /// https://github.com/pcaversaccio/snekmate/blob/main/src/snekmate/utils/math.vy
    /// Formally verified by xuwinnie:
    /// https://github.com/vectorized/solady/blob/main/audits/xuwinnie-solady-cbrt-proof.pdf
    function _cbrt(uint256 x) private pure returns (uint256 z) {
        assembly ("memory-safe") {
            let r := shl(7, lt(0xffffffffffffffffffffffffffffffff, x))
            r := or(r, shl(6, lt(0xffffffffffffffff, shr(r, x))))
            r := or(r, shl(5, lt(0xffffffff, shr(r, x))))
            r := or(r, shl(4, lt(0xffff, shr(r, x))))
            r := or(r, shl(3, lt(0xff, shr(r, x))))
            // Makeshift lookup table to nudge the approximate log2 result.
            z := div(shl(div(r, 3), shl(lt(0xf, shr(r, x)), 0xf)), xor(7, mod(r, 3)))
            // Newton-Raphson's.
            z := div(add(add(div(x, mul(z, z)), z), z), 3)
            z := div(add(add(div(x, mul(z, z)), z), z), 3)
            z := div(add(add(div(x, mul(z, z)), z), z), 3)
            z := div(add(add(div(x, mul(z, z)), z), z), 3)
            z := div(add(add(div(x, mul(z, z)), z), z), 3)
            z := div(add(add(div(x, mul(z, z)), z), z), 3)
            z := div(add(add(div(x, mul(z, z)), z), z), 3)
        }
    }

    /// @dev Returns the cube root of `x`, rounded down.
    function cbrt(uint256 x) internal pure returns (uint256 z) {
        z = _cbrt(x);
        assembly ("memory-safe") {
            // Round down.
            z := sub(z, lt(div(x, mul(z, z)), z))
        }
    }

    /// @dev Returns the cube root of `x`, rounded up.
    function cbrtUp(uint256 x) internal pure returns (uint256 z) {
        z = _cbrt(x);
        assembly ("memory-safe") {
            // Round up.
            z := add(z, lt(mul(z, mul(z, z)), x))
        }
    }
}
