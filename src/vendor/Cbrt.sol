// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

// @author Modified from Solady by Vectorized and Akshay Tarpara https://github.com/Vectorized/solady/blob/ff6256a18851749e765355b3e21dc9bfa417255b/src/utils/clz/FixedPointMathLib.sol#L799-L822 under the MIT license.
library Cbrt {
    /// @dev Returns the cube root of `x`, rounded to within 1ulp.
    /// Credit to bout3fiddy and pcaversaccio under AGPLv3 license:
    /// https://github.com/pcaversaccio/snekmate/blob/main/src/snekmate/utils/math.vy
    /// Formally verified by xuwinnie:
    /// https://github.com/vectorized/solady/blob/main/audits/xuwinnie-solady-cbrt-proof.pdf
    function _cbrt(uint256 x) private pure returns (uint256 z) {
        assembly ("memory-safe") {
            // Initial guess z = 2^ceil((log2(x) + 2) / 3).
            // Since log2(x) = 255 - clz(x), the expression shl((257 - clz(x)) / 3, 1)
            // computes this over-estimate. Guaranteed ≥ cbrt(x) and safe for Newton-Raphson's.
            z := shl(div(sub(257, clz(x)), 3), 1)
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
            // Round up. Avoid cubing `z` to avoid overflow
            let z2 := mul(z, z)
            let d := div(x, z2)
            z := add(z, gt(add(d, lt(mul(d, z2), x)), z))
        }
    }
}
