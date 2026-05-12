// SPDX-License-Identifier: MIT
pragma solidity ^0.8.31;

// @author Modified from Solady by Vectorized and Akshay Tarpara https://github.com/Vectorized/solady/blob/ff6256a18851749e765355b3e21dc9bfa417255b/src/utils/clz/FixedPointMathLib.sol#L799-L822 under the MIT license.
library Cbrt {
    /// @dev Returns the cube root of `x`, rounded to within 1ulp.
    /// Credit to bout3fiddy and pcaversaccio under AGPLv3 license:
    /// https://github.com/pcaversaccio/snekmate/blob/main/src/snekmate/utils/math.vy
    function _cbrt(uint256 x) private pure returns (uint256 z) {
        assembly ("memory-safe") {
            // Initial guess z ≈ c · 2𐞥 where y = ⌊log₂(x)⌋ + 3, q = ⌊y / 3⌋. The 8-bit
            // fixed-point multipliers `c`: 144/256, 181/256, and 229/256 are selected by
            // `y mod 3` to balance each octave's endpoint error. This gives >85 bits of precision
            // after only 5 Newton-Raphson iterations. The `or(1, ...)` keeps z ≥ 1 when the
            // shifted estimate is 0.
            let y := sub(0x0102, clz(x))
            z := or(0x01, shr(0x08, shl(div(y, 0x03), byte(add(0x1d, mod(y, 0x03)), 0x90b5e5))))

            // 5 Newton-Raphson iterations
            z := div(add(add(div(x, mul(z, z)), z), z), 0x03)
            z := div(add(add(div(x, mul(z, z)), z), z), 0x03)
            z := div(add(add(div(x, mul(z, z)), z), z), 0x03)
            z := div(add(add(div(x, mul(z, z)), z), z), 0x03)
            z := div(add(add(div(x, mul(z, z)), z), z), 0x03)
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
            // Round up. Let r_max = 0x285145f31ae515c447bb56. If x ≥ r_max³, then according to its
            // contract `_cbrt(x)` could return r_max + 1. This would cause `mul(z, mul(z, z))` to
            // overflow and `cbrtUp` to return r_max + 2. However, for these specific inputs in
            // practice, `_cbrt` returns r_max, defusing this scenario.
            z := add(z, lt(mul(z, mul(z, z)), x))
        }
    }
}
