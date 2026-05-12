// SPDX-License-Identifier: MIT
pragma solidity ^0.8.31;

// @author Modified from Solady by Vectorized and Akshay Tarpara https://github.com/Vectorized/solady/blob/ff6256a18851749e765355b3e21dc9bfa417255b/src/utils/clz/FixedPointMathLib.sol#L799-L822 under the MIT license.
library Cbrt {
    /// @dev Returns the cube root of `x`, rounded to within 1ulp.
    /// Credit to bout3fiddy and pcaversaccio under AGPLv3 license:
    /// https://github.com/pcaversaccio/snekmate/blob/main/src/snekmate/utils/math.vy
    function _cbrt(uint256 x) private pure returns (uint256 z) {
        assembly ("memory-safe") {
            // Initial guess z ≈ c · 2𐞥 where b = ⌊log₂(x)⌋, q = ⌊b / 3⌋. The 8-bit fixed-point
            // multipliers `c`: 144/128, 181/128, and 229/128 are selected by `b mod 3` to balance
            // each octave's worst-case final error. This gives >98 bits of precision after only 5
            // Newton-Raphson iterations. The `or(1, ...)` keeps z ≥ 1 when the shifted estimate is
            // 0.
            let b := sub(255, clz(x))
            z := or(1, shr(7, shl(div(b, 3), byte(add(29, mod(b, 3)), 0x90b5e5))))

            // 5 Newton-Raphson iterations
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
            // Round up. Let r_max = 0x285145f31ae515c447bb56. If x ≥ r_max³, then according to its
            // contract `_cbrt(x)` could return r_max + 1. This would cause `mul(z, mul(z, z))` to
            // overflow and `cbrtUp` to return r_max + 2. However, for these specific inputs in
            // practice, `_cbrt` returns r_max, defusing this scenario.
            z := add(z, lt(mul(z, mul(z, z)), x))
        }
    }
}
