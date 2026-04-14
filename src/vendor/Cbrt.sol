// SPDX-License-Identifier: MIT
pragma solidity ^0.8.31;

// @author Modified from Solady by Vectorized and Akshay Tarpara https://github.com/Vectorized/solady/blob/ff6256a18851749e765355b3e21dc9bfa417255b/src/utils/clz/FixedPointMathLib.sol#L799-L822 under the MIT license.
library Cbrt {
    /// @dev Returns the cube root of `x`, rounded to within 1ulp.
    /// Credit to bout3fiddy and pcaversaccio under AGPLv3 license:
    /// https://github.com/pcaversaccio/snekmate/blob/main/src/snekmate/utils/math.vy
    function _cbrt(uint256 x) private pure returns (uint256 z) {
        assembly ("memory-safe") {
            // Initial guess z ≈ ∛(3/4) · 2𐞥 where q = ⌊(257 − clz(x)) / 3⌋. The multiplier 233/256
            // ≈ 0.909 ≈ ∛(3/4) balances the worst-case over/underestimate across each octave
            // triplet (ε_over ≈ 0.445, ε_under ≈ −0.278), giving >85 bits of precision after 6 N-R
            // iterations. The `add(1, ...)` term ensures z ≥ 1 when x > 0 (the `shr` can produce 0
            // for small `q`)
            z := add(1, shr(8, shl(div(sub(257, clz(x)), 3), 233)))

            // 6 Newton-Raphson iterations
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
            // Round up. Let r_max = 0x285145f31ae515c447bb56. If x ≥ r_max³, then according to its
            // contract `_cbrt(x)` could return r_max + 1. This would cause `mul(z, mul(z, z))` to
            // overflow and `cbrtUp` to return r_max + 2. However, for these specific inputs in
            // practice, `_cbrt` returns r_max, defusing this scenario.
            z := add(z, lt(mul(z, mul(z, z)), x))
        }
    }
}
