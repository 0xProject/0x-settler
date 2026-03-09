// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

// @author Modified from Solady by Vectorized and Akshay Tarpara https://github.com/Vectorized/solady/blob/1198c9f70b30d472a7d0ec021bec080622191b03/src/utils/clz/FixedPointMathLib.sol#L769-L797 under the MIT license.
library Sqrt {
    /// @dev Returns the square root of `x`, rounded maybe-up maybe-down. For expert use only.
    function _sqrt(uint256 x) private pure returns (uint256 z) {
        assembly ("memory-safe") {
            // Step 1: Get the bit position of the most significant bit
            // n = floor(log2(x))
            // For x ≈ 2^n, we know sqrt(x) ≈ 2^(n/2)
            // We use (n+1)/2 instead of n/2 to round up slightly
            // This gives a better initial approximation
            //
            // Formula: z = 2^((n+1)/2) = 2^(floor((n+1)/2))
            // Implemented as: z = 1 << ((n+1) >> 1)
            z := shl(shr(1, sub(256, clz(x))), 1)

            /// (x/z + z) / 2
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))
        }
    }

    /// @dev Returns the square root of `x`, rounded down.
    function sqrt(uint256 x) internal pure returns (uint256 z) {
        z = _sqrt(x);
        assembly ("memory-safe") {
            // If `x+1` is a perfect square, the Babylonian method cycles between
            // `floor(sqrt(x))` and `ceil(sqrt(x))`. This statement ensures we return floor.
            // See: https://en.wikipedia.org/wiki/Integer_square_root#Using_only_integer_division
            z := sub(z, lt(div(x, z), z))
        }
    }

    /// @dev Returns the square root of `x`, rounded up.
    function sqrtUp(uint256 x) internal pure returns (uint256 z) {
        z = _sqrt(x);
        assembly ("memory-safe") {
            // If `x == type(uint256).max`, then according to its contract `_sqrt(x)` could return
            // `2**128`. This would cause `mul(z, z)` to overflow and `sqrtUp` to return `2**128 +
            // 1`. However, for this specific input in practice, `_sqrt` returns `2**128 - 1`,
            // defusing this scenario.
            z := add(lt(mul(z, z), x), z)
        }
    }
}
