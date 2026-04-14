// SPDX-License-Identifier: MIT
pragma solidity ^0.8.31;

// @author Modified from Solady by Vectorized and Akshay Tarpara https://github.com/Vectorized/solady/blob/1198c9f70b30d472a7d0ec021bec080622191b03/src/utils/clz/FixedPointMathLib.sol#L769-L797 under the MIT license.
library Sqrt {
    /// @dev Returns the square root of `x`, rounded maybe-up maybe-down. For expert use only.
    function _sqrt(uint256 x) private pure returns (uint256 z) {
        assembly ("memory-safe") {
            // Initial guess z = 2^⌊(n+1)/2⌋ where n = ⌊log₂(x)⌋. This seed gives ε₁ = 0.0607 after
            // one Babylonian step for all inputs. With ε_{n+1} ≈ ε²/2, 6 steps yield 2⁻¹⁶⁰ relative
            // error (>128 correct bits).
            z := shl(shr(1, sub(256, clz(x))), 1)

            // 6 Babylonian steps
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
            // If `x+1` is a perfect square, the Babylonian method oscillates between ⌊√x⌋ and
            // ⌈√x⌉. Floor it. See:
            // https://en.wikipedia.org/wiki/Integer_square_root#Using_only_integer_division
            z := sub(z, lt(div(x, z), z))
        }
    }

    /// @dev Returns the square root of `x`, rounded up.
    function sqrtUp(uint256 x) internal pure returns (uint256 z) {
        z = _sqrt(x);
        assembly ("memory-safe") {
            // `mul(z, z)` can overflow when `x == type(uint256).max`. This is because `_sqrt(x)`
            // can return ⌈√x⌉ when `x + 1` is square. An overflow in `zz` causes a spurious
            // round-up (`z` is already rounded up) and causes the result to be `2**128 + 1`, an
            // off-by-one. To compensate, we detect this overflow and avoid rounding.
            let zz := mul(z, z)
            z := add(gt(lt(zz, x), lt(zz, z)), z)
        }
    }
}
