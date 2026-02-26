// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

// @author Modified from Solady by Vectorized and Akshay Tarpara https://github.com/Vectorized/solady/blob/1198c9f70b30d472a7d0ec021bec080622191b03/src/utils/clz/FixedPointMathLib.sol#L769-L797 under the MIT license.
library Sqrt {
    /// @dev Returns the square root of `x`, rounded down.
    function _sqrt(uint256 x) private pure returns (uint256 z) {
        assembly ("memory-safe") {
            // Initial guess z = 2^⌊(n+1)/2⌋ where n = ⌊log₂(x)⌋.
            // The alternating-endpoint seed gives ε₁ = 0.0607 after one Babylonian
            // step for all inputs. With ε_{n+1} ≈ ε²/2, six steps yield 2⁻¹⁶¹
            // relative error (>128 bits), so the 7th step is unnecessary.
            z := shl(shr(1, sub(256, clz(x))), 1)

            // Six Babylonian steps.
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))

            // The Babylonian method oscillates between ⌊√x⌋ and ⌈√x⌉. Floor it.
            // This also guarantees z ≤ 2¹²⁸ − 1, preventing mul(z,z) overflow in
            // sqrtUp.
            z := sub(z, lt(div(x, z), z))
        }
    }

    /// @dev Returns the square root of `x`, rounded down.
    function sqrt(uint256 x) internal pure returns (uint256 z) {
        z = _sqrt(x);
    }

    /// @dev Returns the square root of `x`, rounded up.
    function sqrtUp(uint256 x) internal pure returns (uint256 z) {
        z = _sqrt(x);
        assembly ("memory-safe") {
            z := add(lt(mul(z, z), x), z)
        }
    }
}
