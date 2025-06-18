// SPDX-License-Identifier: BUSL-1.1
pragma solidity ^0.8.25;

// The contents of this file were provided to ZeroEx Inc. by Euler Labs Ltd. on
// 12 June 2025 under an exception to the original license terms (BUSL with no
// additional use grant, change date 2030-05-14, change license GPLv2) for the
// specific purpose of integration into 0x Settler smart contracts for
// deployment to Ethereum mainnet to implement gas-optimized settlement against
// EulerSwap pools.
//
// NO OTHER USE, BEYOND THOSE IN THE ORIGINAL BUSL LICENSE, IS AUTHORIZED.
//
// (That means don't fork this without explicit permission from Euler Labs.)

import {Ternary} from "../utils/Ternary.sol";
import {UnsafeMath, Math} from "../utils/UnsafeMath.sol";
import {Sqrt} from "../vendor/Sqrt.sol";
import {Clz} from "../vendor/Clz.sol";
import {FullMath} from "../vendor/FullMath.sol";
import {Panic} from "../utils/Panic.sol";

/// @author Modified from EulerSwap by Euler Labs Ltd. https://github.com/euler-xyz/euler-swap/blob/aa87a6bc1ca01bf6e5a8e14c030bbe0d008cf8bf/src/libraries/CurveLib.sol . See above for copyright and usage terms.
library CurveLib {
    using Ternary for bool;
    using UnsafeMath for uint256;
    using UnsafeMath for int256;
    using Math for uint256;
    using Sqrt for uint256;
    using Clz for uint256;
    using FullMath for uint256;

    /// @dev EulerSwap curve
    /// @notice Computes the output `y` for a given input `x`.
    /// @param x The input reserve value, constrained to 1 <= x <= x0.
    /// @param px (1 <= px <= 1e25).
    /// @param py (1 <= py <= 1e25).
    /// @param x0 (1 <= x0 <= 2^112 - 1).
    /// @param y0 (0 <= y0 <= 2^112 - 1).
    /// @param c (0 <= c <= 1e18).
    /// @return y The output reserve value corresponding to input `x`, guaranteed to satisfy `y0 <= y <= 2^112 - 1`.
    function f(uint256 x, uint256 px, uint256 py, uint256 x0, uint256 y0, uint256 c) internal pure returns (uint256) {
        unchecked {
            uint256 v = (px * (x0 - x)).unsafeMulDivUp(c * x + (1e18 - c) * x0, x * 1e18);
            if (v > type(uint248).max) {
                Panic.panic(Panic.ARITHMETIC_OVERFLOW);
            }
            return y0 + (v + (py - 1)).unsafeDiv(py);
        }
    }

    /// @dev EulerSwap inverse curve
    /// @notice Computes the output `x` for a given input `y`.
    /// @param y The input reserve value, constrained to y0 <= y <= 2^112 - 1.
    /// @param px (1 <= px <= 1e25).
    /// @param py (1 <= py <= 1e25).
    /// @param x0 (1 <= x0 <= 2^112 - 1).
    /// @param y0 (0 <= y0 <= 2^112 - 1).
    /// @param c (0 <= c <= 1e18).
    /// @return x The output reserve value corresponding to input `y`, guaranteed to satisfy `1 <= x <= x0`.
    function fInverse(uint256 y, uint256 px, uint256 py, uint256 x0, uint256 y0, uint256 c)
        internal
        pure
        returns (uint256)
    {
        // components of quadratic equation
        int256 B;
        uint256 C;
        uint256 fourAC;

        unchecked {
            int256 term1 = int256((py * 1e18).unsafeMulDivUp(y - y0, px)); // scale: 1e36
            int256 term2 = int256(((c << 1) - 1e18) * x0); // scale: 1e36
            B = (term1 - term2).unsafeDiv(1e18); // scale: 1e18
            C = (1e18 - c).unsafeMulDivUpAlt(x0 * x0, 1e18); // scale: 1e36
            fourAC = (c << 2).unsafeMulDivUpAlt(C, 1e18); // scale: 1e36
        }

        uint256 absB = uint256(B.unsafeAbs());
        uint256 sqrt;
        if (1e36 > absB) {
            // B^2 can be calculated directly at 1e18 scale without overflowing
            unchecked {
                uint256 squaredB = absB * absB; // scale: 1e36
                uint256 discriminant = squaredB + fourAC; // scale: 1e36
                sqrt = discriminant.sqrtUp(); // scale: 1e18
            }
        } else {
            // B^2 cannot be calculated directly at 1e18 scale without overflowing
            uint256 scale = computeScale(absB); // calculate the scaling factor such that B^2 can be calculated without overflowing
            uint256 twoScale = scale << 1;
            uint256 squaredB = absB.unsafeMulShift(absB, twoScale);
            uint256 discriminant = squaredB + (fourAC >> twoScale);
            sqrt = discriminant.sqrtUp() << scale; // TODO: there's probably a way to avoid this by keeping everything as a uint512 until we have to sqrt
        }

        uint256 x;
        unchecked {
            x = (
                0 < B
                    // use the "citardauq" quadratic formula solution 2c / (-b - sqrt(b^2 - 4ac))
                    ? (C << 1).unsafeDivUp(absB + sqrt)
                    // use the regular quadratic formula solution (-b + sqrt(b^2 - 4ac)) / 2a
                    : (absB + sqrt).unsafeMulDivUp(1e18, c << 1)
            ) + 1;
        }
        return (x < x0).ternary(x, x0);
    }

    /// @dev Utility to derive optimal scale for computations in fInverse
    function computeScale(uint256 x) private pure returns (uint256) {
        uint256 bits = x.bitLength();
        // 2^(bits - 128) is how much we need to scale down to prevent overflow when squaring x
        unchecked {
            return bits.saturatingSub(128);
        }
    }
}
