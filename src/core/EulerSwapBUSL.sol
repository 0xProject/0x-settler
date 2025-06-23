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
            return y0 + (v + (py - 1)).unsafeDivUp(py);
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
        // The value `B` is implicitly computed as:
        //     [(y - y0) * py * 1e18 - (c * 2 - 1e18) * x0 * px] / px
        // But the intermediate products can overflow 256 bits. Therefore, we have to perform
        // 512-bit multiplications and a subtraction to get the correct value.
        // Additionally, we only care about the absolute value of `B` for use later, so we
        // separately extract the sign of `B` and its absolute value.

        unchecked {
            bool sign; // true when `B` is negative
            uint256 absB; // scale: 1e18

            {
                uint256 denom = px * 1e18; // scale: 1e36

                // perform the two 256-by-256 into 512 multiplications
                (uint256 term1_lo, uint256 term1_hi, uint256 term1_rem) = FullMath._mulDivSetup(y - y0, py * 1e18, denom); // scale: 1e54
                (uint256 term2_lo, uint256 term2_hi, uint256 term2_rem) = FullMath._mulDivSetup(((c << 1) - 1e18) * x0, px, denom); // scale: 1e54

                // compare the resulting 512-bit integers to determine which branch below we need to take
                assembly ("memory-safe") {
                    sign := or(gt(term2_hi, term1_hi), and(eq(term2_hi, term1_hi), gt(term2_lo, term1_lo)))
                }

                // ensure that the result will be positive
                (uint256 a_lo, uint256 b_lo) = sign.maybeSwap(term1_lo, term2_lo);
                (uint256 a_hi, uint256 b_hi) = sign.maybeSwap(term1_hi, term2_hi);
                (uint256 a_rem, uint256 b_rem) = sign.maybeSwap(term1_rem, term2_rem);

                // perform the 512-bit subtraction
                uint256 lo = a_lo - b_lo;
                uint256 hi = (a_hi - b_hi).unsafeDec(lo > a_lo);
                uint256 rem = a_rem.unsafeAddMod(denom - b_rem, denom);

                // if `sign` is true, then we want to round up. compute the carry bit
                bool carry;
                assembly ("memory-safe") {
                    carry := and(lt(0x00, rem), sign)
                }

                // 512-bit by 256-bit division
                absB = FullMath._mulDivInvert(lo, hi, denom, rem).unsafeInc(carry);
            }

            // `shift` is how much we need to shift right (the log of the scaling factor) to prevent overflow when computing B^2
            uint256 shift = absB.bitLength().saturatingSub(128);
            uint256 twoShift = shift << 1;

            uint256 x;
            if (sign) {
                // B is negative; use regular quadratic formula

                // absB and sqrt round up
                // squaredB and fourAC round up
                // C rounds down

                uint256 C = (1e18 - c).unsafeMulDivAlt(x0 * x0, 1e18); // scale: 1e36
                uint256 fourAC = (c << 2).unsafeMulDivUpAlt(C, 1e18); // scale: 1e36

                uint256 squaredB = absB.unsafeMulShiftUp(absB, twoShift);
                uint256 discriminant = squaredB + (fourAC >> twoShift).unsafeInc(0 < fourAC << (256 - twoShift));
                uint256 sqrt = discriminant.sqrtUp() << shift;

                // use the regular quadratic formula solution (-b + sqrt(b^2 - 4ac)) / 2a
                x = (absB + sqrt).unsafeMulDivUp(1e18, c << 1);
            } else {
                // B is nonnegative; use "citardauq" quadratic formula

                // absB and sqrt round down
                // C rounds up
                // squaredB and fourAC round down

                uint256 C = (1e18 - c).unsafeMulDivUpAlt(x0 * x0, 1e18); // scale: 1e36
                uint256 fourAC = (c << 2).unsafeMulDivAlt(C, 1e18); // scale: 1e36

                uint256 squaredB = absB.unsafeMulShift(absB, twoShift);
                uint256 discriminant = squaredB + (fourAC >> twoShift); // TODO: can this addition overflow?
                uint256 sqrt = discriminant.sqrt() << shift;

                // use the "citardauq" quadratic formula solution 2c / (-b - sqrt(b^2 - 4ac))
                x = (C << 1).unsafeDivUp(absB + sqrt);
            }
            return (x < x0).ternary(x, x0);
        }
    }
}
