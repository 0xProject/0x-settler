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

import {Panic} from "../utils/Panic.sol";
import {FastLogic} from "../utils/FastLogic.sol";
import {Ternary} from "../utils/Ternary.sol";
import {UnsafeMath, Math} from "../utils/UnsafeMath.sol";
import {Sqrt} from "../vendor/Sqrt.sol";
import {Clz} from "../vendor/Clz.sol";
import {FullMath} from "../vendor/FullMath.sol";

/// @author Modified from EulerSwap by Euler Labs Ltd. https://github.com/euler-xyz/euler-swap/blob/aa87a6bc1ca01bf6e5a8e14c030bbe0d008cf8bf/src/libraries/CurveLib.sol . See above for copyright and usage terms.
/// @author Extensively modified by Duncan Townsend for Zero Ex Inc. (modifications released under MIT license)
/// @dev Refer to https://raw.githubusercontent.com/euler-xyz/euler-swap/7080c3fe0c9f935c05849a0756ed43d959130afd/docs/whitepaper/EulerSwap_White_Paper.pdf for the underlying equations and their derivation.
library CurveLib {
    using FastLogic for bool;
    using Ternary for bool;
    using UnsafeMath for uint256;
    using UnsafeMath for int256;
    using Math for uint256;
    using Sqrt for uint256;
    using Clz for uint256;
    using FullMath for uint256;

    /// @notice Returns true if the specified reserve amounts would be acceptable, false otherwise.
    /// Acceptable points are on, or above and to-the-right of the swapping curve.
    /// @param newReserve0 An amount of `vault0.asset()` tokens in that token's base unit. No constraint on range.
    /// @param newReserve1 An amount of `vault1.asset()` tokens in that token's base unit. No constraint on range.
    /// @param equilibriumReserve0 (0 <= equilibriumReserve0 <= 2^112 - 1). An amount of `vault0.asset()` tokens in that token's base unit.
    /// @param equilibriumReserve1 (0 <= equilibriumReserve1 <= 2^112 - 1). An amount of `vault1.asset()` tokens in that token's base unit.
    /// @param priceX (1 <= priceX <= 1e25). The equilibrium price of `vault0.asset()`. A fixnum with a basis of 1e18.
    /// @param priceY (1 <= priceY <= 1e25). The equilibrium price of `vault1.asset()`. A fixnum with a basis of 1e18.
    /// @param concentrationX (0 <= concentrationX <= 1e18). The liquidity concentration of `vault0.asset()` on the side of the curve where it is in deficit. A fixnum with a basis of 1e18.
    /// @param concentrationY (0 <= concentrationY <= 1e18). The liquidity concentration of `vault1.asset()` on the side of the curve where it is in deficit. A fixnum with a basis of 1e18.
    function verify(
        uint256 newReserve0,
        uint256 newReserve1,
        uint256 equilibriumReserve0,
        uint256 equilibriumReserve1,
        uint256 priceX,
        uint256 priceY,
        uint256 concentrationX,
        uint256 concentrationY
    ) internal pure returns (bool) {
        bool overflow = (newReserve0 | newReserve1) >> 112 > 0;
        bool yes = !(newReserve0 < equilibriumReserve0).or(newReserve1 < equilibriumReserve1);
        bool no = !(newReserve0 > equilibriumReserve0).or(newReserve1 > equilibriumReserve1);

        (uint256 x, uint256 y, uint256 px, uint256 py, uint256 x0, uint256 y0, uint256 cx) = (
            newReserve0 < equilibriumReserve0
        )
            ? (newReserve0, newReserve1, priceX, priceY, equilibriumReserve0, equilibriumReserve1, concentrationX)
            : (newReserve1, newReserve0, priceY, priceX, equilibriumReserve1, equilibriumReserve0, concentrationY);

        bool maybe;
        unchecked {
            if (cx == 1e18) {
                maybe = y - y0 >= ((x0 - x) * px).unsafeDivUp(py);
            } else {
                (uint256 a_lo, uint256 a_hi) = (y - y0).fullMul(1e18 * x * py);
                (uint256 b_lo, uint256 b_hi) = (px * (x0 - x)).fullMul(cx * x + (1e18 - cx) * x0);
                maybe = !FullMath.fullLt(a_lo, a_hi, b_lo, b_hi);
            }
        }

        return maybe.andNot(no).or(yes).andNot(overflow);
    }

    /// This function is common to both `f` and `saturatingF` and is broken out here to avoid duplication.
    function _setupF(uint256 x, uint256 px, uint256 py, uint256 x0, uint256 cx)
        private
        pure
        returns (uint256 a, uint256 b, uint256 d)
    {
        unchecked {
            // Equation 2 (and 20):
            //     y = y0 + (px/py) * (x0 - x) * (cx + (1 - cx) * (x0/x))
            // We move `py` and `x` to the shared denominator and multiply the uninvolved term
            // (`cx`) by the `x`. The resulting numerator expression:
            //     px * (x0 - x) * (cx * x + (1 - cx) * x0)
            // has a basis of 1e36 from `px` and `cx` that we need to divide out. The denominator
            // expression gets a factor of 1e18 from `py`, so we need to get the other 1e18
            // explicitly.
            // The denominator expression is simply the `x` and `py` from before with the 1e18 to
            // correct the basis to match the numerator.
            a = px * (x0 - x); // scale: 1e18; units: none; range: 196 bits
            b = cx * x + (1e18 - cx) * x0; // scale: 1e18; units: token X; range: 172 bits
            d = 1e18 * x * py; // scale: 1e36; units: token X / token Y; range: 255 bits
        }
    }

    /// @dev EulerSwap curve
    /// @dev Implements equation 2 (and 20) from the whitepaper.
    /// @notice Computes the output `y` for a given input `x`.
    /// @notice The combination `x0 == 0 && cx < 1e18` is invalid.
    /// @dev Throws on overflow or `x0 == 0 && cx < 1e18`.
    /// @param x The input reserve value, constrained to `0 <= x <= x0`. (An amount of tokens in base units.)
    /// @param px (1 <= px <= 1e25). A fixnum with a basis of 1e18.
    /// @param py (1 <= py <= 1e25). A fixnum with a basis of 1e18.
    /// @param x0 (0 <= x0 <= 2^112 - 1). An amount of tokens in base units.
    /// @param y0 (0 <= y0 <= 2^112 - 1). An amount of tokens in base units.
    /// @param cx (0 <= cx <= 1e18). A fixnum with a basis of 1e18.
    /// @return y The output reserve value corresponding to input `x`, guaranteed to satisfy `y0 <= y`. (An amount of tokens in base units.)
    function f(uint256 x, uint256 px, uint256 py, uint256 x0, uint256 y0, uint256 cx) internal pure returns (uint256) {
        if (cx == 1e18) {
            unchecked {
                // `cx == 1e18` indicates that this is a constant-sum curve. Convert `x` into `y`
                // using `px` and `py`
                uint256 v = ((x0 - x) * px).unsafeDivUp(py); // scale: 1; units: token Y
                return y0 + v;
            }
        } else {
            uint256 v; // scale: 1; units: token Y
            unchecked {
                (uint256 a, uint256 b, uint256 d) = _setupF(x, px, py, x0, cx);
                v = a.mulDivUp(b, d); // Throws on divide by zero and overflow
            }
            return y0 + v; // Throws on overflow
        }
    }

    /// @dev EulerSwap curve
    /// @dev Implements equation 2 (and 20) from the whitepaper.
    /// @notice Computes the output `y` for a given input `x`.
    /// @notice The combination `x0 == 0 && cx < 1e18` is invalid.
    /// @dev Returns `type(uint256).max` on overflow or `x0 == 0 && cx < 1e18`.
    /// @param x The input reserve value, constrained to `0 <= x <= x0`. (An amount of tokens in base units.)
    /// @param px (1 <= px <= 1e25). A fixnum with a basis of 1e18.
    /// @param py (1 <= py <= 1e25). A fixnum with a basis of 1e18.
    /// @param x0 (0 <= x0 <= 2^112 - 1). An amount of tokens in base units.
    /// @param y0 (0 <= y0 <= 2^112 - 1). An amount of tokens in base units.
    /// @param cx (0 <= cx <= 1e18). A fixnum with a basis of 1e18.
    /// @return y The output reserve value corresponding to input `x`, guaranteed to satisfy `y0 <= y`. (An amount of tokens in base units.)
    function saturatingF(uint256 x, uint256 px, uint256 py, uint256 x0, uint256 y0, uint256 cx)
        internal
        pure
        returns (uint256)
    {
        unchecked {
            if (cx == 1e18) {
                // `cx == 1e18` indicates that this is a constant-sum curve. Convert `x` into `y`
                // using `px` and `py`
                uint256 v = ((x0 - x) * px).unsafeDivUp(py); // scale: 1; units: token Y
                return y0 + v;
            } else {
                (uint256 a, uint256 b, uint256 d) = _setupF(x, px, py, x0, cx);
                uint256 v = a.saturatingMulDivUp(b, d); // scale: 1; units: token Y
                return y0.saturatingAdd(v);
            }
        }
    }

    /// @dev EulerSwap inverse curve
    /// @dev Implements equations 23 through 27 from the whitepaper.
    /// @notice Computes the output `x` for a given input `y`.
    /// @notice The combination `x0 == 0 && cx < 1e18` is invalid.
    /// @param y The input reserve value, constrained to `y0 <= y <= 2^112 - 1`. (An amount of tokens in base units.)
    /// @param px (1 <= px <= 1e25). A fixnum with a basis of 1e18.
    /// @param py (1 <= py <= 1e25). A fixnum with a basis of 1e18.
    /// @param x0 (0 <= x0 <= 2^112 - 1). An amount of tokens in base units.
    /// @param y0 (0 <= y0 <= 2^112 - 1). An amount of tokens in base units.
    /// @param cx (0 <= cx <= 1e18). A fixnum with a basis of 1e18.
    /// @return x The output reserve value corresponding to input `y`, guaranteed to satisfy `0 <= x <= x0`. (An amount of tokens in base units.)
    /// @dev The maximum possible error (overestimate only) in `x` from the smallest such value that will still pass `verify` is 1 wei.
    function fInverse(uint256 y, uint256 px, uint256 py, uint256 x0, uint256 y0, uint256 cx)
        internal
        pure
        returns (uint256)
    {
        unchecked {
            // The value `B` is implicitly computed as:
            //     [(y - y0) * py * 1e18 - (cx * 2 - 1e18) * x0 * px] / px
            // We only care about the absolute value of `B` for use later, so we separately extract
            // the sign of `B` and its absolute value
            bool sign; // `true` when `B` is negative
            uint256 absB; // scale: 1e18; units: token X; range: 255 bits
            {
                uint256 term1 = 1e18 * ((y - y0) * py + x0 * px); // scale: 1e36; units: none; range: 256 bits
                uint256 term2 = (cx << 1) * x0 * px; // scale: 1e36; units: none; range: 256 bits

                // Ensure that the result will be positive
                uint256 difference; // scale: 1e36; units: none; range: 256 bits
                (difference, sign) = term1.absDiff(term2);

                // If `sign` is true, then we want to round up. Compute the carry bit
                bool carry = (0 < difference.unsafeMod(px)).and(sign);
                absB = difference.unsafeDiv(px).unsafeInc(carry);
            }

            // `twoShift` is how much we need to shift right (the log of the scaling factor) to
            // prevent overflow when computing `squaredB`, `fourAC`, or `discriminant`. `shift` is
            // half that; the amount we have to shift left by after taking the square root of
            // `discriminant` to get back to a basis of 1e18
            uint256 shift;
            {
                uint256 shiftSquaredB = absB.bitLength().saturatingSub(127);
                // 3814697265625 is 5e17 with all the trailing zero bits removed to make the
                // constant smaller. The argument of `saturatingSub` is reduced to compensate
                uint256 shiftFourAc = (x0 * 3814697265625).bitLength().saturatingSub(109);
                shift = (shiftSquaredB < shiftFourAc).ternary(shiftFourAc, shiftSquaredB);
            }
            uint256 twoShift = shift << 1;

            uint256 x; // scale: 1; units: token X; range: 113 bits
            if (sign) {
                // `B` is negative; use the regular quadratic formula; everything rounds up.
                //     (-b + sqrt(b^2 - 4ac)) / 2a
                // Because `B` is negative, `absB == -B`; we can avoid negation.

                // `fourAC` is actually the value $-4ac$ from the "normal" conversion of the
                // constant function to its quadratic form. Computing it like this means we can
                // avoid subtraction (and potential underflow)
                uint256 fourAC = (cx * (1e18 - cx) << 2).unsafeMulShiftUp(x0 * x0, twoShift); // scale: 1e36 >> twoShift; units: (token X)^2; range: 254 bits

                uint256 squaredB = absB.unsafeMulShiftUp(absB, twoShift); // scale: 1e36 >> twoShift; units: (token X)^2; range: 254 bits
                uint256 discriminant = squaredB + fourAC; // scale: 1e36 >> twoShift; units: (token X)^2; range: 254 bits
                uint256 sqrt = discriminant.sqrtUp() << shift; // scale: 1e18; units: token X; range: 172 bits

                x = (absB + sqrt).unsafeDivUp(cx << 1);
            } else {
                // `B` is nonnegative; use the "citardauq" quadratic formula; everything except the
                // final division rounds down.
                //     2c / (-b - sqrt(b^2 - 4ac))

                // `fourAC` is actually the value $-4ac$ from the "normal" conversion of the
                // constant function to its quadratic form. Therefore, we can avoid negation of
                // `absB` and both subtractions
                uint256 fourAC = (cx * (1e18 - cx) << 2).unsafeMulShift(x0 * x0, twoShift); // scale: 1e36 >> twoShift; units: (token X)^2; range: 254 bits

                uint256 squaredB = absB.unsafeMulShift(absB, twoShift); // scale: 1e36 >> twoShift; units: (token X)^2; range: 254 bits
                uint256 discriminant = squaredB + fourAC; // scale: 1e36 >> twoShift; units: (token X)^2; range: 255 bits
                uint256 sqrt = discriminant.sqrt() << shift; // scale: 1e18; units: token X; range: 255 bits

                // If `cx == 1e18` and `B == 0`, we evaluate `0 / 0`, which is `0` on the EVM. This
                // just so happens to be the correct answer
                x = ((1e18 - cx) << 1).unsafeMulDivUpAlt(x0 * x0, absB + sqrt);
            }

            // Handle any rounding error that could produce a value out of the bounds established by
            // the NatSpec
            return x.unsafeDec(x > x0);
        }
    }
}
