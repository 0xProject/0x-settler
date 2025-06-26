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
        if ((newReserve0 | newReserve1) >> 112 != 0) return false;
        if (!(newReserve0 < equilibriumReserve0).or(newReserve1 < equilibriumReserve1)) return true;
        if (!(newReserve0 > equilibriumReserve0).or(newReserve1 > equilibriumReserve1)) return false;

        (uint256 x, uint256 y, uint256 px, uint256 py, uint256 x0, uint256 y0, uint256 cx) = (
            newReserve0 < equilibriumReserve0
        )
            ? (newReserve0, newReserve1, priceX, priceY, equilibriumReserve0, equilibriumReserve1, concentrationX)
            : (newReserve1, newReserve0, priceY, priceX, equilibriumReserve1, equilibriumReserve0, concentrationY);

        unchecked {
            if ((x == 0).and(cx == 1e18)) {
                return y - y0 >= (x0 * px).unsafeDivUp(py);
            } else {
                (uint256 a_lo, uint256 a_hi) = (y - y0).fullMul(1e18 * x * py);
                (uint256 b_lo, uint256 b_hi) = (px * (x0 - x)).fullMul(cx * x + (1e18 - cx) * x0);
                return !FullMath.fullLt(a_lo, a_hi, b_lo, b_hi);
            }
        }
    }

    /// This function is common to both `f` and `saturatingF` and is broken out here to avoid duplication.
    function _setupF(uint256 x, uint256 px, uint256 py, uint256 x0, uint256 cx)
        private
        pure
        returns (uint256 a, uint256 b, uint256 d)
    {
        unchecked {
            a = px * (x0 - x); // scale: 1e18; units: none; range: 196 bits
            b = cx * x + (1e18 - cx) * x0; // scale: 1e18; units: token X; range: 173 bits
            d = 1e18 * x * py; // scale: 1e36; units: token X / token Y; range: 255 bits
        }
    }

    /// @dev EulerSwap curve
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
        if ((x == 0).and(cx == 1e18)) {
            unchecked {
                uint256 v = (x0 * px).unsafeDivUp(py); // scale: 1; units: token Y
                return y0 + v;
            }
        } else {
            uint256 v; // scale: 1; units: token Y
            unchecked {
                (uint256 a, uint256 b, uint256 d) = _setupF(x, px, py, x0, cx);
                v = a.mulDivUp(b, d);
            }
            return y0 + v;
        }
    }

    /// @dev EulerSwap curve
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
            if ((x == 0).and(cx == 1e18)) {
                uint256 v = (x0 * px).unsafeDivUp(py); // scale: 1; units: token Y
                return y0 + v;
            } else {
                (uint256 a, uint256 b, uint256 d) = _setupF(x, px, py, x0, cx);
                uint256 v = a.saturatingMulDivUp(b, d); // scale: 1; units: token Y
                return y0.saturatingAdd(v);
            }
        }
    }

    /// @dev EulerSwap inverse curve
    /// @notice Computes the output `x` for a given input `y`.
    /// @notice The combination `x0 == 0 && cx < 1e18` is invalid.
    /// @param y The input reserve value, constrained to `y0 <= y <= 2^112 - 1`. (An amount of tokens in base units.)
    /// @param px (1 <= px <= 1e25). A fixnum with a basis of 1e18.
    /// @param py (1 <= py <= 1e25). A fixnum with a basis of 1e18.
    /// @param x0 (0 <= x0 <= 2^112 - 1). An amount of tokens in base units.
    /// @param y0 (0 <= y0 <= 2^112 - 1). An amount of tokens in base units.
    /// @param cx (0 <= cx <= 1e18). A fixnum with a basis of 1e18.
    /// @return x The output reserve value corresponding to input `y`, guaranteed to satisfy `0 <= x <= x0`. (An amount of tokens in base units.)
    function fInverse(uint256 y, uint256 px, uint256 py, uint256 x0, uint256 y0, uint256 cx)
        internal
        pure
        returns (uint256)
    {
        unchecked {
            // The value `B` is implicitly computed as:
            //     [(y - y0) * py * 1e18 - (cx * 2 - 1e18) * x0 * px] / px
            // We only care about the absolute value of `B` for use later, so we separately extract
            // the sign of `B` and its absolute value.
            bool sign; // true when `B` is negative
            uint256 absB; // scale: 1e18; units: token X; range: 255 bits
            {
                uint256 term1 = 1e18 * ((y - y0) * py + x0 * px); // scale: 1e36; units: none; range: 256 bits
                uint256 term2 = (cx << 1) * x0 * px; // scale: 1e36; units: none; range: 256 bits

                // compare to determine which branch below we need to take
                sign = term2 > term1;

                // ensure that the result will be positive
                (uint256 a, uint256 b) = sign.maybeSwap(term1, term2);
                uint256 difference = a - b; // scale: 1e36; units: none; range: 256 bits

                // if `sign` is true, then we want to round up. compute the carry bit
                bool carry = (0 < difference.unsafeMod(px)).and(sign);
                absB = difference.unsafeDiv(px).unsafeInc(carry);
            }

            uint256 C; // scale: 1; units: (token X)^2; range: 224 bits
            bool carryC; // true when we need to round C up
            {
                (uint256 C_lo, uint256 C_hi, uint256 C_rem) = FullMath._mulDivSetup(1e18 - cx, x0 * x0, 1e18);
                C = FullMath._mulDivInvert(C_lo, C_hi, 1e18, C_rem);
                carryC = 0 < C_rem;
            }

            // `twoShift` is how much we need to shift right (the log of the scaling factor) to
            // prevent overflow when computing `squaredB` or `fourAC`
            uint256 twoShift;
            {
                uint256 twoShiftSquaredB = (absB.bitLength() << 1).saturatingSub(255);
                uint256 twoShiftFourAc = C.unsafeInc(carryC).bitLength().saturatingSub(133); // 4e36 has 122 bits
                twoShift = (twoShiftSquaredB < twoShiftFourAc).ternary(twoShiftFourAc, twoShiftSquaredB);
                twoShift += twoShift & 1;
            }
            // `shift` is how much we have to shift left by after taking the square root of
            // `discriminant` to get back to a basis of 1e18
            uint256 shift = twoShift >> 1;

            uint256 x;
            if (sign) {
                // B is negative; use regular quadratic formula; everything rounds up

                C = C.unsafeInc(carryC);

                uint256 fourAC = (cx * 4e18).unsafeMulShiftUp(C, twoShift); // scale: 1e36 >> twoShift; units: (token X)^2; range: 254 bits
                uint256 squaredB = absB.unsafeMulShiftUp(absB, twoShift); // scale: 1e36 >> twoShift; units: (token X)^2; range: 254 bits
                uint256 discriminant = squaredB + fourAC; // scale: 1e36 >> twoShift; units: (token X)^2; range: 255 bits
                uint256 sqrt = discriminant.sqrtUp() << shift; // scale: 1e18; units: token X; range: 256 bits

                // use the regular quadratic formula solution (-b + sqrt(b^2 - 4ac)) / 2a
                x = (absB + sqrt).unsafeDivUp(cx << 1); // scale: 1; units: token X; range: 112 bits
            } else {
                // B is nonnegative; use "citardauq" quadratic formula; everything except C rounds down

                uint256 fourAC = (cx * 4e18).unsafeMulShift(C, twoShift); // scale: 1e36 >> twoShift; units: (token X)^2; range: 254 bits
                uint256 squaredB = absB.unsafeMulShift(absB, twoShift); // scale: 1e36 >> twoShift; units: (token X)^2; range: 254 bits
                uint256 discriminant = squaredB + fourAC; // scale: 1e36 >> twoShift; units: (token X)^2; range: 255 bits
                uint256 sqrt = discriminant.sqrt() << shift; // scale: 1e18; units: token X; range: 256 bits

                // use the "citardauq" quadratic formula solution 2c / (-b - sqrt(b^2 - 4ac))
                x = (C.unsafeInc(carryC) << 1).unsafeMulDivUpAlt(1e18, absB + sqrt); // scale: 1; units: token X; range: 112 bits
                // if `cx == 1e18` and `B == 0`, we evaluate `0 / 0`, which is `0` on the EVM. this
                // just so happens to be the correct answer.
            }

            return (x < x0).ternary(x, x0);
        }
    }
}
