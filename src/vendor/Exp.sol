// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;

import {Panic} from "../utils/Panic.sol";
import {FastLogic} from "../utils/FastLogic.sol";
import {Clz} from "./Clz.sol";

library Exp {
    using FastLogic for bool;

    // With s = clz(abs(y)) - 129, the s ≤ 127 guard admits exactly magnitudes through 2¹²⁷ − 1.
    uint256 private constant _SCALE_MAX_CLZ = 129;
    // 10¹⁸ ⋅ 2⁶⁷ < 2¹²⁷: `expRayToWad`'s scale — the wad output basis carrying 67 bits of
    // closing headroom.
    uint256 private constant _WAD_SCALE = 0x6f05b59d3b2000000000000000000000;
    // The least x whose octave count k = round(x / (10²⁷⋅ln(2))) reaches 66, i.e.
    // ⌈(66⋅2¹⁹² - 2¹⁹¹) / CINV⌉ ≈ 65.5⋅ln(2)⋅10²⁷ ≈ 45.40⋅10²⁷ (CINV is `_octave`'s
    // reciprocal): at `expRayToWad`'s fixed headroom s = 67 the deficit envelope reaches one
    // output unit at k = 66.
    int256 private constant _EXP_RAY_TO_WAD_HI = 0x92b2f16cc66c5a4ae96e80d4;
    // ⌊10²⁷ ⋅ ln(10⁻¹⁸)⌋: the greatest x with 10¹⁸⋅exp(x / 10²⁷) < 1. At or below it
    // `expRayToWad` clamps to zero; the clamp consults only x, so it also discards the
    // reduction garbage for x ≲ -2¹⁵¹ where `_octave`'s product wraps.
    int256 private constant _WAD_ZERO_MAX = -41446531673892822312323846185;
    // The least x whose octave count reaches 126, i.e. ⌈(126⋅2¹⁹² - 2¹⁹¹) / CINV⌉ ≈
    // 125.5⋅ln(2)⋅10²⁷ ≈ 87.00⋅10²⁷: the first octave past the deficit envelope at even the
    // maximal scale headroom (s = 127, at y = 0). Within the wrap-free octave range the
    // closing-shift guard already rejects these inputs; this comparison's irreducible role is
    // the fence that keeps accepted x clear of the region (x ≳ 2¹⁵¹) where `_octave`'s product
    // wraps and the octave word is garbage; without it, a wrapped word could pass the accuracy
    // guard and the kernel would return an unflagged wrong value.
    int256 private constant _MUL_EXP_RAY_HI = 86989971160273136331862631244;
    // The least x whose octave count reaches -127, i.e. ⌈(-127⋅2¹⁹² - 2¹⁹¹) / CINV⌉ ≈
    // -127.5⋅ln(2)⋅10²⁷ ≈ -88.38⋅10²⁷. At or below it the kernel clamps `mulExpRay` to zero,
    // which is within the bracket at every supported scale ((2¹²⁷ - 1)⋅exp(x/10²⁷) < 1); the
    // clamp consults only x, so it also zeroes every accepted x inside `_octave`'s negative
    // wraparound region (x ≲ -2¹⁵²). Above it, k ≥ -127 keeps the closing shift below 256 and
    // the reduced argument on the certified domain.
    int256 private constant _MUL_EXP_RAY_ZERO_MAX = -88376265521393026950697095485;

    /// @notice Compute the natural exponential of a fixnum with 10**27 (ray) basis, returning the
    ///         result as a fixnum with 10**18 (wad) basis.
    /// @dev Let E = 10¹⁸ ⋅ exp(x / 10²⁷) be the exact, infinite-precision result. This function
    ///      returns either ⌊E⌋ or ⌊E⌋ - 1; it never overestimates. `expRayToWad(0) == 10**18`
    ///      exactly. The result is never negative. The function is monotonic; x₁ < x₂ →
    ///      expRayToWad(x₁) ≤ expRayToWad(x₂). For "central" inputs 707106781186547525 ≤ w ≤
    ///      1414213562373095048, `expRayToWad(lnWadToRay(w)) == w - 1`, except at w = 10¹⁸ where it
    ///      returns w. Reverts with `Panic(17)` when x is large enough to leave the supported range
    ///      (x ≥ 0x92b2f16cc66c5a4ae96e80d4 ≈ 45.40 ⋅ 10²⁷, i.e. E ≳ 5.22 ⋅ 10³⁷).
    function expRayToWad(int256 x) internal pure returns (int256) {
        // At this input the octave count k = round(x / (10²⁷⋅ln(2))) reaches 66, where the deficit
        // envelope below exceeds 1ulp.
        if (x >= _EXP_RAY_TO_WAD_HI) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }

        int256 k = _octave(x);
        unchecked {
            return int256(_expRayKernel(x, k, _WAD_SCALE, uint256(int256(67) - k), _WAD_ZERO_MAX));
        }
    }

    /// @notice Compute y * exp(x / 10**27), with y's sign reapplied after magnitude evaluation.
    /// @dev Let A = abs(y) ⋅ exp(x / 10²⁷). For accepted inputs, this function returns sign(y) ⋅ m
    ///      with 0 ≤ m ≤ A and A < m + 2: the magnitude m is ⌊A⌋ or ⌊A⌋ - 1, except that when
    ///      A < 1 the lower bound pins m = 0. `mulExpRay(0, x) == 0` for every accepted x, and
    ///      `mulExpRay(y, 0) == y` exactly whenever 4⋅abs(y) ≤ 2¹²⁷ - 1 =
    ///      170141183460469231731687303715884105727 (larger magnitudes leave fewer than two bits
    ///      of closing shift, so x = 0 reverts there). Among accepted inputs, the result is
    ///      monotone in x: nondecreasing if y ≥ 0 and nonincreasing if y < 0. For a fixed x,
    ///      among accepted inputs, the result is nondecreasing in y. Jointly, for accepted pairs
    ///      (y₁, x₁) and (y₂, x₂), the first result is no greater than the second when 0 ≤ y₁ ≤ y₂
    ///      and x₁ ≤ x₂, when y₁ ≤ y₂ ≤ 0 and x₂ ≤ x₁, and when y₁ ≤ 0 ≤ y₂ for any exponents.
    ///
    ///      Reverts with `Panic(17)` in exactly three cases:
    ///      abs(y) > 2¹²⁷ - 1 = 170141183460469231731687303715884105727 ≈ 1.70⋅10³⁸ (including
    ///      y = type(int256).min); x ≥ 86989971160273136331862631244 ≈ 87.00⋅10²⁷ (regardless of
    ///      y); or the octave word — `_octave`'s output, which is round(x / (10²⁷⋅ln(2))) wherever
    ///      its product does not wrap (|x| ≲ 2¹⁵²) — exceeding s - 2, with 2ˢ the scale headroom
    ///      above abs(y) (the largest power of two with abs(y)⋅2ˢ < 2¹²⁷;
    ///      s = 127 at y = 0). Within the wrap-free range the accepted exponents form one
    ///      interval that narrows as abs(y) grows, and every accepted
    ///      x ≤ -88376265521393026950697095485 ≈ -88.38⋅10²⁷ evaluates to zero. Below the wrap
    ///      boundary (x ≲ -5.7⋅10⁴⁵) the wrapped octave word decides: such x revert or clamp to
    ///      zero, either of which is sound (A < 1 there at every supported magnitude).
    function mulExpRay(int256 y, int256 x) internal pure returns (int256) {
        uint256 ay;
        uint256 sign;
        // Split y into a sign mask and a magnitude without negating `type(int256).min`:
        //     sign = y >> 255; ay = (y ^ sign) - sign
        assembly ("memory-safe") {
            sign := sar(0xff, y)
            ay := sub(xor(y, sign), sign)
        }

        unchecked {
            // The scale headroom aligns ay's top bit with bit 126 (127 at ay = 0), keeping every
            // supported pre-scale below 2¹²⁷ without a value comparison. For a 128-bit or larger
            // ay, clz comes up short of _SCALE_MAX_CLZ and the subtraction
            // underflows to a word whose int256 value is in [-129, -1]. The magnitude guard below
            // rejects every such ay after FastLogic eagerly evaluates the garbage shift comparison.
            uint256 s = Clz.clz(ay) - _SCALE_MAX_CLZ;

            int256 k = _octave(x);
            int256 shift = int256(s) - k;
            // Reject inputs whose two-unit magnitude bracket the kernel cannot deliver:
            //  - abs(y) requiring at least 128 bits;
            //  - x at or above the octave (k = 126) that exhausts the deficit envelope at even
            //    the maximal headroom, phrased as one signed comparison against the constant
            //    less one; its irreducible role is fencing accepted x away from `_octave`'s
            //    positive wraparound (see `_MUL_EXP_RAY_HI`);
            //  - fewer than two bits of closing shift: the deficit envelope
            //    (2993/1000 + margin)⋅2ᵏ⁻ˢ reaches one output unit at k > s - 2 (see the
            //    kernel). This also rejects x = 0 when abs(y) leaves s ≤ 1, although the pinned
            //    result would be exact. When `_octave`'s product wraps (x ≲ -2¹⁵²) its output
            //    stands in for k, so those exponents revert or pass as the wrapped word falls;
            //    the kernel's clamp zeroes every accepted one.
            if ((s > 127).or(x > _MUL_EXP_RAY_HI - 1).or(shift < 2)) {
                Panic.panic(Panic.ARITHMETIC_OVERFLOW);
            }

            // Monotonicity in y at a fixed accepted x: within one headroom class (fixed s) the
            // magnitude is a composition of nondecreasing maps of ay. At a bit-length boundary
            // (ay reaching 2ᴸ), the scale ay << s does not decrease while the closing shift shrinks
            // by one, so both effects raise the result. The x = 0 pin and zero clamp preserve order,
            // and sign reapplication mirrors the argument to y < 0.
            uint256 m = _expRayKernel(x, k, ay << s, uint256(shift), _MUL_EXP_RAY_ZERO_MAX);
            // Reapply y's sign and collapse y = 0 (whose kernel output is unspecified; the scale
            // is zero) in one branchless step:
            //     m *= sgn(y)
            assembly ("memory-safe") {
                m := mul(m, or(sign, lt(0, ay)))
            }
            return int256(m);
        }
    }

    function _octave(int256 x) private pure returns (int256 k) {
        // Round to the nearest octave:
        //     k = round(x / (10**27 * ln(2)))
        assembly ("memory-safe") {
            // k = round(x / (10²⁷⋅ln(2))), half-open. CINV = round(2¹⁹² / (10²⁷⋅ln(2))); the +2¹⁹¹
            // and `sar(192, …)` round to nearest with ties resolved toward +∞.
            k := sar(0xc0, add(shl(0xbf, 0x01), mul(0x724d54edbacbebbb95c52a0f60, x)))
        }
    }

    /// @dev The rational polynomial approximation kernel, shared by `expRayToWad`
    ///      (scale = 10¹⁸⋅2⁶⁷, shift = 67 - k) and `mulExpRay` (scale = abs(y)⋅2ˢ, shift = s - k).
    ///      The caller must maintain:
    ///       - `k == _octave(x)` and `scale < 2¹²⁷`: the margin and deficit budgets below
    ///         hold throughout this range, and smaller scales only shrink them;
    ///       - `scale == base << s` for the caller's magnitude base, with `shift == s - k`;
    ///       - for every accepted x with `zeroCutoff` < x and x ≠ 0: `shift ≥ 2` (the deficit
    ///         envelope reaches one output unit below that), `_octave`'s product must not wrap
    ///         (x ≲ 2¹⁵¹), and `shift < 256`. At x = 0 the result is exact for any shift;
    ///       - for every x ≤ `zeroCutoff`: base⋅exp(x / 10²⁷) < 1, so the clamped-to-zero result
    ///         satisfies the bracket. The clamp consults only x, so `_octave` wraparound garbage
    ///         (x ≲ -2¹⁵¹) in k, t, and shift is discarded.
    ///      When `scale == 0` the returned value is unspecified and the caller must discard it.
    function _expRayKernel(int256 x, int256 k, uint256 scale, uint256 shift, int256 zeroCutoff)
        private
        pure
        returns (uint256 r)
    {
        // Equivalent pseudocode; fixed-point truncations are accounted for below:
        //     t = x/10²⁷ - k⋅ln(2);        // range-reduced argument; Q129
        //     ev = Ev(t²);                 // polynomial approximation; Q89
        //     od = Od(t²);                 // polynomial approximation; Q89
        //     n = ev + t⋅od;               // rational numerator; Q89
        //     d = ev - t⋅od;               // rational denominator; Q89
        //     e = scale⋅n / d;             // ≈ scale⋅exp(t)
        //     r = ⌊(e - margin) / 2ˢʰⁱᶠᵗ⌋;
        //     r = r ⋅ (x > zeroCutoff);
        //     return r + (x == 0);         // pin exact scale points
        //
        // `exp(t) = (1 + tanh(t/2)) / (1 - tanh(t/2))`, so with the even/odd split N(t) = Ev(t²) +
        // t⋅Od(t²) the quotient N(t)/N(-t) is the reciprocal-symmetric rational that matches
        // `Od/Ev` to `tanh(√v/2)/√v` on v = t² ∈ [0, (ln(2)/2)²]. Ev(v) is degree 5 and Od(v)
        // degree 4; in exact arithmetic this (4,5) form approximates exp to ≈135 bits, and the
        // integer coefficients realize ≈133 of them: each coefficient's low bits are chosen
        // jointly, after rounding at the staircase bases, to re-center the ten quantization
        // residuals, holding the realized envelope at ≤ 0.0075 ulp. Ev(v) is monic, so its leading
        // stage is just an add.
        //
        // Mixed fixed-point bases (a staircase): each coefficient takes the widest basis fitting
        // its chosen byte width. A coefficient followed by more multiplies by v tolerates a shorter
        // basis. Each renormalizing shift lands a value directly at the basis its consumer needs.
        //     v = t²: Q123 the widest basis whose monic-stage product stays inside 256 bits, so
        //         Ev(v)'s leading stage consumes v with no renormalizing shift. t's Q129 basis (|t|
        //         ≤ ln(2)/2) means that pre-reduction t² fits 256 bits.
        //     Ev(v) Horner down the staircase Q123 → Q97 → Q97 → Q91 → Q89
        //     Od(v) Horner down the staircase Q105 → Q102 → Q93 → Q94 → Q89
        //         t and closing bases of Ev and Od are the widest at which the t⋅Od intermediate
        //         product stays inside 256 bits
        //     dividend: Q156 the widest basis that fits in 256 bits before the single truncating
        //         `DIV` by Q89 divisor. < 2¹²⁹
        //     r: the pre-scale is below 2¹²⁷ to avoid overflowing the dividend.
        //     output: the closing `shr(shift, …)` is the output-rounding floor, with the 2ᵏ octave
        //         scaling folded into the caller's scale/shift pair.
        //
        // Error budget. Let ê = N/D be the exact value of the integer rational (N = Ev + t⋅Od, D =
        // Ev - t⋅Od; the closing `DIV` floor is counted on the output grid below) and write its
        // excess over exp(t) as Δ = (ê - exp(t))⋅2¹²⁶ (in Q126 units, one unit = 2⁻¹²⁶). The
        // budget bounds Δ ≤ 0.4668745981919039833, the sum
        // of four one-sided contributions:
        //     integer Horner truncation: the shared Ev cancels to first order in the quotient, so
        //         its truncation barely perturbs ê; this jitter stays ≤ 0.1102011232081646123.
        //     argument granularity: v carries t² on the Q123 grid, and its floor only lowers the
        //         polynomials' shared argument, which lifts ê on the t > 0 half by
        //         ≤ 0.3290521163436398582: one v-grain moves the quotient by
        //         2t⋅(Od⋅ΔEv - Ev⋅ΔOd)/(D⋅D′), whose one-signed numerator is maximal at each
        //         piece's upper edge and whose denominator, analyzed over 32 domain pieces, has
        //         pointwise supremum ≈ 0.3287 at t = ln(2)/2. The t < 0 direction is budgeted on
        //         the under side.
        //     rational `Mp`-factor (the dyadic gap between the reciprocal-symmetric form and exp):
        //         ≤ 0.0220970869120796102 (its supremum is √2⋅2¹²⁶/(2¹³²-1)).
        //     reduced-argument gap: the Q129 floor of t only pushes ê downward (that direction is
        //         budgeted on the under side); the over side is the K27/LN2 constant-grid residue
        //         (the K27 coefficient-grid term is below 2⁻¹³³ over |x| < 2⁹⁷ and the k⋅ln(2)
        //         grid term below 2⁻²²⁸), lifting ê by ≤ 0.0055242717280199026 (≈ √2/256).
        //
        // The quotient `r` carries the scaled rational on a dynamic output grid, where one grid unit
        // is worth 2ᵏ⁻ˢ ulp (1 ulp = 1 in the caller's magnitude). Because scale < 2¹²⁷ and
        // Δ < 1/2, its image scale⋅Δ/2¹²⁶ is below one grid unit. The margin dominates the image:
        // 0x01, worth 0.25 ulp at the supported edge. The `DIV` floor only lowers the quotient, so
        // the pre-floor accumulator A = q - margin satisfies A⋅2ᵏ⁻ˢ ≤ E. The under side is
        // certified directly on the output grid, piecewise over the 32 domain pieces: q ≥
        // scale⋅exp(t) - 2993/1000. The `DIV` floor costs one unit at any scale. On the positive
        // half, the integer-rational carry is certified over the same 32 pieces used for the
        // denominator floors, while the scale-dependent 2⁻¹³² and reduced-argument terms remain
        // exact. On the negative half, the one-grain direction and reduced-argument bound shrink.
        //
        // Hence the maximum underestimation is E - A⋅2ᵏ⁻ˢ ≤ (2993/1000 + margin)⋅2ᵏ⁻ˢ. The caller
        // keeps k ≤ s - 2, where this is < 1, so the floor returns ⌊E⌋ or ⌊E⌋ - 1. For the wad
        // specialization s = 67, the deficit envelope exceeds 1ulp at k ≥ 66. On the central octave
        // k = 0, the margin is 2⁻⁶⁷ ≈ 6.8⋅10⁻²¹ ulp, far below the ≈10⁻⁹ ulp gap `lnWadToRay`
        // leaves, so the round trip floors to ⌊E⌋. The k = 0 band is exactly [-H, H] with H =
        // ⌊10²⁷⋅ln(2)/2⌋, matching `lnWadToRay`'s image over [1/√2, √2).
        //
        // Monotonicity: one unit step in x multiplies E by exp(10⁻²⁷) ≈ 1 + 10⁻²⁷, which moves the
        // pre-floor accumulator by at least scale⋅10⁻²⁷/√2 > 5.2⋅10¹⁰ grid units (every live
        // scale is at least 2¹²⁶ > 10¹⁸⋅2⁶⁶). The error
        // terms above confine the accumulator to a band of width scale⋅Δ/2¹²⁶ + 2993/1000 < 4.0 grid
        // units just below E's grid image at every octave (in grid units the band is k-independent;
        // an octave seam rescales E and the band together), so the per-step gain exceeds any
        // adverse swing within the band by more than 9 orders of magnitude, and the pre-floor
        // accumulator strictly increases at every step; its floor is non-decreasing. The zeroing
        // clamp and the +1 pin at x = 0 preserve order: below C the result is 0 while just above it
        // ⌊E⌋ ≥ 0, and the adjacent runtime values around x = 0 bracket the pinned scale-point
        // value.
        assembly ("memory-safe") {
            // t in Q129. K27 = round(2²³⁵ / 10²⁷) and LN2 = round(ln(2) ⋅ 2²³⁵). Subtracting k⋅LN2
            // from K27⋅x at the Q235 product basis (so the k⋅ln(2) rounding error stays below
            // 2⁻²²⁸ over |k| ≤ 127, far below an output ulp) then one `sar(106, …)` leaves the
            // reduced argument at Q129.
            let t :=
                sar(
                    0x6a,
                    sub(
                        mul(0x279d346de4781f921dd7a89933d54d1f72928, x),
                        mul(0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d, k)
                    )
                )

            // v = t² in Q123: the widest basis at which the monic-stage product below stays inside
            // 256 bits.
            let v := shr(0x87, mul(t, t))

            // Ev(0) = 2⋅Od(0) by construction.
            let c0 := 0x9c2948bcaca16a0dd2fe98bb4470c388

            // Ev(v), monic, Horner down the staircase.
            let ev := add(0xb9aacfacf3c10b378435f8e22adf48500e, v)
            ev := add(0x9a036222841f47c6ed6fc3f7599445, shr(0x95, mul(ev, v)))
            ev := add(0x9064d9657e9a21fc16bb69331b81ae1e, shr(0x7b, mul(ev, v)))
            ev := add(0x93f11e650dd6c64b96ce79065cdf80f4, shr(0x81, mul(ev, v)))
            ev := add(shl(0x01, c0), shr(0x7d, mul(ev, v)))

            // Od(v), Horner down the staircase.
            let od := 0xdc07aff8276bde9a361278df6a10
            od := add(0xc926ddbecdeeb42e68cd16db7ed378, shr(0x7e, mul(od, v)))
            od := add(0xad4506af99be27419341e181693281, shr(0x84, mul(od, v)))
            od := add(0xaf566247c05753b42892f77b67a6b7c7, shr(0x7a, mul(od, v)))
            od := add(c0, shr(0x80, mul(od, v)))

            // t⋅Od in Q89 (signed via t); the numerator Ev + t⋅Od and denominator Ev - t⋅Od are
            // both positive.
            let tod := sar(0x81, mul(t, od))

            // The scaled rational: the caller keeps scale < 2¹²⁷, so one `DIV` scales, widens,
            // and floors at once. The numerator stays below 2¹²⁹ and scale < 2¹²⁷, so the
            // dividend stays inside 256 bits; the denominator > 0.
            r := div(mul(scale, add(ev, tod)), sub(ev, tod))

            // Less the one-sided margin (0x01; see the budget above), then floored by
            // `shr(shift, …)` which folds in the 2ᵏ octave scaling.
            r := shr(shift, sub(r, 0x01))

            // Zero results whose exact magnitude is below one output unit. For very negative x,
            // this also discards arithmetic outside the reduction range.
            r := mul(slt(zeroCutoff, x), r)

            // exp(0) = 1 is the only input whose exact result is an integer; the construction lands
            // one unit below the input magnitude, so add one back exactly there.
            r := add(iszero(x), r)
        }
    }
}
