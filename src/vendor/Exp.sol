// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;

import {Panic} from "../utils/Panic.sol";
import {FastLogic} from "../utils/FastLogic.sol";
import {Clz} from "./Clz.sol";

library Exp {
    using FastLogic for bool;

    /// @notice Compute the natural exponential of a fixnum with 10**27 (ray) basis, returning the
    ///         result as a fixnum with 10**18 (wad) basis.
    /// @dev Let E = 10¹⁸ ⋅ exp(x / 10²⁷) be the exact, infinite-precision result. This function
    ///      returns either ⌊E⌋ or ⌊E⌋ - 1; it never overestimates. `expRayToWad(0) == 10**18`
    ///      exactly. The result is never negative. The function is monotonic; x₁ < x₂ →
    ///      expRayToWad(x₁) ≤ expRayToWad(x₂). For "central" inputs 707106781186547525 ≤ w ≤
    ///      1414213562373095048, `expRayToWad(lnWadToRay(w)) == w - 1`, except at w = 10¹⁸ where it
    ///      returns w. Reverts with `Panic(17)` when x is large enough to leave the supported range
    ///      (x ≥ 0x92b2f16cc66c5a4ae96e80d4 ≈ 45.40 ⋅ 10²⁷, i.e. E ≳ 5.22 ⋅ 10³⁷).
    function expRayToWad(int256 x) internal pure returns (int128) {
        // This is ⌈(66⋅2¹⁹² - 2¹⁹¹) / CINV⌉, with CINV the Q192 reciprocal in `_octave`; here the
        // octave count reaches 66 and the deficit envelope exceeds 1ulp.
        if (x >= 0x92b2f16cc66c5a4ae96e80d4) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }

        int256 k = _octave(x);
        unchecked {
            // 10¹⁸⋅2⁶⁷ carries 67 closing-headroom bits. The cutoff is ⌊10²⁷⋅ln(10⁻¹⁸)⌋, the
            // greatest x with 10¹⁸⋅exp(x/10²⁷) < 1.
            return int128(
                int256(
                    _expRayKernel(
                        x,
                        k,
                        0x6f05b59d3b2000000000000000000000,
                        uint256(int256(67) - k),
                        -41446531673892822312323846185
                    )
                )
            );
        }
    }

    /// @notice Compute `trunc(y * exp(x / 10**27))` with up to 1ulp of error, towards zero
    /// @dev Let A = |y| ⋅ exp(x / 10²⁷). For accepted inputs, this function returns sign(y) ⋅ m
    ///      with 0 ≤ m ≤ A ∧ A < m + 2: the magnitude m is ⌊A⌋ or ⌊A⌋ - 1, without
    ///      underflow. `mulExpRay(0, x) == 0` for every accepted x, and `mulExpRay(y, 0) == y`
    ///      exactly whenever 4⋅|y| ≤ 2¹²⁷ - 1 = 170141183460469231731687303715884105727. Among
    ///      accepted inputs, the result is monotone in `x`: nondecreasing if y ≥ 0 and
    ///      nonincreasing if y < 0. For a fixed `x`, among accepted inputs, the result is
    ///      nondecreasing in `y`. Jointly, for accepted (y₁, x₁, r₁ = mulExpRay(y₁, x₁)) and (y₂,
    ///      x₂, r₂ = mulExpRay(y₂, x₂)), r₁ ≤ r₂ when 0 ≤ y₁ ≤ y₂ ∧ x₁ ≤ x₂, when y₁ ≤ y₂ ≤ 0 ∧ x₂
    ///      ≤ x₁, and when y₁ ≤ 0 ≤ y₂ for any (x₁, x₂).
    /// @dev Reverts with `Panic(17)` when x ≥ 86989971160273136331862631244 ≈ 87.00⋅10²⁷
    ///      (regardless of y), or when round(x / (10²⁷⋅ln(2))) exceeds s - 2, with 2ˢ the scale
    ///      headroom above |y|; s = 0 at both maximal signed magnitudes and s = 127 at y = 0. The
    ///      accepted exponents form one interval that narrows as |y| grows, and every accepted x ≤
    ///      -88376265521393026950697095485 ≈ -88.38⋅10²⁷ evaluates to zero. Below the wrap boundary
    ///      (x ≲ -5.7⋅10⁴⁵) the wrapped octave word decides: such `x` revert or clamp to zero, (A <
    ///      1 there at every supported magnitude).
    function mulExpRay(int128 y, int256 x) internal pure returns (int128) {
        unchecked {
            // Split `y` into a sign mask and a magnitude
            uint256 sign = uint256(int256(y) >> 255);
            uint256 ay = (uint256(int256(y)) ^ sign) - sign;

            // The top-bit term admits ay = abs(type(int128).min) at s = 0 while leaving every
            // smaller magnitude's normalization unchanged.
            uint256 s = Clz.clz(ay) - 129 + (ay >> 127);

            int256 k = _octave(x);
            int256 shift = int256(s) - k;
            // Reject inputs whose two-unit magnitude bracket the kernel cannot deliver:
            //  * x at or above ⌈(126⋅2¹⁹² - 2¹⁹¹) / CINV⌉, where k = 126 exhausts the deficit
            //    envelope at even the maximal headroom. This fences accepted x away from
            //    `_octave`'s positive wraparound
            //  * fewer than 2 bits of closing shift: the deficit envelope (2993/1000 + margin)⋅2ᵏ⁻ˢ
            //    reaches 1ulp at k > s - 2 (see the kernel). When `_octave`'s product wraps (x ≲
            //    -2¹⁵²) its output stands in for k, so those exponents revert or pass as the
            //    wrapped word falls
            if ((x > 86989971160273136331862631243).or(shift < 2)) {
                Panic.panic(Panic.ARITHMETIC_OVERFLOW);
            }

            // Monotonicity in `y` at a fixed accepted `x`: within one headroom class (fixed s) the
            // magnitude is a composition of nondecreasing maps of `ay`. At a bit-length boundary
            // (ay reaching 2ᴸ), the scale `ay << s` does not decrease while the closing shift
            // shrinks by one, so both effects raise the result. The x = 0 pin and zero-clamp
            // preserve order, and sign reapplication mirrors the argument to y < 0. The cutoff is
            // ⌈(-127⋅2¹⁹² - 2¹⁹¹) / CINV⌉. At or below it, 2¹²⁷⋅exp(x/10²⁷) < 1, so every supported
            // magnitude clamps soundly to zero.
            uint256 m = _expRayKernel(x, k, ay << s, uint256(shift), -88376265521393026950697095485);
            // Reapply `y`'s sign and collapse y = 0 (kernel output is unspecified; scale is 0):
            //     m *= sign(y)
            assembly ("memory-safe") {
                m := mul(or(lt(0x00, ay), sign), m)
            }
            return int128(int256(m));
        }
    }

    function _octave(int256 x) private pure returns (int256 k) {
        assembly ("memory-safe") {
            // k = round(x / (10²⁷⋅ln(2))), half-open. CINV = round(2¹⁹² / (10²⁷⋅ln(2))); the +2¹⁹¹
            // and `sar(192, …)` round to nearest with ties resolved toward +∞.
            k := sar(0xc0, add(shl(0xbf, 0x01), mul(0x724d54edbacbebbb95c52a0f60, x)))
        }
    }

    /// @dev The rational polynomial approximation kernel, shared by `expRayToWad` (scale =
    ///      10¹⁸⋅2⁶⁷, shift = 67 - k) and `mulExpRay` (scale = |y|⋅2ˢ, shift = s - k).
    /// @dev The caller must maintain:
    ///       * `k == _octave(x)` and `scale <= 2**127`: the margin and deficit budgets below hold
    ///         throughout this range, and smaller scales only shrink them
    ///       * `scale == base << s` for the caller's magnitude `base`, with `shift == s - k`
    ///       * for every accepted `x` with `zeroCutoff < x` and `x != 0`: `shift >= 2` (the deficit
    ///         envelope reaches 1ulp below that), `_octave`'s product must not wrap (x ≲ 2¹⁵¹), and
    ///         `shift < 256`. At x = 0 the result is exact for any shift
    ///       * for every x ≤ zeroCutoff: base⋅exp(x / 10²⁷) < 1, so the clamped-to-zero result
    ///         satisfies the bracket. The clamp consults only `x`, so `_octave` wraparound garbage
    ///         (x ≲ -2¹⁵¹) in `k`, `t`, and `shift` is discarded
    /// @dev When `scale == 0` the returned value is unspecified and the caller must discard it.
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
        // degree 4; in exact arithmetic this (5,4) form approximates exp to ≈135 bits, and the
        // integer coefficients realize ≈133 of them: each coefficient's low bits are chosen
        // jointly, after rounding at the staircase bases, to re-center the ten quantization
        // residuals, holding the realized envelope at ≤ 0.0075 ulp. Ev(v) is monic, so its leading
        // stage is just an add.
        //
        // Mixed fixed-point bases (a staircase): each coefficient takes the widest basis fitting
        // its chosen byte width. A coefficient followed by more multiplies by `v` tolerates a
        // shorter basis. Each renormalizing shift lands a value directly at the basis its consumer
        // needs.
        //     v = t²: Q123 the widest basis whose monic-stage product stays inside 256 bits, so
        //         Ev(v)'s leading stage consumes v with no renormalizing shift. t's Q129 basis (|t|
        //         ≤ ln(2)/2) means that pre-reduction t² fits 256 bits.
        //     Ev(v) Horner down the staircase Q123 → Q97 → Q97 → Q91 → Q89
        //     Od(v) Horner down the staircase Q105 → Q102 → Q93 → Q94 → Q89
        //         t and closing bases of Ev and Od are the widest at which the t⋅Od intermediate
        //         product stays inside 256 bits
        //     dividend: Q156 the widest basis that fits in 256 bits before the single truncating
        //         `DIV` by Q89 divisor. < 2¹²⁹
        //     r: the pre-scale is at most 2¹²⁷; the strict numerator bound keeps the dividend
        //         below 2²⁵⁶ at the endpoint.
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
        // The quotient `r` carries the scaled rational on a dynamic output grid, where one grid
        // unit is worth 2ᵏ⁻ˢ ulp (1ulp = 1 in the caller's magnitude). Because scale ≤ 2¹²⁷ and Δ <
        // 1/2, its image scale⋅Δ/2¹²⁶ is below one grid unit. The margin dominates the image: 0x01,
        // worth 0.25 ulp at the supported edge. The `DIV` floor only lowers the quotient, so the
        // pre-floor accumulator A = q - margin satisfies A⋅2ᵏ⁻ˢ ≤ E. The under side is certified
        // directly on the output grid. The `DIV` floor costs one unit at any scale. On the positive
        // half, the integer-rational carry is certified similarly, while the scale-dependent 2⁻¹³²
        // and reduced-argument terms remain exact. On the negative half, the one-grain direction
        // and reduced-argument bound shrink.
        //
        // Hence the maximum underestimation is E - A⋅2ᵏ⁻ˢ ≤ (2993/1000 + margin)⋅2ᵏ⁻ˢ. The caller
        // keeps k ≤ s - 2, where this is < 1, so the floor returns ⌊E⌋ or ⌊E⌋ - 1. For the wad
        // specialization s = 67, the deficit envelope exceeds 1ulp at k ≥ 66. On the central octave
        // k = 0, the margin is 2⁻⁶⁷ ≈ 6.8⋅10⁻²¹ ulp, far below the ≈10⁻⁹ ulp gap `lnWadToRay`
        // leaves, so the round trip floors to ⌊E⌋. The k = 0 band is exactly [-H, H] with H =
        // ⌊10²⁷⋅ln(2)/2⌋, matching `lnWadToRay`'s image over [1/√2, √2).
        //
        // Monotonicity: one unit step in x multiplies E by exp(10⁻²⁷) ≈ 1 + 10⁻²⁷, which moves the
        // pre-floor accumulator by at least scale⋅10⁻²⁷/√2 > 5.2⋅10¹⁰ grid units (every live scale
        // is at least 2¹²⁶ > 10¹⁸⋅2⁶⁶). The error terms above confine the accumulator to a band of
        // width scale⋅Δ/2¹²⁶ + 2993/1000 < 4.0 grid units just below E's grid image at every octave
        // (in grid units the band is k-independent; an octave seam rescales E and the band
        // together), so the per-step gain exceeds any adverse swing within the band by more than 9
        // orders of magnitude, and the pre-floor accumulator strictly increases at every step; its
        // floor is non-decreasing. The zeroing clamp and the +1 pin at x = 0 preserve order: below
        // C the result is 0 while just above it ⌊E⌋ ≥ 0, and the adjacent runtime values around x =
        // 0 bracket the pinned scale-point value.
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

            // The scaled rational: one `DIV` scales, widens, and floors at once. The numerator
            // stays strictly below 2¹²⁹ and scale ≤ 2¹²⁷, so the dividend stays inside 256 bits;
            // the denominator > 0.
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
