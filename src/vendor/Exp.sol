// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;

import {Panic} from "../utils/Panic.sol";

library Exp {
    /// @notice Compute the natural exponential of a fixnum with 10**27 (ray) basis, returning the
    ///         result as a fixnum with 10**18 (wad) basis.
    /// @dev Let E = 10¹⁸ ⋅ exp(x / 10²⁷) be the exact, infinite-precision result. This function
    ///      returns either ⌊E⌋ or ⌊E⌋ - 1; it never overestimates. `expRayToWad(0) == 10**18`
    ///      exactly. The result is never negative. The function is monotonic; x₁ < x₂ →
    ///      expRayToWad(x₁) ≤ expRayToWad(x₂). For "central" inputs 707106781186547525 ≤ w ≤
    ///      1414213562373095048, `expRayToWad(lnWadToRay(w)) == w - 1`, except at w = 10¹⁸ where it
    ///      returns w. Reverts with `Panic(17)` when x is large enough to leave the supported range
    ///      (x ≥ 0x907595ccd30708cabec8a9db ≈ 44.71 ⋅ 10²⁷, i.e. E ≳ 2.61 ⋅ 10³⁷).
    function expRayToWad(int256 x) internal pure returns (int256) {
        // At this input the octave count k = round(x / (10²⁷⋅ln(2))) reaches 65, where the deficit
        // envelope below exceeds 1ulp.
        if (x >= 0x907595ccd30708cabec8a9db) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
        return _expRayToWad(x);
    }

    /// @dev The rational polynomial approximation kernel
    function _expRayToWad(int256 x) private pure returns (int256 r) {
        // Equivalent pseudocode; fixed-point truncations are accounted for below:
        //     k = round(x / (10²⁷⋅ln(2)));                   // x = (k⋅ln(2) + t)⋅10²⁷, |t| ≤ ln(2)/2
        //     t = x/10²⁷ - k⋅ln(2);                          // range-reduced argument (Q128)
        //     e = 10¹⁸⋅(Ev(t²) + t⋅Od(t²)) / (Ev(t²) - t⋅Od(t²)); // ≈ 10¹⁸⋅exp(t) in Q68
        //     r = ⌊(e - margin)⋅2ᵏ⌋;                         // wad
        //     r = r ⋅ (x > C);                               // C = ⌊-18⋅ln10⋅10²⁷⌋; 0 where E < 1
        //     return r + (x == 0);                           // pin exp(0) = 10¹⁸ exactly
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
        //     t: Q128 (from the Q235 reduction K27⋅x - k⋅LN2; |t| ≤ ln(2)/2)
        //     v = t²: Q123 the widest basis whose monic-stage product stays inside 256 bits, so
        //         Ev(v)'s leading stage consumes v with no renormalizing shift
        //     Ev(v) Horner down the staircase Q123 → Q97 → Q97 → Q91 → Q88 (monic)
        //     Od(v) Horner down the staircase Q105 → Q102 → Q93 → Q94 → Q89
        //     t⋅Od and the numerator/denominator: Q88. The closing bases are the widest at which
        //         the t⋅Od intermediate product stays inside 256 bits
        //     quotient: one `DIV` placing 10¹⁸⋅exp(t) at Q68. The numerator is pre-scaled by
        //         10¹⁸⋅2⁶⁸ = 5¹⁸⋅2⁸⁶, the widest such scale at which the dividend stays inside 256
        //         bits, and the `DIV` floor is the pipeline's only truncation of the quotient
        //     output: the closing `shr(68 - k, …)` is the single output-rounding floor, with the 2ᵏ
        //         octave scaling folded in
        //
        // Error budget. Let ê = N/D be the exact value of the integer rational (N = Ev + t⋅Od, D =
        // Ev - t⋅Od; the closing `DIV` floor is counted on the output grid below) and write its
        // excess over exp(t) as Δ = (ê - exp(t))⋅2¹²⁶ (in Q126 units, one unit = 2⁻¹²⁶). Δ is the
        // tightest bound the proof technique can bear, in spite of the fact that the worst-case
        // error contributions do not co-occur. The budget bounds Δ ≤ 0.5792534503673398887, the sum
        // of four one-sided contributions:
        //     integer Horner truncation: the Ev shared by the numerator Ev + t⋅Od and denominator
        //         Ev - t⋅Od cancels to first order in the quotient, so its truncation barely
        //         perturbs ê; this jitter stays < 0.21706.
        //     argument granularity: v carries t² on the Q123 grid, and its floor only lowers the
        //         polynomials' shared argument (by < 2⁻¹²³), which lifts ê on the t > 0 half by <
        //         0.32906: one v-grain moves the quotient by 2t⋅(Od⋅ΔEv - Ev⋅ΔOd)/(D⋅D′), whose
        //         one-signed numerator is maximal at each piece's upper edge and whose denominator
        //         is floored piecewise over 32 domain pieces (the pointwise supremum is ≈ 0.3287 at
        //         t = ln(2)/2). The t < 0 direction is budgeted on the under side.
        //     rational `Mp`-factor (the dyadic gap between the reciprocal-symmetric form and exp):
        //         < 0.02210 (its supremum is √2⋅2¹²⁶/(2¹³²-1)).
        //     reduced-argument gap: the Q128 floor of t only pushes ê downward (that direction is
        //         budgeted on the under side); the over side is the K27/LN2 constant-grid residue
        //         (the k⋅ln(2) grid error stays below 2⁻²²⁹), enveloped one-sidedly at 2⁻¹³³ of
        //         reduced argument, lifting ê by < 0.01105 (√2⋅2¹²⁶/(32⋅2¹²⁸) = √2/128).
        // The quotient carries 10¹⁸⋅ê on the 2⁶⁸ output grid, where one grid unit is worth 2ᵏ⁻⁶⁸
        // ulp (1 ulp = 10⁻¹⁸ of the result) and Δ's image is 5¹⁸⋅Δ/2⁴⁰ < 2.0097 grid units. The
        // margin is the least integer strictly above that image: 0x03 (the excess over Δ's image
        // meets the strict never-overestimate requirement), worth 3/2⁴ = 0.1875 ulp at the
        // supported edge k = 64. The `DIV` floor only lowers the quotient, so the pre-floor
        // accumulator A = q - margin satisfies A⋅2ᵏ⁻⁶⁸ ≤ E. The under side is certified directly on
        // the output grid: q ≥ 10¹⁸⋅2⁶⁸⋅exp(t) - 33/4, where 33/4 bounds the sum of the
        // integer-rational deficit together with the `DIV` floor (≤ 6210/1000; the Horner deficit
        // is 3/2 in Q126 units and the floor is one grid unit), the `Mp` factor (≤ 2/25, via ê ≤
        // 1.45), the under-direction reduced-argument gap (≤ 1267/1000, via exp(t) ≤ √2), and the
        // under-direction argument granularity (≤ 571/1000: the one-grain envelope with the
        // negative-half denominator floor; free on the t > 0 half). Hence the maximum
        // underestimation is E - A⋅2ᵏ⁻⁶⁸ ≤ (33/4 + margin)⋅2ᵏ⁻⁶⁸ = (45/4)⋅2ᵏ⁻⁶⁸ ≈ 0.7031 ulp at
        // k = 64 < 1, so the floor returns ⌊E⌋ or ⌊E⌋ - 1. The
        // deficit envelope doubles each octave and can exceed 1ulp at k ≥ 65. On the central octave
        // k = 0 the margin is 3⋅2⁻⁶⁸ ≈ 1.0⋅10⁻²⁰ ulp, far below the ≈10⁻⁹ ulp gap `lnWadToRay`
        // leaves, so the round trip floors to ⌊E⌋. The k = 0 band is exactly [-H, H] with H =
        // ⌊10²⁷⋅ln(2)/2⌋, matching `lnWadToRay`'s image over [1/√2, √2).
        //
        // Monotonicity: one unit step in x multiplies E by exp(10⁻²⁷) ≈ 1 + 10⁻²⁷, which moves the
        // pre-floor accumulator by at least 10¹⁸⋅2⁶⁸⋅10⁻²⁷/√2 ≈ 2.1⋅10¹¹ grid units. The error
        // terms above confine the accumulator to a band of width 5¹⁸⋅Δ/2⁴⁰ + 33/4 ≈ 10.3
        // grid units just below E's grid image at every octave (in grid units the band is
        // k-independent; an octave seam rescales E and the band together), so the per-step gain
        // exceeds any adverse swing within the band by more than 9 orders of magnitude, and the
        // pre-floor accumulator strictly increases at every step; its floor is non-decreasing. The
        // zeroing clamp and the +1 pin at x = 0 preserve order: below C the result is 0 while just
        // above it ⌊E⌋ ≥ 0, and the adjacent runtime values around x = 0 bracket the pinned
        // scale-point value.
        assembly ("memory-safe") {
            // k = round(x / (10²⁷⋅ln(2))), half-open. CINV = round(2¹⁹² / (10²⁷⋅ln(2))); the +2¹⁹¹
            // and `sar(192, …)` round to nearest with ties resolved toward +∞.
            let k := sar(0xc0, add(shl(0xbf, 0x01), mul(0x724d54edbacbebbb95c52a0f60, x)))

            // t in Q128. K27 = round(2²³⁵ / 10²⁷) and LN2 = round(ln(2) ⋅ 2²³⁵). Subtracting k ⋅
            // LN2 from K27 ⋅ x at the Q235 product basis (so the k ⋅ ln(2) rounding error is
            // ~2⁻²³⁵, far below an output ulp) then one `sar(107, …)` leaves the reduced argument
            // at Q128.
            let t :=
                sar(
                    0x6b,
                    sub(
                        mul(0x279d346de4781f921dd7a89933d54d1f72928, x),
                        mul(0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d, k)
                    )
                )

            // v = t² in Q123 (nonnegative; logical shift): the widest basis at which the
            // monic-stage product below stays inside 256 bits.
            let v := shr(0x85, mul(t, t))

            // Ev(0) = 2⋅Od(0) by construction, so at closing bases one bit apart (Q88/Q89) the
            // constant terms are the same.
            let c0 := 0x9c2948bcaca16a0dd2fe98bb4470c388

            // Ev(v), monic, Horner down the staircase. The leading v⁵ coefficient is 1, so the
            // first stage is just an add.
            let ev := add(0xb9aacfacf3c10b378435f8e22adf48500e, v)
            ev := add(0x9a036222841f47c6ed6fc3f7599445, shr(0x95, mul(ev, v)))
            ev := add(0x9064d9657e9a21fc16bb69331b81ae1e, shr(0x7b, mul(ev, v)))
            ev := add(0x93f11e650dd6c64b96ce79065cdf80f4, shr(0x81, mul(ev, v)))
            ev := add(c0, shr(0x7e, mul(ev, v)))

            // Od(v), Horner down the staircase.
            let od := 0xdc07aff8276bde9a361278df6a10
            od := add(0xc926ddbecdeeb42e68cd16db7ed378, shr(0x7e, mul(od, v)))
            od := add(0xad4506af99be27419341e181693281, shr(0x84, mul(od, v)))
            od := add(0xaf566247c05753b42892f77b67a6b7c7, shr(0x7a, mul(od, v)))
            od := add(c0, shr(0x80, mul(od, v)))

            // t⋅Od in Q88 (signed via t); the numerator Ev + t⋅Od and denominator Ev - t⋅Od are
            // both positive.
            let tod := sar(0x81, mul(t, od))

            // 10¹⁸⋅exp(t) in Q68: the constant is 10¹⁸⋅2⁶⁸ = 5¹⁸⋅2⁸⁶, so one `DIV` scales, widens,
            // and floors at once. The numerator stays below 2¹²⁸ and 10¹⁸⋅2⁶⁸ < 2¹²⁸, so the
            // dividend stays inside 256 bits; the denominator > 0.
            r := div(mul(0xde0b6b3a764000000000000000000000, add(ev, tod)), sub(ev, tod))

            // Less the one-sided margin (0x03; see the budget above), then floored by
            // `shr(68 - k, …)` which folds in the 2ᵏ octave scaling (68 - k ∈ [4, 128]).
            r := shr(sub(0x44, k), sub(r, 0x03))

            // Zero the result at and below C = ⌊-18⋅ln(10)⋅10²⁷⌋ = ⌊10²⁷⋅ln(10⁻¹⁸)⌋, the greatest x
            // with E < 1. This is the exact 0/1 output boundary, and it sits far above the inputs
            // where the reduction would overflow, so it also discards those (otherwise garbage).
            r := mul(slt(sub(0x00, 0x85ebc478242540a11f5f1029), x), r)

            // exp(0) = 1 is the only input whose exact result is an integer; the construction lands
            // on 10¹⁸ - 1, so add one back exactly there.
            r := add(iszero(x), r)
        }
    }
}
