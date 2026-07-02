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
    ///      (x ≥ 0x8e383a2cdfa1b74a9422d2e1 ≈ 44.01 ⋅ 10²⁷, i.e. E ≳ 1.30 ⋅ 10³⁷).
    function expRayToWad(int256 x) internal pure returns (int256 r) {
        // At this input the octave count k = round(x / (10²⁷⋅ln(2))) reaches 64. The error in
        // `_expRayToWad` exceeds 1ulp at that scale.
        if (x >= 0x8e383a2cdfa1b74a9422d2e1) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
        r = _expRayToWad(x);
    }

    /// @dev The rational polynomial approximation kernel
    function _expRayToWad(int256 x) private pure returns (int256 r) {
        // Equivalent pseudocode; fixed-point truncations are accounted for below:
        //     k = round(x / (10²⁷⋅ln(2)));                   // x = (k⋅ln(2) + t)⋅10²⁷, |t| ≤ ln(2)/2
        //     t = x/10²⁷ - k⋅ln(2);                          // reduced argument (Q128)
        //     e = (Ev(t²) + t⋅Od(t²)) / (Ev(t²) - t⋅Od(t²)); // ≈ exp(t) (Ev Q87; Od Q87; e Q126)
        //     r = ⌊(10¹⁸⋅e)⋅2ᵏ - margin⌋;                    // wad
        //     r = r ⋅ (x > C);                               // C = ⌊-18⋅ln10⋅10²⁷⌋; 0 where E < 1
        //     return r + (x == 0);                           // pin exp(0) = 10¹⁸ exactly
        //
        // `exp(t) = (1 + tanh(t/2)) / (1 - tanh(t/2))`, so with the even/odd split N(t) = Ev(t²) +
        // t⋅Od(t²) the quotient N(t)/N(-t) is the reciprocal-symmetric rational that matches
        // `Od/Ev` to `tanh(√v/2)/√v` on v = t² ∈ [0, (ln(2)/2)²]. Ev(v) is degree 5 and Od(v)
        // degree 4; in exact arithmetic this (4,5) form approximates exp to ≈135 bits, and the
        // integer coefficients realize ≈131 of them: each coefficient's low bits are chosen
        // jointly, after rounding at the staircase bases, to re-center the ten quantization
        // residuals, holding the realized envelope at ≤ 0.019 ulp. Ev(v) is monic, so its leading
        // stage is just an add.
        //
        // Mixed fixed-point bases (a staircase): each coefficient takes the widest basis fitting
        // its chosen byte width. A coefficient followed by more multiplies by v tolerates a shorter
        // basis. Each renormalizing shift lands a value directly at the basis its consumer needs.
        //     t:      Q128 (from the Q235 reduction K27⋅x - k⋅LN2; |t| ≤ ln(2)/2)
        //     v = t²: Q123 the widest basis whose monic-stage product stays inside 256 bits, so
        //         Ev(v)'s leading stage consumes v with no renormalizing shift
        //     Ev(v) Horner down the staircase Q123 → Q97 → Q97 → Q91 → Q87 (monic)
        //     Od(v) Horner down the staircase Q105 → Q102 → Q93 → Q94 → Q87
        //     Ev, Od, t⋅Od, and the numerator/denominator: Q87
        //     quotient: one `DIV` placing exp(t) at Q126 (the dividend, numerator << 126, stays
        //         below 2²⁵⁵)
        //     output: multiplying by 5¹⁸ lands E on the 2¹⁰⁸ output grid (the 10¹⁸⋅2¹²⁶ grid with
        //         the wad unit's 2¹⁸ pre-folded); the closing `shr(108 - k, …)` is the single
        //         output-rounding floor, with 2ᵏ folded in
        //
        // Error budget. The integer rational `e` lands on the Q126 grid; write its excess over the
        // exact quotient as Δ = (e - exp(t))⋅2¹²⁶ (in Q126 units, one unit = 2⁻¹²⁶). Δ is the
        // tightest bound the proof technique can bear, in spite of the fact that the worst-case
        // error contributions do not co-occur. The budget bounds Δ ≤ 1.0050013498897899168, the sum
        // of four one-sided contributions:
        //     integer Horner + closing `DIV` truncation: the Ev shared by the numerator Ev + t⋅Od
        //         and denominator Ev - t⋅Od cancels to first order in the quotient, so its
        //         truncation barely perturbs e; this jitter stays < 0.62071.
        //     argument granularity: v carries t² on the Q123 grid, and its floor only lowers the
        //         polynomials' shared argument (by < 2⁻¹²³), which lifts e on the t > 0 half by <
        //         0.32906: one v-grain moves the quotient by 2t⋅(Od⋅ΔEv - Ev⋅ΔOd)/(D⋅D′), whose
        //         one-signed numerator is maximal at each piece's upper edge and whose denominator
        //         is floored piecewise over 32 domain pieces (the pointwise supremum is ≈ 0.3287 at
        //         t = ln(2)/2). The t < 0 direction is budgeted on the under side.
        //     rational `Mp`-factor (the dyadic gap between the reciprocal-symmetric form and exp):
        //         < 0.04420 (its supremum is √2⋅2¹²⁶/(2¹³¹-1)).
        //     reduced-argument gap: the Q128 floor of t only pushes e downward (that direction is
        //         budgeted on the under side); the over side is the K27/LN2 constant-grid residue
        //         (the k⋅ln(2) grid error stays below 2⁻²²⁹), which the proof envelopes one-sidedly
        //         at 2⁻¹³³ of reduced argument, lifting e by < 0.01105 (√2⋅2¹²⁶/(32⋅2¹²⁸) =
        //         √2/128).
        // Scaling by 10¹⁸⋅2ᵏ, the accumulator's excess over E peaks at the supported edge k = 63 at
        // S = 10¹⁸⋅Δ/2⁶³ ≈ 0.1090 ulp (1 ulp = 10⁻¹⁸ of the result). The margin is the least integer
        // on the 2¹⁰⁸ output grid strictly above Δ's image: 0x37c9ed9cabf = ⌊5¹⁸⋅Δ⌋ + 1 =
        // 3833775901375 (worth ≈ S ulp at k = 63; the +1 is needed to meet the strict never
        // overestimate requirement). So 10¹⁸⋅e⋅2ᵏ - margin ≤ E. The under side is bounded to the
        // same precision: e⋅2¹²⁶ ≥ exp(t)⋅2¹²⁶ - 67/10, where 67/10 bounds the sum of the
        // integer-rational deficit (≤ 6001/1000, the Horner/`DIV`/floor truncation against the
        // denominator), the `Mp` factor (≤ 1/20, via e ≤ 1.45·2¹²⁶), the under-direction
        // reduced-argument gap (≤ 37/100, via exp(t) ≤ √2), and the under-direction argument
        // granularity (≤ 17/100: the same one-grain envelope with the negative-half denominator
        // floor). Hence the maximum underestimation of the pre-floor accumulator A is E - A ≤
        // ((67/10)⋅10¹⁸ + 2¹⁸⋅margin)/2⁶³ ≈ 0.83538 < 1, so the floor returns ⌊E⌋ or ⌊E⌋ - 1. The
        // deficit envelope ((67/10)⋅10¹⁸ + 2¹⁸⋅margin)/2^(126 - k) doubles each octave, so at k = 64 it
        // exceeds 1ulp. On the central octave k = 0 the margin is margin⋅2⁻¹⁰⁸ ≈ 1.2⋅10⁻²⁰ ulp, far
        // below the ≈10⁻⁹ ulp gap `lnWadToRay` leaves, so the round trip floors to ⌊E⌋. The k = 0
        // band is exactly [-H, H] with H = ⌊10²⁷⋅ln(2)/2⌋, matching `lnWadToRay`'s image over [1/√2,
        // √2).
        //
        // Monotonicity: one unit step in x multiplies E by exp(10⁻²⁷) ≈ 1 + 10⁻²⁷, which moves the
        // pre-floor accumulator by at least 5¹⁸⋅2¹²⁶⋅10⁻²⁷/√2 ≈ 2.3⋅10²³ grid units. The error
        // terms above confine the accumulator to a band of width 5¹⁸⋅(Δ + 67/10) ≈ 2.9⋅10¹³ grid
        // units just below E's grid image at every octave (in grid units the band is k-independent;
        // an octave seam rescales E and the band together), so the per-step gain exceeds any
        // adverse swing within the band by more than 9 orders of magnitude, and the pre-floor
        // accumulator strictly increases at every step; its floor is non-decreasing. The zeroing
        // clamp and the +1 pin at x = 0 preserve order: below C the result is 0 while just above it
        // ⌊E⌋ ≥ 0, and the adjacent runtime values around x = 0 bracket the pinned scale-point
        // value.
        assembly ("memory-safe") {
            // k = round(x / (10²⁷⋅ln(2))), half-open. CINV = round(2²⁰⁰ / (10²⁷⋅ln(2))); the +2¹⁹⁹
            // and `sar(200, …)` round to nearest with ties resolved toward +∞.
            let k := sar(0xc8, add(shl(0xc7, 0x01), mul(0x724d54edbacbebbb95c52a0f6076, x)))

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

            // Ev(v), monic, Horner down the staircase. The leading v⁵ coefficient is 1, so the
            // first stage is just an add.
            let ev := add(0xb9aacfacf3c10b378435f8e22adf48500e, v)
            ev := add(0x9a036222841f47c6ed6fc3f7602053, shr(0x95, mul(ev, v)))
            ev := add(0x9064d9657e9a21fc16bb69331c5c3057, shr(0x7b, mul(ev, v)))
            ev := add(0x93f11e650dd6c64b96ce79065cdf809e, shr(0x81, mul(ev, v)))
            ev := add(0x4e14a45e5650b506e97f4c5da23861e2, shr(0x7f, mul(ev, v)))

            // Od(v), Horner down the staircase.
            let od := 0xdc07aff8276bde9a361278df6a10
            od := add(0xc926ddbecdeeb42e68cd16db7da8c1, shr(0x7e, mul(od, v)))
            od := add(0xad4506af99be27419341e1816ff351, shr(0x84, mul(od, v)))
            od := add(0xaf566247c05753b42892f77b67a6b7c6, shr(0x7a, mul(od, v)))
            od := add(0x270a522f2b285a8374bfa62ed11c30f1, shr(0x82, mul(od, v)))

            // t⋅Od in Q87 (signed via t); the numerator Ev + t⋅Od and denominator Ev - t⋅Od are
            // both positive.
            let tod := sar(0x80, mul(t, od))

            // exp(t) in Q126: the dividend (numerator << 126) stays below 2²⁵⁵, the denominator >
            // 0.
            r := div(shl(0x7e, add(ev, tod)), sub(ev, tod))

            // E on the 2¹⁰⁸ output grid (5¹⁸ = 10¹⁸/2¹⁸ multiplies the Q126 quotient), less the
            // one-sided margin (0x37c9ed9cabf = ⌊5¹⁸⋅Δ⌋ + 1; see the budget above), then floored by
            // `shr(108 - k, …)` which folds in the 2ᵏ octave scaling and the wad unit's remaining
            // 2¹⁸ (108 - k ∈ [45, 168]).
            r := shr(sub(0x6c, k), sub(mul(0x3782dace9d9, r), 0x37c9ed9cabf))

            // Zero the result at and below C = ⌊-18⋅ln10⋅10²⁷⌋ = ⌊10²⁷⋅ln(10⁻¹⁸)⌋, the greatest x
            // with E < 1. This is the exact 0/1 output boundary, and it sits far above the inputs
            // where the reduction would overflow, so it also discards those (otherwise garbage).
            r := mul(slt(0xffffffffffffffffffffffffffffffffffffffff7a143b87dbdabf5ee0a0efd7, x), r)

            // exp(0) = 1 is the only input whose exact result is an integer; the construction lands
            // on 10¹⁸ - 1, so add one back exactly there.
            r := add(iszero(x), r)
        }
    }
}
