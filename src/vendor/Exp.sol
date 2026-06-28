// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;

import {Panic} from "../utils/Panic.sol";

library Exp {
    /// @notice Compute the natural exponential of a fixnum with 10**27 (ray) basis, returning the
    ///         result as a fixnum with 10**18 (wad) basis. The inverse of `Ln.lnWadToRay`.
    /// @dev Let E = 10¹⁸ ⋅ exp(x / 10²⁷) be the exact, infinite-precision result. This function
    ///      returns either ⌊E⌋ or ⌊E⌋ - 1; it never overestimates. `expRayToWad(0) == 10**18`
    ///      exactly, and the result is never negative. The function is monotonic; x₁ < x₂ →
    ///      expRayToWad(x₁) ≤ expRayToWad(x₂). On the central octave it is tight (returns exactly
    ///      ⌊E⌋): for w with w / 10¹⁸ ∈ [1/√2, √2), `expRayToWad(lnWadToRay(w)) == w - 1` (and
    ///      `== w` at the scale point w = 10¹⁸), so a consumer constrained to that regime recovers
    ///      `w` by adding one. Reverts with `Panic(17)` when x is large enough to leave the
    ///      supported range (x ≥ 0x8e383a2cdfa1b74a9422d2e1 ≈ 44.01 ⋅ 10²⁷, i.e. E ≳ 1.30 ⋅ 10³⁷).
    function expRayToWad(int256 x) internal pure returns (int256 r) {
        // At this input the octave count k = round(x / (10²⁷⋅ln2)) reaches 64, where the margin
        // (which scales as 2ᵏ⁻⁶³ of its k = 63 value) exceeds one ulp and the floor can fall two
        // below E.
        if (x >= 0x8e383a2cdfa1b74a9422d2e1) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
        r = _expRayToWad(x);
    }

    /// @dev The supported-range kernel. Equivalent pseudocode; fixed-point truncations are
    ///      accounted for below:
    ///          k = round(x / (10²⁷⋅ln2));                        // x = (k⋅ln2 + t)⋅10²⁷, |t| ≤ ln2/2
    ///          t = x/10²⁷ - k⋅ln2;                               // reduced argument
    ///          e = (Ev(t²) + t⋅Od(t²)) / (Ev(t²) - t⋅Od(t²));    // ≈ exp(t)
    ///          r = ⌊(10¹⁸⋅e)⋅2ᵏ - margin⌋;
    ///          r = r ⋅ (x > C);                                  // C = ⌊-18⋅ln10⋅10²⁷⌋; 0 where E < 1
    ///          return r + (x == 0);                              // pin exp(0) = 10¹⁸ exactly
    ///
    ///      `exp(t) = (1 + tanh(t/2)) / (1 - tanh(t/2))`, so with the even/odd split
    ///      N(t) = Ev(t²) + t⋅Od(t²) the quotient N(t)/N(-t) is the reciprocal-symmetric rational
    ///      that matches `Od/Ev` to `tanh(√v/2)/√v` on v = t² ∈ [0, (ln2/2)²]. Ev is degree 5 and
    ///      Od degree 4; in exact arithmetic this (4,5) form approximates exp to ≈135 bits, and the
    ///      integer coefficients realize ≈126 of them (the Q126 quotient). Ev is monic, so its
    ///      leading stage is a shift, not a multiply.
    ///
    ///      Mixed fixed-point bases (a staircase): every quantity is rounded exactly once, and each
    ///      coefficient takes the widest basis fitting its minimal byte width, so a coefficient
    ///      followed by j more multiplies by v tolerates a shorter basis.
    ///          t:      Q128 (one `sar` from the Q235 reduction K27⋅x - k⋅LN2; |t| ≤ ln2/2)
    ///          v = t²: Q128 (one `shr` by 128 from the Q256 product)
    ///          Ev Horner up the staircase Q99 → Q97 → Q97 → Q91 → Q87 (monic leading stage at Q99)
    ///          Od Horner up the staircase Q105 → Q102 → Q93 → Q94 → Q87
    ///          Ev, Od, t⋅Od, and the numerator/denominator: Q87 (the basis the closing quotient shares)
    ///          quotient: one `sdiv` placing exp(t) at Q126 (the dividend, numerator << 126, < 2²⁵⁶)
    ///          output: multiplying by 10¹⁸ lands E on the 10¹⁸⋅2¹²⁶ grid; the closing
    ///              `sar(126 - k, …)` is the single output-rounding floor, with 2ᵏ folded in
    ///
    ///      Error budget in output ulp (1 ulp = 10⁻¹⁸ of the result). Writing the margin-free
    ///      accumulator's excess over E as RAW = 10¹⁸⋅e⋅2ᵏ - E, the rational and `sdiv` terms grow
    ///      as 2ᵏ, so RAW peaks at the supported edge k = 63. Bounding each source there:
    ///          reduction:  ln2 is carried at Q235, so the under-subtraction of k⋅ln2 lifts the
    ///              accumulator by ≤ 2.32⋅10⁻⁶ ulp (negligible).
    ///          real-coefficient rational approximation + coefficient quantization (smooth), and the
    ///              integer Horner + closing `sdiv` truncation: a one-sided envelope. The Ev shared
    ///              by the numerator Ev + t⋅Od and denominator Ev - t⋅Od cancels at leading order, so
    ///              its truncation barely perturbs the quotient; together these stay ≤ 0.0859 ulp.
    ///      Hence RAW ≤ S, with the proven bound S = 0.0858862987232991853 ulp. The margin is the
    ///      least integer that covers S once placed in the Q126 grid: 0xafe527e18748a8a = ⌈2⁶³⋅S⌉
    ///      (worth ≈ S ulp at k = 63). So 10¹⁸⋅e⋅2ᵏ - margin ≤ E (never overestimates), and
    ///      E - A ≤ margin - min RAW ≤ 0.6057 < 1, so the floor is ⌊E⌋ or ⌊E⌋ - 1. At k = 64 the
    ///      margin exceeds one ulp and the floor can fall two below E, so that input is reverted. On
    ///      the central octave k = 0 the margin is ⌈2⁶³⋅S⌉⋅2⁻¹²⁶ ≈ 9.3⋅10⁻²¹ ulp, far below the
    ///      ≈10⁻⁹ ulp gap `lnWadToRay` leaves, so the round trip floors to ⌊E⌋. `round(x/(10²⁷⋅ln2))`
    ///      is half-open, so the k = 0 band is exactly [-H, H) with H = ⌊10²⁷⋅ln2/2⌋, matching
    ///      `lnWadToRay`'s image over [1/√2, √2).
    ///
    ///      Monotonicity: one unit step in x multiplies E by exp(10⁻²⁷) ≈ 1 + 10⁻²⁷, a relative
    ///      gain that exceeds the entire error span above (≤ S ≈ 7⋅10⁻³⁹ relative at k = 63, and
    ///      ∝ 2ᵏ below it) and its per-step variation — including the margin's doubling at each
    ///      octave boundary (≤ ⌈2⁶³⋅S⌉⋅2ᵏ⁻¹²⁶ ≈ 7⋅10⁻³⁹ relative) — by more than nine orders of
    ///      magnitude, so the pre-floor accumulator strictly increases at every step and its floor
    ///      is non-decreasing. The zeroing clamp and the +1 pin preserve order: below C the result
    ///      is 0 while just above it ⌊E⌋ ≥ 0, and at x = 0 the exact-on-central neighbours bracket
    ///      the pinned value (⌊E(-1)⌋ = 10¹⁸ - 1 ≤ 10¹⁸ ≤ ⌊E(1)⌋ = 10¹⁸).
    function _expRayToWad(int256 x) private pure returns (int256 r) {
        assembly ("memory-safe") {
            // k = round(x / (10²⁷⋅ln2)), half-open. CINV = round(2²⁰⁰ / (10²⁷⋅ln2)); the +2¹⁹⁹
            // and `sar(200, …)` round to nearest with ties resolved toward +∞.
            let k := sar(0xc8, add(shl(0xc7, 0x01), mul(0x724d54edbacbebbb95c52a0f6076, x)))

            // t in Q128. K27 = round(2²³⁵ / 10²⁷) and LN2 = round(ln2 ⋅ 2²³⁵). Subtracting k ⋅ LN2
            // from K27 ⋅ x at the Q235 product basis (so the k ⋅ ln2 rounding error is ~2⁻²³⁵, far
            // below an output ulp) then one `sar(107, …)` leaves the reduced argument at Q128.
            // Carrying ln2 in a single wide word matches the op count of a Q128 reduction.
            let t :=
                sar(
                    0x6b,
                    sub(
                        mul(0x279d346de4781f921dd7a89933d54d1f72928, x),
                        mul(0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d, k)
                    )
                )

            // v = t² in Q128 (nonnegative; logical shift).
            let v := shr(0x80, mul(t, t))

            // Ev(v), monic, Horner up the staircase. The leading v⁵ coefficient is one, so the
            // first stage is a shift and an add, not a multiply. Both polynomials carry a common
            // scaling (the reciprocal of Ev's pre-normalization leading coefficient) that makes Ev
            // monic and cancels in the quotient below.
            let ev := add(0xb9aacfad41060587203a79af0ebc, shr(0x1d, v))
            ev := add(0x9a036222e11aee18465042f8ea64c8, shr(0x82, mul(ev, v)))
            ev := add(0x9064d965e1c4863b73604e0ddbec53f9, shr(0x80, mul(ev, v)))
            ev := add(0x93f11e65781741b92fa7fc4f4fffcca2, shr(0x86, mul(ev, v)))
            ev := add(0x4e14a45e8ec305e233e11b4174e214ac, shr(0x84, mul(ev, v)))

            // Od(v), Horner up the staircase.
            let od := 0xdc07aff85e5bb5629d0fb64a84bb
            od := add(0xc926ddbf3830ca5561cc01585402d0, shr(0x83, mul(od, v)))
            od := add(0xad4506b00b1246c7e5b4fd33e1201b, shr(0x89, mul(od, v)))
            od := add(0xaf5662483c4ce783a9ef5fe025f42e9e, shr(0x7f, mul(od, v)))
            od := add(0x270a522f476182f119f08da0ba710a56, shr(0x87, mul(od, v)))

            // t⋅Od in Q87 (signed via t); the numerator Ev + t⋅Od and denominator Ev - t⋅Od are
            // both positive.
            let tod := sar(0x80, mul(t, od))

            // exp(t) in Q126: the dividend (numerator << 126) stays below 2²⁵⁶, the denominator > 0.
            r := sdiv(shl(0x7e, add(ev, tod)), sub(ev, tod))

            // E in Q126 on the 10¹⁸⋅2¹²⁶ grid, less the one-sided margin (the provable minimum
            // 0xafe527e18748a8a = ⌈2⁶³⋅S⌉; see the budget above), then floored by `sar(126 - k, …)`
            // which folds in the 2ᵏ octave scaling (126 - k ∈ [64, 188]).
            r := sar(sub(0x7e, k), sub(mul(0xde0b6b3a7640000, r), 0xafe527e18748a8a))

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
