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
        // At this input the octave count k = round(x / (10²⁷⋅ln2)) reaches 64. The error in
        // `_expRayToWad` exceeds 1ulp at that scale.
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
    ///      `exp(t) = (1 + tanh(t/2)) / (1 - tanh(t/2))`, so with the even/odd split N(t) = Ev(t²)
    ///      + t⋅Od(t²) the quotient N(t)/N(-t) is the reciprocal-symmetric rational that matches
    ///      `Od/Ev` to `tanh(√v/2)/√v` on v = t² ∈ [0, (ln2/2)²]. Ev is degree 5 and Od degree 4;
    ///      in exact arithmetic this (4,5) form approximates exp to ≈135 bits, and the integer
    ///      coefficients realize ≈126 of them (the Q126 quotient). Ev is monic, so its leading
    ///      stage is a shift, not a multiply.
    ///
    ///      Mixed fixed-point bases (a staircase): every quantity is rounded exactly once, and each
    ///      coefficient takes the widest basis fitting its chosen byte width, so a coefficient
    ///      followed by j more multiplies by v tolerates a shorter basis.
    ///          t:      Q128 (one `sar` from the Q235 reduction K27⋅x - k⋅LN2; |t| ≤ ln2/2)
    ///          v = t²: Q128 (one `shr` by 128 from the Q256 product)
    ///          Ev Horner up the staircase Q99 → Q97 → Q97 → Q91 → Q87 (monic leading stage at Q99)
    ///          Od Horner up the staircase Q105 → Q102 → Q93 → Q94 → Q87
    ///          Ev, Od, t⋅Od, and the numerator/denominator: Q87 (the basis the closing quotient
    ///              shares)
    ///          quotient: one `sdiv` placing exp(t) at Q126 (the dividend, numerator << 126, stays
    ///              below 2²⁵⁵: a nonnegative signed word)
    ///          output: multiplying by 10¹⁸ lands E on the 10¹⁸⋅2¹²⁶ grid; the closing
    ///              `sar(126 - k, …)` is the single output-rounding floor, with 2ᵏ folded in
    ///
    ///      Error budget. The integer rational `e` lands on the Q126 grid; write its excess over
    ///      the exact quotient as Δ = (e - exp(t))⋅2¹²⁶ (in Q126 units, one unit = 2⁻¹²⁶). Δ is the
    ///      tightest bound the proof technique can bear, in spite of the fact that the worst-case
    ///      error contributions do not co-occur. The proof bounds Δ ≤ 0.7201434073703092789, the
    ///      sum of three one-sided contributions:
    ///          integer Horner + closing `sdiv` truncation: the Ev shared by the numerator Ev +
    ///              t⋅Od and denominator Ev - t⋅Od cancels to first order in the quotient, so its
    ///              truncation barely perturbs e; this jitter (the dominant term) stays <
    ///              0.62071.
    ///          rational `Mp`-factor (the dyadic gap between the reciprocal-symmetric form and
    ///              exp): < 0.08839 (its supremum is √2⋅2¹²⁶/(2¹³⁰-1)).
    ///          reduced-argument gap: the Q128 floor of t only pushes e downward (that direction is
    ///              budgeted on the under side); the over side is the K27/LN2 constant-grid residue
    ///              (the k⋅ln2 grid error stays below 2⁻²²⁹), which the proof envelopes one-sidedly
    ///              at 2⁻¹³³ of reduced argument, lifting e by < 0.01105 (√2⋅2¹²⁶/(32⋅2¹²⁸) =
    ///              √2/128).
    ///      Scaling by 10¹⁸⋅2ᵏ, the accumulator's excess over E peaks at the supported edge k = 63
    ///      at S = 10¹⁸⋅Δ/2⁶³ ≈ 0.0781 ulp (1 ulp = 10⁻¹⁸ of the result). The margin is the least
    ///      integer strictly above 2⁶³⋅S: 0x9fe769d0fa58e9f = ⌊10¹⁸⋅Δ⌋ + 1 = 720143407370309279
    ///      (worth ≈ S ulp at k = 63; the +1 makes the never-over strict, which the round trip
    ///      below needs). So 10¹⁸⋅e⋅2ᵏ - margin ≤ E (never overestimates). The under side is
    ///      bounded to the same precision: e⋅2¹²⁶ ≥ exp(t)⋅2¹²⁶ - 13/2, where 13/2 is the proven
    ///      sum of the integer-rational deficit (≤ 6001/1000, the Horner/`sdiv`/floor truncation
    ///      against the denominator), the `Mp` factor (≤ 1/10, via e ≤ 1.45·2¹²⁶), and the
    ///      under-direction reduced-argument gap (≤ 37/100, via exp(t) ≤ √2). Hence the maximum
    ///      underestimation of the pre-floor accumulator A is E - A ≤ ((13/2)⋅10¹⁸ + margin)/2⁶³ ≈
    ///      0.78281 < 1, so the floor returns ⌊E⌋ or ⌊E⌋ - 1. The deficit envelope ((13/2)⋅10¹⁸ +
    ///      margin)/2^(126 - k) doubles each octave, so at k = 64 it exceeds 1ulp. On the central
    ///      octave k = 0 the margin is margin⋅2⁻¹²⁶ ≈ 8.5⋅10⁻²¹ ulp, far below the ≈10⁻⁹ ulp gap
    ///      `lnWadToRay` leaves, so the round trip floors to ⌊E⌋. `round(x/(10²⁷⋅ln2))` is
    ///      half-open, so the k = 0 band is exactly [-H, H] with H = ⌊10²⁷⋅ln2/2⌋, matching
    ///      `lnWadToRay`'s image over [1/√2, √2).
    ///
    ///      Monotonicity: one unit step in x multiplies E by exp(10⁻²⁷) ≈ 1 + 10⁻²⁷, which moves
    ///      the pre-floor accumulator by at least 10¹⁸⋅2¹²⁶⋅10⁻²⁷/√2 ≈ 6⋅10²⁸ grid units. The error
    ///      terms above confine the accumulator to a band of width 10¹⁸⋅(Δ + 13/2) ≈ 7.2⋅10¹⁸ grid
    ///      units just below E's grid image at every octave (in grid units the band is
    ///      k-independent; an octave seam rescales E and the band together), so the per-step gain
    ///      exceeds any adverse swing within the band by more than nine orders of magnitude, and
    ///      the pre-floor accumulator strictly increases at every step; its floor is
    ///      non-decreasing. The zeroing clamp and the +1 pin preserve order: below C the result is
    ///      0 while just above it ⌊E⌋ ≥ 0, and the adjacent runtime values around x = 0 bracket the
    ///      pinned scale-point value.
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

            // exp(t) in Q126: the dividend (numerator << 126) stays below 2²⁵⁵, the denominator > 0.
            r := sdiv(shl(0x7e, add(ev, tod)), sub(ev, tod))

            // E in Q126 on the 10¹⁸⋅2¹²⁶ grid, less the one-sided margin (the provable minimum
            // 0x9fe769d0fa58e9f = ⌊10¹⁸⋅Δ⌋ + 1; see the budget above), then floored by `sar(126 - k, …)`
            // which folds in the 2ᵏ octave scaling (126 - k ∈ [63, 186]).
            r := sar(sub(0x7e, k), sub(mul(0xde0b6b3a7640000, r), 0x9fe769d0fa58e9f))

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
