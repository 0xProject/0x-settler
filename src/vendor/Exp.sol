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
    ///      supported range (x ≥ 0x8e383a2cdfa1b74a9422d2e1 ≈ 44.01 ⋅ 10²⁷, i.e. E ≳ 1.30 ⋅ 10¹⁹).
    function expRayToWad(int256 x) internal pure returns (int256 r) {
        // At this input the octave count k = round(x / (10²⁷⋅ln2)) reaches 64, where the margin
        // (which scales as 2ᵏ⁻⁶⁴ ulp) reaches one and the floor can fall two below E.
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
    ///      Od degree 4 (a (4,5) form, ≈135 bits); Ev is monic so its leading stage is a shift, not
    ///      a multiply. The relative error of the integer-rounded rational dwarfs the ≈2⁻⁶⁶ headroom
    ///      that flooring leaves on the central octave, so the round-trip with `lnWadToRay` lands
    ///      exactly one below the input there.
    ///
    ///      Mixed fixed-point bases (a staircase): every quantity is rounded exactly once, and each
    ///      coefficient takes the widest basis fitting its minimal byte width, so a coefficient
    ///      followed by j more multiplies by v tolerates a shorter basis.
    ///          t:      Q128 (one sdiv-free reduction; |t| ≤ ln2/2)
    ///          v = t²: Q128 (one `shr` by 128 from the Q256 product)
    ///          Ev Horner up the staircase Q99 → Q97 → Q97 → Q91 → Q87 (monic leading stage at Q99)
    ///          Od Horner up the staircase Q105 → Q102 → Q93 → Q94 → Q87
    ///          Ev, Od, t⋅Od, Num, Den final: Q87 (the basis shared by the closing quotient)
    ///          quotient: one `sdiv` placing exp(t) at Q126 (the dividend `Num << 126` < 2²⁵⁶)
    ///          output: multiplying by 10¹⁸ lands E on the 10¹⁸⋅2¹²⁶ grid; the closing
    ///              `sar(126 - k, …)` is the single output-rounding floor, with 2ᵏ folded in
    ///
    ///      The margin (2⁶²) is subtracted in the Q126 output grid so the accumulator never exceeds
    ///      E⋅2¹²⁶; margin plus the downward errors stay below one ulp on the central octave, so the
    ///      floor there is exactly ⌊E⌋, and below two ulps everywhere, so elsewhere it is ⌊E⌋ or
    ///      ⌊E⌋ - 1. `round(x / (10²⁷⋅ln2))` is computed half-open so the k = 0 band is exactly
    ///      [-H, H) with H = ⌊10²⁷⋅ln2/2⌋, matching the image of `lnWadToRay` over [1/√2, √2).
    function _expRayToWad(int256 x) private pure returns (int256 r) {
        assembly ("memory-safe") {
            // k = round(x / (10²⁷⋅ln2)), half-open. CINV = round(2²⁰⁰ / (10²⁷⋅ln2)); the +2¹⁹⁹
            // and `sar(200, …)` round to nearest with ties resolved toward +∞.
            let k := sar(0xc8, add(shl(0xc7, 0x01), mul(0x724d54edbacbebbb95c52a0f6076, x)))

            // t in Q128. K27 = round(2²³⁵ / 10²⁷) places x/10²⁷ at Q135; subtracting
            // k ⋅ round(ln2 ⋅ 2¹³⁵) leaves t at Q135 (the wider ln2 basis keeps k⋅ln2 exact),
            // then `sar(7, …)` drops it to the Q128 working basis.
            let t :=
                sar(
                    0x07,
                    sub(
                        sar(0x64, mul(0x279d346de4781f921dd7a89933d54d1f72928, x)),
                        mul(0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a0, k)
                    )
                )

            // v = t² in Q128 (nonnegative; logical shift).
            let v := shr(0x80, mul(t, t))

            // Ev(v), monic, Horner up the staircase. The leading v⁵ coefficient is one, so the
            // first stage `(v >> 29) + a4` is a shift and an add. Coefficients are scaled by
            // 1/e5 (shared with Od) so the quotient below is unaffected.
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

            // t⋅Od in Q87 (signed via t). Num = Ev + t⋅Od, Den = Ev - t⋅Od, both positive.
            let tod := sar(0x80, mul(t, od))

            // exp(t) in Q126: |Num ⋅ 2¹²⁶| < 2²⁵⁶ ∧ Den > 0.
            r := sdiv(shl(0x7e, add(ev, tod)), sub(ev, tod))

            // E in Q126 on the 10¹⁸⋅2¹²⁶ grid, less the one-sided margin, then floored by
            // `sar(126 - k, …)` which folds in the 2ᵏ octave scaling (126 - k ∈ [64, 188]).
            r := sar(sub(0x7e, k), sub(mul(0xde0b6b3a7640000, r), 0x4000000000000000))

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
