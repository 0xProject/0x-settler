// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;

library Ln {
    /// @notice Compute the natural logarithm of a positive fixnum with 10**18 (wad) basis,
    ///         returning the result as a fixnum with 10**27 (ray) basis.
    /// @dev Let L = 10²⁷ ⋅ ln(x / 10¹⁸) be the exact, infinite-precision result. This function
    ///      returns either ⌊L⌋ or ⌊L⌋ - 1 (equivalently, the unique integers r satisfy L - 2 < r ≤
    ///      L). It never returns a value greater than the correctly-rounded-down
    ///      result. `lnWadToRay(10**18) == 0` exactly, and the result is negative iff `x <
    ///      10**18`. `lnWadToRay` is monotonic; x1 < x2 implies lnWadToRay(x1) ≤
    ///      lnWadToRay(x2). Reverts with `Panic(18)` when `x <= 0`.
    function lnWadToRay(int256 x) internal pure returns (int256 r) {
        // Equivalent pseudocode, in exact real arithmetic:
        //     require(x > 0);
        //     k = ⌊log₂(x)⌋ - 103;                      // x = m ⋅ 2ᵏ, m in [2¹⁰³, 2¹⁰⁴)
        //     m = x / 2ᵏ;                               // Q103 fixnum in [1, 2)
        //     z = (s - m) / (m + s);                    // s = √2 ⋅ 2¹⁰³; |z| ≤ 3 - 2√2
        //     A = 2 ⋅ atanh(-z) = (p(z²) ⋅ z) / q(z²);  // ln(m / 2¹⁰³) = A + ln(s / 2¹⁰³)
        //     return ⌊10²⁷ ⋅ (A + ln(s) + k⋅ln(2) - 18⋅ln(10)) - margin⌋ + (x = 10¹⁸);
        //
        // z is negated (s - m, not m - s) so that every polynomial coefficient below can be written
        // as a positive literal; p carries the compensating negation. p/q is a (4,5)-degree
        // rational polynomial approximation of f(u) = atanh(√u)/√u on u in [0, (3-2√2)²], fit under
        // the weight √u (the weight the error carries into ln), with q monic and p(0) = q(0)
        // constrained so both polynomials share their constant-term literal. The weighted
        // sup-norm error of the integer-rounded rational 2⋅√u⋅|p/q - f|⋅10²⁷ is ≤0.325ulp.
        //
        // Mixed fixed-point bases, chosen so every renormalizing shift lands a value directly
        // at the basis its consumer needs (each runtime quantity is rounded exactly once):
        //     m:      Q103 (truncated from x; error < 2⁻¹⁰³)
        //     z:      Q100 (one sdiv)
        //     u = z²: Q96 (one `shr` by 104, straight from the Q200 product)
        //     Horner stages: a coefficient followed by j more multiplies by u tolerates a shorter
        //         basis, so the stage bases form a staircase -- p: Q68, Q80, Q86, Q93, Q94; q: Q96
        //         (the monic stage shares u's basis for free), Q87, Q85, Q93, Q94. Each literal
        //         then takes the widest basis that fits its minimal `PUSH` width. One `SAR` per
        //         multiply is forced: ray precision requires ~96 significant bits while each
        //         multiply by u consumes ~91 bits of headroom, so consecutive unrenormalized steps
        //         cannot fit in 256 bits.
        //     p, q final: Q94 (|p ⋅ z| < 2²⁰¹; both final stage shifts land there directly)
        //     p⋅z/q: one sdiv at Q100 (granularity 2⁻¹⁰⁰, ~0.0016 ulp)
        //     output: multiply by 5²⁷ = 10²⁷ / 2²⁷ places the quotient on the 10²⁷ ⋅ 2⁷² grid
        //         shared by the k⋅ln(2) term and the bias, so the closing `sar(72, …)` is the
        //         single output-rounding floor
        //
        // Error budget in ulps (1 ulp = 10⁻²⁷ of ln; 2⁷² pre-shift units): rational polynomial
        // approximation and coefficient quantization ≤0.325 combined; z, u, and `sdiv` truncations
        // ≤0.005 combined; Horner stage truncations ≤10⁻⁴; ln(2) and bias constant rounding
        // ≤10⁻¹⁹. The bias is reduced by a margin of 2.36⋅10²¹ units (0.500 ulp) > certified upward
        // error 0.329 ulp, so the Q72 accumulator never exceeds L⋅2⁷²; margin plus downward errors
        // total < 0.830 ⋅ 2⁷², so it always exceeds (L-1)⋅2⁷². `sar(72, …)` therefore yields ⌊L⌋ or
        // ⌊L⌋ - 1.
        //
        // Monotonicity: within an octave, the mantissa map m → z is antitone because
        // d/dm[(s-m)/(m+s)] = -2s/(m+s)² < 0 with |dz/dm| < 1, and the quotient p⋅z/q is an
        // antitone function of the integer z: per unit step of z it moves by at least Rₘᵢₙ -
        // zₘₐₓ⋅2J > 0.82 quotient units (R = p/-q ≥ 0.939; J bounds the truncation of R between
        // adjacent u values), and `sdiv` truncation toward zero preserves order. The x = 10¹⁸
        // correction preserves monotonicity because its neighbors' results bracket [0, 999999999].
        assembly ("memory-safe") {
            if iszero(sgt(x, 0)) {
                mstore(0x00, 0x4e487b71) // selector for `Panic(uint256)`
                mstore(0x20, 0x12)       // panic code for division by zero
                revert(0x1c, 0x24)
            }

            // ln(1) = 0 is the only input whose exact result is an integer; the floored accumulator
            // below lands on -1 for it. Adding this flag back yields the exact 0.
            let one := eq(x, 0xde0b6b3a7640000)

            // Normalize: x := m, a Q103 fixnum in [1, 2), truncated from x / 2ᵏ. Truncation
            // underestimates ln(x) by less than 2⁻¹⁰³ (only possible when k > 0).
            let c := clz(x)
            let k := sub(0x98, c)
            x := shr(0x98, shl(c, x))

            // z = (s - m)/(m + s) in Q100, truncated toward zero, where the Q103 constant s =
            // 0xb504f333f9de6484597d89b375 = round(√2 ⋅ 2¹⁰³). Centering at s makes |z| ≤ 3 - 2⋅√2
            // ≈ 0.17157 over m in [1, 2).
            let s := 0xb504f333f9de6484597d89b375
            let z := sdiv(shl(0x64, sub(s, x)), add(x, s))

            // u = z² in Q96, truncated; u in [0, 0.029438 ⋅ 2⁹⁶].
            let u := shr(0x68, mul(z, z))

            // Constant terms of p and q in Q94; p(0) = q(0) by construction, so the
            // literal is shared.
            let c0 := 0xb05a8b41cf51c04d1b8a08d465

            // Numerator p(u), Horner up the basis staircase Q68 -> Q80 -> Q86 -> Q93 -> Q94.
            // p(u)/2⁹⁴ in [663.7, 705.5] on the domain. The leading product is nonnegative, so the
            // first shift may be logical.
            let p := sub(shr(0x54, mul(0xf642b0ed5372ff45e0, u)), 0xede142e73a9acbb00e9c42)
            p := add(sar(0x5a, mul(p, u)), 0xf2a56533e74a454c9d585f70)
            p := sub(sar(0x59, mul(p, u)), 0xb44d9253cd61fb87dc7efcfbc5)
            p := add(sar(0x5f, mul(p, u)), c0)

            // Denominator q(u), monic, Horner up the staircase Q96 -> Q87 -> Q85 -> Q93 ->
            // Q94. q(u)/2⁹⁴ in [-705.5, -656.0] on the domain: bounded away from zero, and
            // p(u)/(-q(u)) in [1, 1.01].
            let q := sub(u, 0x364589193443b48661938f59da)
            q := add(sar(0x69, mul(q, u)), 0xe904c4e76307954df78feedf)
            q := sub(sar(0x62, mul(q, u)), 0xad960ab2f600bd9765c15ffd)
            q := add(sar(0x58, mul(q, u)), 0xd1b1fedec544f0ea0bc812bbbc)
            q := sub(sar(0x5f, mul(q, u)), c0)

            // A = 2⋅atanh(-z/2¹⁰⁰) in Q100: |p ⋅ z| < 2²⁰¹ and |q| > 656 ⋅ 2⁹⁴, so the quotient
            // fits in 98 bits.
            r := sdiv(mul(p, z), q)

            // Rescale to ray in Q72: 5²⁷ = 10²⁷ ⋅ 2⁷² / 2¹²⁷; exact.
            r := mul(r, 0x6765c793fa10079d)

            // Add k ⋅ round(ln(2) ⋅ 10²⁷ ⋅ 2⁷²). k is two's complement (k in [-103, 151])
            r := add(r, mul(0x23d5b9ff36551802aa5d6f9754b0f3fad83b19450, k))

            // Add floor((ln(s/2¹⁰³) + 103⋅ln(2) - 18⋅ln(10)) ⋅ 10²⁷ ⋅ 2⁷²) - 2.36 ⋅ 10²¹. The
            // subtrahend 2.36 ⋅ 10²¹ is the one-sided error margin described above.
            r := add(r, 0x61e2c6b2c35132b01ead59b21a4a764a0e2f452bd5)

            // Q72 -> integer ray result (`SAR` floors), then the x = 10¹⁸ correction.
            r := add(sar(0x48, r), one)
        }
    }

    /// @notice Compute the natural logarithm of a positive fixnum with 10**18 (wad) basis,
    ///         returning the result as a fixnum with 10**18 (wad) basis.
    /// @dev Let Lw = 10**18 * ln(x / 10**18) be the exact, infinite-precision result. This
    ///      function returns either `floor(Lw)` or `floor(Lw) - 1`. The generated-model
    ///      theorem `model_ln_wad_to_wad_floor` packages the ray-scale floor certificate
    ///      with the exact signed floor-division window by 10**9. Monotonicity is theorem
    ///      `model_ln_wad_to_wad_mono`, `lnWad(10**18) == 0` is theorem
    ///      `model_ln_wad_to_wad_one_wad`, and the sign characterization is theorem
    ///      `model_ln_wad_to_wad_negative_iff`.
    function lnWad(int256 x) internal pure returns (int256 r) {
        r = lnWadToRay(x);
        // Floor division of the ray result by 10**9 (`sdiv` alone truncates toward zero,
        // which would round negative results the wrong way). Equivalent Solidity:
        //     r = (r - (r < 0 ? 10**9 - 1 : 0)) / 10**9;
        // The subtraction cannot overflow: |r| < 2**97.
        assembly ("memory-safe") {
            r := sdiv(sub(r, mul(slt(r, 0), 0x3b9ac9ff)), 0x3b9aca00)
        }
    }
}
