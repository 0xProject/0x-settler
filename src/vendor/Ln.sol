// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;

library Ln {
    /// @notice Compute the natural logarithm of a positive fixnum with 10**18 (wad) basis,
    ///         returning the result as a fixnum with 10**27 (ray) basis.
    /// @dev Let L = 10²⁷ ⋅ ln(x / 10¹⁸) be the exact, infinite-precision result. This function
    ///      returns either ⌊L⌋ or ⌊L⌋ - 1; it never overestimates. `lnWadToRay(10**18) == 0`
    ///      exactly, and the result is negative iff `x < 10**18`. `lnWadToRay` is monotonic; x₁ <
    ///      x₂ → lnWadToRay(x₁) ≤ lnWadToRay(x₂). Reverts with `Panic(18)` when `x <= 0`.
    function lnWadToRay(int256 x) internal pure returns (int256 r) {
        // Equivalent pseudocode; fixed-point truncations are accounted for below:
        //     require(x > 0);
        //     k = ⌊log₂(x)⌋ - 95;                       // x = m ⋅ 2ᵏ, m ∈ [2⁹⁵, 2⁹⁶)
        //     m = x / 2ᵏ;                               // Q95 fixnum ∈ [1, 2)
        //     z = (s - m) / (m + s);                    // s = √2 ⋅ 2⁹⁵; |z| ≤ 3 - 2√2
        //     h = atanh(-z) = (p(z²) ⋅ z) / q(z²);      // ln(m / 2⁹⁵) = 2h + ln(s / 2⁹⁵)
        //     return ⌊10²⁷ ⋅ (2h + ln(s) + k⋅ln(2) - 18⋅ln(10)) - margin⌋ + (x = 10¹⁸);
        //
        // z is negated (s - m, not m - s) so that every polynomial coefficient below can be written
        // as a positive literal; q carries the compensating negation. p/-q is a (4,5)-degree
        // rational polynomial approximation of f(u) = atanh(√u)/√u on u ∈ [0, (3-2√2)²], fit under
        // the weight √u (the weight the error carries into ln), with q monic and p(0) = -q(0)
        // constrained so both polynomials share their constant-term literal. The weighted
        // sup-norm error of the integer-rounded rational 2⋅√u⋅|p/-q - f|⋅10²⁷ is ≤0.335ulp.
        //
        // Mixed fixed-point bases, chosen so every renormalizing shift lands a value directly
        // at the basis its consumer needs (each quantity is rounded exactly once):
        //     m:      Q95 (truncated from x; error < 2⁻⁹⁵)
        //     z:      Q100 (one sdiv)
        //     u = z²: Q96 (one `shr` by 104, straight from the Q200 product)
        //     Horner stages: a coefficient followed by j more multiplies by u tolerates a shorter
        //         basis, so the stage bases form a staircase -- p: Q68, Q72, Q78, Q85, Q94; q: Q96
        //         (the monic stage shares u's basis for free), Q71, Q77, Q85, Q94. Each literal
        //         then takes the widest basis that fits its minimal `PUSH` width. One `SAR` per
        //         multiply is forced: ray precision requires ~96 significant bits while each
        //         multiply by u consumes ~91 bits of headroom, so consecutive unrenormalized steps
        //         cannot fit in 256 bits.
        //     p, q final: Q94 (|p ⋅ z| < 2²⁰¹; both final stage shifts land there directly)
        //     p⋅z/q: one `SDIV` at Q100 (granularity 2⁻¹⁰⁰, ~0.0016 ulp)
        //     output: the quotient is h in Q100; multiplying by 5²⁷ = 2⋅10²⁷⋅2⁷² / 2¹⁰⁰ folds in
        //         the factor of 2 and places it on the 10²⁷ ⋅ 2⁷² grid shared by the k⋅ln(2) term
        //         and the bias, so the closing `sar(72, …)` is the single output-rounding floor
        //
        // Error budget in ulps (1 ulp = 10⁻²⁷ of ln; 2⁷² pre-shift units): rational polynomial
        // approximation and coefficient quantization ≤0.335 combined; mantissa (Q95) truncation
        // ≤2⁻⁹⁵⋅10²⁷ ≈ 0.026 (downward only); z, u, and `sdiv` truncations ≤0.005 combined; Horner
        // stage truncations ≤10⁻⁴; ln(2) and bias constant rounding ≤10⁻¹⁹. The bias is reduced by a
        // margin of ~1.607⋅10²¹ units (0.3403 ulp), so the Q72 accumulator never exceeds L⋅2⁷²;
        // margin plus downward errors total < 0.706 ⋅ 2⁷², so it always exceeds (L-1)⋅2⁷².
        // `sar(72, …)` therefore yields ⌊L⌋ or ⌊L⌋ - 1.
        //
        // Monotonicity: within an octave, the integer z = sdiv((s-m)⋅2¹⁰⁰, m+s) is strictly
        // decreasing in m -- ∂/∂m⋅[(s-m)/(m+s)⋅2¹⁰⁰] = -2s⋅2¹⁰⁰/(m+s)² ∈ [-16, -8] over the octave,
        // so each unit step of m lowers z by 8 to 16 (and `sdiv`, monotone, never reverses that).
        // The quotient p⋅z/q is an antitone function of the integer z: per unit step of z it moves
        // by at least Rₘᵢₙ - zₘₐₓ⋅2J > 0.82 quotient units (R = p/-q ≥ 0.939; J bounds the truncation
        // of R between adjacent u values), so it is antitone across each m-step's multi-unit z
        // decrease, and `SDIV` truncation toward zero preserves order. The x = 10¹⁸ correction
        // preserves monotonicity because its neighbors' results bracket [0, 999999999].
        assembly ("memory-safe") {
            if iszero(slt(0x00, x)) {
                mstore(0x00, 0x4e487b71) // selector for `Panic(uint256)`
                mstore(0x20, 0x12)       // panic code for division by zero
                revert(0x1c, 0x24)
            }

            // lnWadToRay(1⋅10¹⁸) = 0 is the only input whose exact result is an integer; the
            // floored accumulator below lands on -1 for it. Adding this flag back yields the exact
            // 0.
            let one := eq(0xde0b6b3a7640000, x)

            // Normalize: x := m, a Q95 fixnum, m ∈ [1, 2), truncated from x / 2ᵏ. Truncation
            // underestimates ln(x) by less than 2⁻⁹⁵ (only possible when k > 0).
            let c := clz(x)
            let k := sub(0xa0, c)
            x := shr(0xa0, shl(c, x))

            // z = (s - m)/(m + s) in Q100, truncated toward zero, where the Q95 constant s =
            // 0xb504f333f9de6484597d89b3 = round(√2 ⋅ 2⁹⁵). Centering at s makes |z| ≤ 3 - 2⋅√2
            // ≈ 0.17157 over m ∈ [1, 2).
            let s := 0xb504f333f9de6484597d89b3
            let z := sdiv(shl(0x64, sub(s, x)), add(x, s))

            // u = z² in Q96, truncated; u ∈ [0, 0.029438 ⋅ 2⁹⁶].
            let u := shr(0x68, mul(z, z))

            // Constant terms of p and q in Q94; p(0) = -q(0) by construction, so the
            // literal is shared.
            let c0 := 0xb05a8b41cf51c04d1b8a08d465

            // Numerator p(u), Horner up the basis staircase Q68 → Q72 → Q78 → Q85 → Q94. p(u)/2⁹⁴ ∈
            // [663.7, 705.5] on the domain. The leading product is nonnegative, so the first shift
            // may be logical.
            let p := sub(shr(0x5c, mul(0xf642b0ed5372ff45e0, u)), 0xede142e73a9acbb00e9c)
            p := add(sar(0x5a, mul(p, u)), 0xf2a56533e74a454c9d585f)
            p := sub(sar(0x59, mul(p, u)), 0xb44d9253cd61fb87dc7efcfc)
            p := add(sar(0x57, mul(p, u)), c0)

            // Denominator q(u), monic, Horner up the staircase Q96 → Q71 → Q77 → Q85 →
            // Q94. q(u)/2⁹⁴ ∈ [-705.5, -656.0] on the domain: bounded away from zero, and
            // p(u)/-q(u) ∈ [1, 1.01].
            let q := sub(u, 0x364589193443b48661938f59da)
            q := add(sar(0x79, mul(q, u)), 0xe904c4e76307954df790)
            q := sub(sar(0x5a, mul(q, u)), 0xad960ab2f600bd9765c160)
            q := add(sar(0x58, mul(q, u)), 0xd1b1fedec544f0ea0bc812bc)
            q := sub(sar(0x57, mul(q, u)), c0)

            // h = atanh(-z/2¹⁰⁰) in Q100: |p ⋅ z| < 2²⁰¹ ∧ |q| > 656 ⋅ 2⁹⁴, so the quotient fits in
            // 98 bits.
            r := sdiv(mul(p, z), q)

            // Double h and rescale to ray in Q72: 5²⁷ = 2 ⋅ 10²⁷ ⋅ 2⁷² / 2¹⁰⁰; exact.
            r := mul(0x6765c793fa10079d, r)

            // Add k ⋅ round(ln(2) ⋅ 10²⁷ ⋅ 2⁷²). k is two's complement (k ∈ [-95, 159])
            r := add(mul(0x23d5b9ff36551802aa5d6f9754b0f3fad83b19450, k), r)

            // Add ⌊(ln(s/2⁹⁵) + 95⋅ln(2) - 18⋅ln(10)) ⋅ 10²⁷ ⋅ 2⁷²⌋ minus the one-sided error
            // margin described above.
            r := add(0x4ff7e9b32826a6aec97ea1e696bd71eb764c77277c, r)

            // Q72 → integer ray result (`SAR` floors), then the x = 10¹⁸ correction.
            r := add(sar(0x48, r), one)
        }
    }

    /// @notice Compute the natural logarithm of a positive fixnum with 10**18 (wad) basis,
    ///         returning the result as a fixnum with 10**18 (wad) basis.
    /// @dev Let Lw = 10¹⁸ * ln(x / 10¹⁸) be the exact, infinite-precision result. This function
    ///      returns either `⌊Lw⌋` or `⌊Lw⌋ - 1`. Like `lnWadToRay`, `lnWad(10**18) == 0` exactly,
    ///      and `lnWad` is monotonic.
    function lnWad(int256 x) internal pure returns (int256 r) {
        r = lnWadToRay(x);
        // Floor division of the ray result by 10⁹. `SDIV` alone truncates toward zero, which would
        // round negative results the wrong way. Equivalent Solidity:
        //     r = (r - (r < 0 ? 10**9 - 1 : 0)) / 10**9;
        // The subtraction cannot overflow: |r| < 2⁹⁷.
        assembly ("memory-safe") {
            r := sdiv(sub(r, mul(0x3b9ac9ff, sgt(0x00, r))), 0x3b9aca00)
        }
    }
}
