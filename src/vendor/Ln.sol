// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;

library Ln {
    /// @notice Compute the natural logarithm of a positive fixnum with 10**18 (wad) basis,
    ///         returning the result as a fixnum with 10**27 (ray) basis.
    /// @dev Let L = 10**27 * ln(x / 10**18) be the exact, infinite-precision result. This
    ///      function returns either `floor(L)` or `floor(L) - 1` (equivalently, the unique
    ///      integers r satisfy L - 2 < r <= L). It never returns a value greater than the
    ///      correctly-rounded-down result. `lnWad(10**18) == 0` exactly, and the result is
    ///      negative iff `x < 10**18`. Both properties are proven in Lean over the
    ///      generated model (formal/ln/LnProof): the floor specification
    ///      `r <= L < r + 2` is theorem `model_ln_wad_floor` (arithmetized through
    ///      integer-scaled partial sums of the exponential, standard axioms only), and
    ///      monotonicity — `x1 < x2` implies `lnWad(x1) <= lnWad(x2)`, via the analytic
    ///      within-octave leg plus the finite leg covering the 254 clz seams and the
    ///      corrected point `x = 10**18` — is theorem `model_ln_wad_mono`, with an
    ///      executable exact-rational counterpart in formal/python/ln/check_ln_monotone.py.
    ///      Reverts with `LnWadUndefined()` when `x <= 0`.
    function lnWad(int256 x) internal pure returns (int256 r) {
        // Assembly is required for `clz`, wrapping arithmetic on 256-bit fixnums, and the
        // truncating `sar`/`sdiv` primitives whose rounding directions the error analysis
        // below depends on. Equivalent pseudocode, in exact real arithmetic:
        //     require(x > 0);
        //     k = floor(log2(x)) - 103;                  // x = m * 2**k, m in [2**103, 2**104)
        //     m = x / 2**k;                              // Q103 fixnum in [1, 2)
        //     z = (s - m) / (m + s);                     // s = sqrt(2) * 2**103; |z| <= 3 - 2*sqrt(2)
        //     A = 2 * atanh(-z) = (p(z**2) * z) / q(z**2);  // ln(m / 2**103) = A + ln(s / 2**103)
        //     return floor(10**27 * (A + ln(s) + k*ln(2) - 18*ln(10)) - margin) + (x == 10**18);
        //
        // z is negated (s - m, not m - s) so that every polynomial coefficient below can be
        // written as a positive literal; p carries the compensating negation. p/q is a
        // (4,5)-degree rational minimax approximation of f(u) = atanh(sqrt(u))/sqrt(u) on
        // u in [0, (3-2*sqrt(2))**2], fit under the weight sqrt(u) (the weight the error
        // carries into ln), with q monic and p(0) = q(0) constrained so both polynomials
        // share their constant-term literal. Certified weighted sup-norm error of the
        // integer-rounded rational: 2*sqrt(u)*|p/q - f| * 10**27 <= 0.325 ulp.
        //
        // Mixed fixed-point bases, chosen so every renormalizing shift lands a value directly
        // at the basis its consumer needs (each runtime quantity is rounded exactly once):
        //     m:      Q103 (truncated from x; error < 2**-103)
        //     z:      Q100 (one sdiv)
        //     u = z**2: Q96 (one shr by 104, straight from the Q200 product)
        //     Horner stages: a coefficient followed by j more multiplies by u tolerates a
        //         shorter basis, so the stage bases form a staircase -- p: Q68, Q80, Q86,
        //         Q93, Q94; q: Q96 (the monic stage shares u's basis for free), Q87, Q85,
        //         Q93, Q94 -- where each stage basis is floored by the monotonicity
        //         certificate (a truncation at basis b followed by j multiplies perturbs the
        //         final Q94 polynomial by < 2**(94-b) * u_max**j, and the sum of these slops
        //         must stay well below one quotient unit; see
        //         formal/python/ln/check_ln_monotone.py) and each literal then takes the
        //         widest basis that fits its minimal PUSH width. One sar per multiply is
        //         forced: ray precision requires ~96 significant bits while each multiply by
        //         u consumes ~91 bits of headroom, so consecutive unrenormalized steps cannot
        //         fit in 256 bits.
        //     p, q final: Q94 (|p * z| < 2**201; both final stage shifts land there directly)
        //     p*z/q: one sdiv at Q100 (granularity 2**-100, ~0.0016 ulp)
        //     output: multiply by 5**27 = 10**27 / 2**27 -- exact, no rounding -- places the
        //         quotient on the 10**27 * 2**72 grid shared by the k*ln(2) term and the
        //         bias, so the closing `sar(72)` is the single output-rounding floor
        //
        // Error budget in ulps (1 ulp = 1e-27 of ln, = 2**72 pre-shift units): minimax and
        // coefficient quantization (certified together) <= 0.325; z, u, and sdiv truncations
        // <= 0.005 combined; Horner stage truncations <= 1e-4; ln(2) and bias constant
        // rounding <= 1e-19. The bias is reduced by a margin of 2.36e21 units (0.500 ulp)
        // > certified upward error 0.329 ulp, so the Q72 accumulator never exceeds L*2**72;
        // margin plus downward errors total < 0.830 * 2**72, so it always exceeds
        // (L-1)*2**72. `sar(72, .)` therefore yields floor(L) or floor(L) - 1.
        //
        // Monotonicity: within an octave (fixed clz), the mantissa map m -> z is antitone
        // because d/dm[(s-m)/(m+s)] = -2s/(m+s)**2 < 0 with |dz/dm| < 1, and the quotient
        // p*z/q is an antitone function of the integer z: per unit step of z it moves by at
        // least R_min - z_max*2J > 0.82 quotient units (R = p/-q >= 0.939 certified; J
        // bounds the truncation jitter of R between adjacent u values), and `sdiv`
        // truncation toward zero preserves order. Octave seams reduce to the 254 adjacent
        // pairs (2**t - 1, 2**t), each verified exactly (the rational's error at u_max is
        // certified negative, giving ~0.32 ulp of seam slack). The x == 10**18 correction
        // below preserves monotonicity because its neighbors' results bracket [0, 999999999].
        assembly ("memory-safe") {
            if iszero(sgt(x, 0)) {
                mstore(0x00, 0x1615e638) // `LnWadUndefined()`.
                revert(0x1c, 0x04)
            }

            // ln(10**18 / 10**18) = 0 is the only input whose exact result is an integer;
            // the floored accumulator below lands on -1 for it (pinned by test and by the
            // Lean model theorem `model_ln_wad_one_wad`). Adding this flag back yields
            // the exact 0, branchlessly. Recorded before `x` is clobbered.
            let one := eq(x, 0xde0b6b3a7640000)

            // Normalize: x := m, a Q103 fixnum in [1, 2), truncated from x / 2**k. Truncation
            // underestimates ln(x) by less than 2**-103 (only possible when k > 0).
            let c := clz(x)
            let k := sub(0x98, c)
            x := shr(0x98, shl(c, x))

            // z = (s - m)/(m + s) in Q100, truncated toward zero, where the Q103 constant
            // s = 0xb504f333f9de6484597d89b375 = round(sqrt(2) * 2**103). Centering at s
            // makes |z| <= 3 - 2*sqrt(2) ~= 0.17157 over m in [1, 2).
            let s := 0xb504f333f9de6484597d89b375
            let z := sdiv(shl(0x64, sub(s, x)), add(x, s))

            // u = z**2 in Q96, truncated; u in [0, 0.029438 * 2**96].
            let u := shr(0x68, mul(z, z))

            // Constant terms of p and q in Q94; p(0) = q(0) by construction, so the
            // literal is shared.
            let c0 := 0xb05a8b41cf51c04d1b8a08d465

            // Numerator p(u), Horner up the basis staircase Q68 -> Q80 -> Q86 -> Q93 -> Q94.
            // p(u)/2**94 in [663.7, 705.5] on the domain. The leading product is nonnegative,
            // so the first shift may be logical.
            let p := sub(shr(0x54, mul(0xf642b0ed5372ff45e0, u)), 0xede142e73a9acbb00e9c42)
            p := add(sar(0x5a, mul(p, u)), 0xf2a56533e74a454c9d585f70)
            p := sub(sar(0x59, mul(p, u)), 0xb44d9253cd61fb87dc7efcfbc5)
            p := add(sar(0x5f, mul(p, u)), c0)

            // Denominator q(u), monic, Horner up the staircase Q96 -> Q87 -> Q85 -> Q93 ->
            // Q94. q(u)/2**94 in [-705.5, -656.0] on the domain: bounded away from zero, and
            // p(u)/(-q(u)) in [1, 1.01].
            let q := sub(u, 0x364589193443b48661938f59da)
            q := add(sar(0x69, mul(q, u)), 0xe904c4e76307954df78feedf)
            q := sub(sar(0x62, mul(q, u)), 0xad960ab2f600bd9765c15ffd)
            q := add(sar(0x58, mul(q, u)), 0xd1b1fedec544f0ea0bc812bbbc)
            q := sub(sar(0x5f, mul(q, u)), c0)

            // A = 2*atanh(-z/2**100) in Q100: |p * z| < 2**201 and |q| > 656 * 2**94, so
            // the quotient fits in 98 bits.
            r := sdiv(mul(p, z), q)

            // Rescale to ray in Q72: 5**27 = 10**27 * 2**72 / 2**(100 + 27); exact.
            r := mul(r, 0x6765c793fa10079d)

            // Add k * round(ln(2) * 10**27 * 2**72). k is two's complement (k in [-103, 151]);
            // `mul` wraps correctly.
            r := add(r, mul(0x23d5b9ff36551802aa5d6f9754b0f3fad83b19450, k))

            // Add floor((ln(s/2**103) + 103*ln(2) - 18*ln(10)) * 10**27 * 2**72) - 2.36e21.
            // The 2.36e21 subtrahend is the one-sided error margin described above.
            r := add(r, 0x61e2c6b2c35132b01ead59b21a4a764a0e2f452bd5)

            // Q72 -> integer ray result (`sar` floors), then the x == 10**18 correction.
            r := add(sar(0x48, r), one)
        }
    }

    /// @notice Compute the natural logarithm of a positive fixnum with 10**18 (wad) basis,
    ///         returning the result as a fixnum with 10**18 (wad) basis.
    /// @dev Let Lw = 10**18 * ln(x / 10**18) be the exact, infinite-precision result. This
    ///      function returns either `floor(Lw)` or `floor(Lw) - 1`; the contract, the
    ///      monotonicity guarantee, and `lnWadToWad(10**18) == 0` carry over from `lnWad`
    ///      because flooring composes exactly with floor division by 10**9.
    function lnWadToWad(int256 x) internal pure returns (int256 r) {
        r = lnWad(x);
        // Floor division of the ray result by 10**9 (`sdiv` alone truncates toward zero,
        // which would round negative results the wrong way). Equivalent Solidity:
        //     r = (r - (r < 0 ? 10**9 - 1 : 0)) / 10**9;
        // The subtraction cannot overflow: |r| < 2**97.
        assembly ("memory-safe") {
            r := sdiv(sub(r, mul(slt(r, 0), 0x3b9ac9ff)), 0x3b9aca00)
        }
    }
}
