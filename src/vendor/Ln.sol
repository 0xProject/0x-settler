// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;

library Ln {
    /// @notice Compute the natural logarithm of a positive fixnum with 10**18 basis.
    /// @dev Let L = 10**18 * ln(x / 10**18) be the exact, infinite-precision result. This
    ///      function returns either `floor(L)` or `floor(L) - 1` (equivalently, the unique
    ///      integers r satisfy L - 2 < r <= L). It never returns a value greater than the
    ///      correctly-rounded-down result. Reverts with `LnWadUndefined()` when `x <= 0`.
    function lnWad(int256 x) internal pure returns (int256 r) {
        // Assembly is required for `clz`, wrapping arithmetic on 256-bit fixnums, and the
        // truncating `sar`/`sdiv` primitives whose rounding directions the error analysis
        // below depends on. Equivalent pseudocode, in exact real arithmetic:
        //     require(x > 0);
        //     k = floor(log2(x)) - 96;                    // x = m * 2**k, m in [2**96, 2**97)
        //     m = x / 2**k;                               // Q96 fixnum in [1, 2)
        //     z = (m - s) / (m + s);                      // s = sqrt(2) * 2**96; |z| <= 3 - 2*sqrt(2)
        //     A = 2 * atanh(z) ~= z * p(z**2) / q(z**2);  // ln(m / 2**96) = 2*atanh(z) + ln(s / 2**96)
        //     return floor(10**18 * (A + ln(s) + k*ln(2) - 18*ln(10)) - margin);
        //
        // p/q is a (3,3)-degree rational minimax approximation of f(u) = atanh(sqrt(u))/sqrt(u)
        // on u in [0, (3-2*sqrt(2))**2], with coefficients rounded to Q96; the sup-norm error of
        // the rounded rational is certified <= 2.532e-19. The result is accumulated in Q78 with
        // basis 10**18 (1 final ulp = 2**78). Upper error bound before the margin: minimax
        // 2*|z|*2.532e-19*10**18*2**78 <= 2.63e22, plus truncation of z, u, the Horner steps,
        // the final sdiv, and rounding of the ln(2) constant, together < 1e13. The constant
        // term is biased down by a margin of 3e22 > 2.63e22 so the Q78 accumulator never
        // exceeds L*2**78. Lower bound: margin + downward errors (the same terms, plus < 2**-96
        // relative truncation of m) total < 5.7e22 < 2**78, so the accumulator also always
        // exceeds (L-1)*2**78. `sar(78, .)` therefore yields floor(L) or floor(L) - 1.
        assembly ("memory-safe") {
            if iszero(sgt(x, 0)) {
                mstore(0x00, 0x1615e638) // `LnWadUndefined()`.
                revert(0x1c, 0x04)
            }

            // Normalize: x := m, a Q96 fixnum in [1, 2), truncated from x / 2**k. Truncation
            // underestimates ln(x) by less than 2**-96 (only possible when k > 0).
            let c := clz(x)
            let k := sub(0x9f, c)
            x := shr(0x9f, shl(c, x))

            // z = (m - s)/(m + s) in Q96, truncated toward zero, where the Q96 constant
            // s = 0x16a09e667f3bcc908b2fb1367 = round(sqrt(2) * 2**96). Centering at s makes
            // |z| <= 3 - 2*sqrt(2) ~= 0.17157 over m in [1, 2), and
            // ln(m) = 2*atanh(z/2**96) + ln(s/2**96).
            let s := 0x16a09e667f3bcc908b2fb1367
            let z := sdiv(shl(0x60, sub(x, s)), add(x, s))

            // u = z**2 in Q96, truncated; u in [0, 0.029438 * 2**96].
            let u := shr(0x60, mul(z, z))

            // Numerator p(u), Horner in Q96. p(u)/2**96 in [-12.03, -11.57] on the domain.
            let p := sub(sar(0x60, mul(0x35df006e603cd672cc56856f, u)), 0x4d2343bbe6f1bc6bc52c19476)
            p := add(sar(0x60, mul(p, u)), 0xf7eb3d8e052bcbf7ee1828049)
            p := sub(sar(0x60, mul(p, u)), 0xc0631c0b347de96c2c5867380)

            // Denominator q(u), monic, Horner in Q96. q(u)/2**96 in [-12.03, -11.45] on the
            // domain: bounded away from zero, and p(u)/q(u) in [1, 1.01].
            let q := sub(u, 0x8ead228f38fe4d674ca1bf0b2)
            q := add(sar(0x60, mul(q, u)), 0x1380c46e716aaf05b93b36e930)
            q := sub(sar(0x60, mul(q, u)), 0xc0631c0b347de968fad1273f4)

            // r = 2*atanh(z/2**96) * 10**18 * 2**78 ~= (10**18 / 2**17) * p * z / q.
            // |p * z| < 2**194 and |(10**18 / 2**17) * p * z| < 2**237: no overflow.
            r := sdiv(mul(0x6f05b59d3b2, mul(p, z)), q)

            // Add k * round(ln(2) * 10**18 * 2**78). k is two's complement (k in [-96, 158]);
            // `mul` wraps correctly.
            r := add(r, mul(0x267a36c0c95b3975ab3ee5b203a7614a3f7, k))

            // Add floor((ln(s/2**96) + 96*ln(2) - 18*ln(10)) * 10**18 * 2**78) - 3e22.
            // The 3e22 subtrahend is the one-sided error margin described above.
            r := add(r, 0x58452ffd07d74b4395bf265ea3c4e3c7f3f1)

            // Q78 -> integer result; `sar` floors.
            r := sar(0x4e, r)
        }
    }
}
