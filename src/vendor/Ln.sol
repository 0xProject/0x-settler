// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;

library Ln {
    function lnWad(int256 x) internal pure returns (int256 r) {
        /// @solidity memory-safe-assembly
        assembly {
            if iszero(sgt(x, 0)) {
                mstore(0x00, 0x1615e638) // `LnWadUndefined()`.
                revert(0x1c, 0x04)
            }

            // ── 1. Range reduction ─────────────────────────────────────────
            // Shift x so its high bit lands at position 96.
            // After this:  x = m_internal · 2^96   with   m_internal ∈ [1, 2).
            let c := clz(x)
            let k := sub(159, c)
            x := shr(159, shl(c, x))

            // ── 2. atanh substitution:  z = (m − 1)/(m + 1)   in Q96 ───────
            let TWO96 := shl(96, 1)
            let z := sdiv(shl(96, sub(x, TWO96)), add(x, TWO96))

            // ── 3. u = z²   in Q96 ─────────────────────────────────────────
            let u := sar(96, mul(z, z))

            // ── 4. Numerator p(u) — Horner; LAST step leaves num in Q192 ──
            let num :=     386692213752848720801329619                            // P4
            num := sub(sar(96, mul(num, u)),  14278668760191006216796320113)      // P3
            num := add(sar(96, mul(num, u)),   80791143393211373894836915812)      // P2
            num := sub(sar(96, mul(num, u)), 144012260871247609072064398628)      // P1
            num := add(mul(num, u), shl(96,    79228162514264337609150029708))     // P0 promoted

            // ── 5. Denominator q(u) — Horner stays in Q96 ─────────────────
            let den :=    2277930843114621577247569024                            // Q4
            den := sub(sar(96, mul(den, u)),  32096890353737504506818729143)     // Q3
            den := add(sar(96, mul(den, u)),  121752727015687765449182681860)     // Q2
            den := sub(sar(96, mul(den, u)), 170421648376002366840644783424)     // Q1
            den := add(sar(96, mul(den, u)),   79228162514264337593543950336)     // Q0

            // ── 6. f(u) = num / den.  Q192 / Q96 → Q96 ───────────────────
            let f := sdiv(num, den)

            // ── 7-8. (2·z·f) in (5^18·2^192) basis — one mul folds the ×2 ──
            // 2·5^18 = 7629394531250;  z·f is Q192, so this promotes to big basis.
            let logM := mul(mul(z, f), 7629394531250)

            // ── 9. Add k·ln(2) and the rounded reconciliation constant ─────
            // The second constant is  (96·ln(2) − ln(1e18))·5^18·2^192  +  2^173.
            // The extra 2^173 is half an output-ULP: folding it in makes the
            // final sar a round-to-nearest instead of a floor, for ZERO extra ops.
            // (Without it, ln(1) computes as −0.066 ULP and floors to −1.)
            let logX := add(
                add(logM,
                    mul(k, 16597577552685614221487285958193947469193820559219878177908093499208371)
                ),  //                                                            ↑ ln(2) · 5^18 · 2^192
                        600920179829731861748675400734636216301396844198685892064399282412077700
            )       //                       ↑ (96·ln(2) − ln(1e18))·5^18·2^192  +  2^173  (round-to-nearest)

            // ── 10. (5^18·2^192) → WAD via a single right shift ───────────
            r := sar(174, logX)
        }
    }
}
