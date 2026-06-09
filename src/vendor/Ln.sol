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

            // z = [0, 1/3] * 2^96
            // ── 3. u = z²   in Q96 ─────────────────────────────────────────
            let u := shr(96, mul(z, z))

            // ── 4. Numerator p(u) — Horner; LAST step leaves num in Q192 ──
            let p := sub(sar(96, mul(11118219211550167393714956266, u)), 617966711108841718279123450878)
            p := add(sar(96, mul(p, u)), 5440510745984559975347664312626)
            p := sub(sar(96, mul(p, u)), 16611667854347085824509759028817) // 2^96
            p := add(sar(96, mul(p, u)), 20539621768103526992786752172899)
            p := sub(sar(96, mul(p, u)), 8828913114255221716823834898758) // 2^96


            // // ── 5. Denominator q(u) — Horner stays in Q96 ─────────────────
            let q := sub(u, 1644639538787028851042260486634)
            q := add(sar(96, mul(q, u)), 9563070875747371828339838696894)
            q := sub(sar(96, mul(q, u)), 22673416166892241714432840535271)
            q := add(sar(96, mul(q, u)), 23482592806188600898200439671396)
            q := sub(sar(96, mul(q, u)), 8828913114255221716823740237208) // 2^96


            // p/q = [1, 1.03972077084) * 2^96

            // ── 6. P * S / q --> Q96 format ()
            r := sdiv(mul(7629394531250, mul(p,z)), q)

            r := add(
                r,
                mul(209490880843000310329976925384580330202103, k)
            )
            r := add(7584678992416887619351357778094049639144312, r)
            r := sar(78, r)
        }
    }
}
