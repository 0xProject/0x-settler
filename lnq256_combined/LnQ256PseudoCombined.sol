// SPDX-License-Identifier: MIT
pragma solidity ^0.8.30;

// PSEUDO-SOLIDITY ONLY.
// This file intentionally does not compile. It documents the control flow and
// fixed-point layout for a 2-stage floor(ln(x) * 2^256) implementation on a
// 512-bit positive integer x = (xHi, xLo).
//
// This is the combined design integrating two independent optimizations:
//
//   Stage 1: Q216 Remez-optimal [6/7] rational + G=24 guard bits
//     - 15x less Horner quantization error (Q216 vs Q212)
//     - 0 extra gas (all intermediates already 2-word pairs for any G > 0)
//     - +17 bytes code size (slightly wider constant hi words)
//     - Fallback rate: 0.035% on random inputs (21x better than Q212/G=13)
//
//   Stage 2: One-shared-2-bucket micro reduction
//     - Lower bucket: c0 = 0 (free)
//     - Upper bucket: c1 = 1/64 (shift-encoded)
//     - Boundary: 1/128 (shift-encoded)
//     - Only 1 nonzero additive constant (32 bytes)
//     - Saves ~128 bytes of stage-2 constants vs prior 2-bucket design
//     - ~8% more series terms when fallback runs (negligible at 0.035% rate)

library LnQ256PseudoCombined {
    // ═══════════════════════════════════════════════════════════════════
    // STAGE 1: Q216/G24 fast path
    // ═══════════════════════════════════════════════════════════════════

    uint256 internal constant COEFF_BITS = 216;
    uint256 internal constant G_FAST = 24;

    // Per-bucket bias and certified radius in Q(256 + 24).
    int16[16] internal constant FAST_BIAS_Q = [
        -150, -862, 1222, -348, 42, 196, 188, 154,
        42, 2, -250, 1356, 33, -1140, 104, -179
    ];
    uint16[16] internal constant FAST_RADIUS_Q = [
        1199, 5810, 6293, 3502, 148, 907, 1518, 891,
        150, 103, 3382, 6313, 44, 5792, 514, 1162
    ];

    uint256[16] internal constant N0 = [31,29,28,26,25,24,23,22,21,20,19,19,18,17,17,16];

    // Remez-optimal [6/7] rational coefficients, Q216 (27 bytes each).
    // Max Horner product: 464 bits (48-bit headroom under 512).
    int256[7] internal constant FAST_P = [
        int256(23402731481901597043981783929704540515310021200122024723180217230),
        int256(-79147257707505802445321067591641956191893173416852452736772062152),
        int256(105567710592264149655895345681626059811476843737297988261266061719),
        int256(-70280975374256110316161633634422318148227266301984626622229992403),
        int256(24260002286396336386066722552550012983868598792106518362024927003),
        int256(-4031542932217000284709476574733749729411078599780997370963274225),
        int256(244504971595928297752455626929162943780014968997496095305629633)
    ];
    int256[7] internal constant FAST_Q = [
        int256(-442327261958050172847695917721755520215342540249012582887183524330),
        int256(764050311468718105200385962090128619260907774191827731723142005680),
        int256(-698357271234189264361221256846859697717152049975428562654123141828),
        int256(361238115265142525912392094197617069095853073482781560893409836147),
        int256(-104363990572981334424492003201115405883168394510253602517671885198),
        int256(15307805589224505617810266544830173595922016396186463802374189830),
        int256(-855788182002653539265473379773190817088756284166928459588115371)
    ];

    // Q280 constants: ln(2) and -ln(n/32) for each bucket.
    // See Python model for exact values (omitted here for brevity).

    // ═══════════════════════════════════════════════════════════════════
    // STAGE 2: one-profile micro reduction + adaptive odd atanh series
    // ═══════════════════════════════════════════════════════════════════

    // One shared 2-bucket split in |z|:
    //   lower bucket: c0 = 0              -> no constant needed
    //   upper bucket: c1 = 64/4096 = 1/64 -> encoded as SHR(250, sign(z))
    //   boundary:     b  = 32/4096 = 1/128-> comparison: |z| < 1 << 249
    uint8 constant C1_NUM = 64;
    uint8 constant BOUND_NUM = 32;
    uint8 constant STAGE2_DEN_BITS = 12;

    // floor(2 * atanh(1/64) * 2^256).  The only stage-2 constant (32 bytes).
    uint256 constant A64_Q256 = 3618797306320365907038389356091966445740960606432524368886479476623023988535;

    uint8 constant MAX_STAGE2_TERMS = 80;

    struct CoarseState {
        uint16 exponent;
        uint8  bucket;
        uint256 coarseNum;
        int256 uNumHi;
        uint256 uNumLo;
        uint256 zDenHi;
        uint256 zDenLo;
    }

    // ── Entry point ──

    function floorLnQ256(uint256 xHi, uint256 xLo)
        internal
        pure
        returns (uint256 outHi, uint256 outLo, bool usedFallback, uint256 termsUsed)
    {
        require(xHi != 0 || xLo != 0, "x=0");
        if (xHi == 0 && xLo == 1) {
            return (0, 0, false, 0);
        }

        CoarseState memory s = _extractState(xHi, xLo);

        // Stage 1: Q216/G24 fast evaluation.
        (int256 qFastHi, uint256 qFastLo) = _fastEvalState(s);

        // Per-bucket re-centering.
        (qFastHi, qFastLo) = _addSmallSigned(qFastHi, qFastLo, FAST_BIAS_Q[s.bucket]);

        // Same-floor test with per-bucket radius.
        uint256 fastRadius = FAST_RADIUS_Q[s.bucket];
        (int256 qLoHi, uint256 qLoLo) = _floorShrSigned(
            _subSmall(qFastHi, qFastLo, fastRadius), G_FAST
        );
        (int256 qHiHi, uint256 qHiLo) = _floorShrSigned(
            _addSmall(qFastHi, qFastLo, fastRadius), G_FAST
        );

        if (_cmpSigned(qLoHi, qLoLo, qHiHi, qHiLo) == 0) {
            return (_signedToUnsigned(qLoHi, qLoLo), false, 0);
        }

        // Stage 2: one-profile micro reduction + adaptive series.
        (int256 rHi, uint256 rLo, uint256 usedTerms) =
            _stage2ResolveOneProfile(s, qFastHi, qFastLo, qLoHi, qLoLo, qHiHi, qHiLo);

        return (_signedToUnsigned(rHi, rLo), true, usedTerms);
    }

    // ── Fast path evaluation (identical to LnQ256PseudoQ216G24.sol) ──

    function _fastEvalState(CoarseState memory s)
        internal pure returns (int256 qHi, uint256 qLo)
    {
        // z = u / (2 + u), at Q280 precision.
        // w = z^2 >> 280, downshift to Q256 for Horner.
        // Horner evaluation of [6/7] rational at Q216.
        // Explicit odd terms: 2z + (2/3)z^3 + (2/5)z^5 + (2/7)z^7
        // Rational residual: z^9 * R(w)
        // Sum: e*ln2 + C0[j] + local terms
        //
        // See LnQ256PseudoQ216G24.sol for the full expansion.
    }

    // ── Stage 2: one-profile micro reduction ──

    function _stage2ResolveOneProfile(
        CoarseState memory s,
        int256 qFastHi, uint256 qFastLo,
        int256 qLoHi, uint256 qLoLo,
        int256 qHiHi, uint256 qHiLo
    )
        internal pure returns (int256 outHi, uint256 outLo, uint256 termsUsed)
    {
        // Compute z = u / (2 + u) in signed Q256.
        int256 z = _divQ256(s.uNumHi, s.uNumLo, s.zDenHi, s.zDenLo);
        int256 a = z < 0 ? -z : z;

        // One shared 2-bucket split: boundary = 1/128.
        // In Q256: 1/128 = 1 << (256-7) = 1 << 249.
        bool upper = uint256(a) >= (uint256(BOUND_NUM) << (256 - STAGE2_DEN_BITS));

        // Center selection: c = 0 (lower) or sign(z)/64 (upper).
        // In Q256: 1/64 = 1 << (256-6) = 1 << 250.
        int256 c = upper ? int256(uint256(C1_NUM) << (256 - STAGE2_DEN_BITS)) : int256(0);
        if (z < 0) c = -c;

        // t = (z - c) / (1 - z*c)
        int256 t = _divQ256(_subQ256(z, c), _subQ256(int256(1) << 256, _mulQ256(z, c)));

        // Prefix correction: exact constants minus fast-path approximation.
        (int256 deltaHi, uint256 deltaLo) = _deltaPrefixExactMinusFast(
            s, qFastHi, qFastLo, qHiHi, qHiLo
        );

        // Add micro additive constant: 2*atanh(c).
        // For lower bucket (c=0): nothing to add.
        // For upper bucket (c=1/64): add sign(z) * A64_Q256.
        if (upper) {
            if (z < 0) {
                (deltaHi, deltaLo) = _subSmallSigned(deltaHi, deltaLo, int256(A64_Q256));
            } else {
                (deltaHi, deltaLo) = _addSmallSigned(deltaHi, deltaLo, int256(A64_Q256));
            }
        }

        // Adaptive odd atanh series to certify boundary sign.
        return _resolveTailByAdaptiveAtanh(deltaHi, deltaLo, t, qLoHi, qLoLo, qHiHi, qHiLo);
    }

    function _resolveTailByAdaptiveAtanh(
        int256 deltaHi, uint256 deltaLo,
        int256 tQ256,
        int256 qLoHi, uint256 qLoLo,
        int256 qHiHi, uint256 qHiLo
    ) internal pure returns (int256 outHi, uint256 outLo, uint256 termsUsed) {
        // Same adaptive series as prior designs:
        //   2*atanh(t) = 2*(t + t^3/3 + t^5/5 + ...)
        // After each term, bound remainder:
        //   R_m <= 2*|t|^(2m+3) / ((2m+3)*(1-t^2))
        // Stop when the sign of delta + 2*atanh(t) is forced.
        //
        // See Python model for the executable reference.
    }

    // Helper stubs intentionally omitted.
}
