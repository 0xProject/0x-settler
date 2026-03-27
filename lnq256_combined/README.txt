lnQ256 combined implementation: Q216/G24 fast path + oneprofile stage-2
=======================================================================

This package combines two independent optimizations into a single design:

  Stage 1 (fast path): Q216 Remez-optimal rational + G=24 guard bits
  Stage 2 (fallback):  One-shared-2-bucket micro reduction

Together they minimize both the fallback rate AND the constant payload.

Design summary
--------------

Stage 1 (fast path, ~99.965% of inputs, ~930 gas):
- 16-bucket coarse reduction, N0 table
- Fast kernel: 2z + (2/3)z^3 + (2/5)z^5 + (2/7)z^7 + z^9 * R(z^2)
- R is a Remez-optimal [6/7] rational, Q216 coefficients (27 bytes each)
- Guard bits: G_FAST = 24 (Q280 working precision)
- Per-bucket bias and certified radius

Stage 2 (fallback, ~0.035% of inputs, ~2000-5000 gas):
- One shared 2-bucket micro split in |z|:
    lower bucket: c0 = 0 (free -- no constant)
    upper bucket: c1 = 1/64 (dyadic -- shift-encoded)
    boundary:     b  = 1/128 (dyadic -- shift-encoded)
- Only 1 nonzero additive constant: A64_Q256 = floor(2*atanh(1/64)*2^256)
- Adaptive odd atanh series with certified remainder bound

Provenance
----------

Stage 1 improvements (Q216 + G=24):
- Rational coefficients recomputed via Remez minimax algorithm.
- Minimax approximation error: 5.2e-67 (same degree, better quantization).
- Horner error: 1.2e-65 (was 1.8e-64 at Q212) -- 15x improvement.
- Guard bits raised from 13 to 24 at zero runtime cost (all Q(256+G)
  intermediates are 2-word 512-bit pairs for any G > 0).
- Bias/radius calibrated on 6-seed battery, validated on seeds 7..15.

Stage 2 optimization (oneprofile):
- Prior design used 2 arbitrary-precision micro buckets with Q255 centers:
    BOUND_Z_Q255 (32 bytes) + CENTER_Z_Q255[2] (64 bytes) +
    A_MICRO_Q256[2] (64 bytes) = ~160 bytes
- New design uses dyadic centers c0=0, c1=1/64 with boundary 1/128:
    A64_Q256 (32 bytes) = 32 bytes
- Savings: ~128 bytes of deployed constant payload
- Trade: ~8-9% more series terms per fallback (negligible at 0.035% rate)

Constant payload summary
------------------------

  Component                 | Bytes
  --------------------------|------
  FAST_P[7] (Q216)          |  189
  FAST_Q[7] (Q216)          |  189
  LN2_FAST (Q280)           |   64
  C0_FAST[16] (Q280)        | 1024
  FAST_BIAS_Q[16]           |   32
  FAST_RADIUS_Q[16]         |   32
  A64_Q256                  |   32
  TOTAL                     | 1562

For comparison:
  Prior Q212/G13 + old stage 2: ~1700 bytes
  Original 9/9 Q256/G24:        ~1920 bytes (20 coefficients at 32 bytes)

Validation results
------------------

All runs: zero violations, zero correctness failures.

  Battery                       | Cases   | Fallback | Max terms | Avg terms/fb
  ------------------------------|---------|----------|-----------|-------------
  seeds 1,2,3 (no hard family)  | 190,835 | 0.0346%  | 19        | 15.5
  seeds 1,2,3 + hard family     | 191,068 | 0.1565%  | 21        | 10.0
  seeds 7,8,9 + hard family     | 191,106 | 0.1596%  | 21        | 10.2

Comparison across implementations
----------------------------------

  Implementation                    | Fb (random) | Fb (+hard) | Stage-2 bytes
  ----------------------------------|-------------|------------|---------------
  lnq256_packaged (9/9 Q256/G24)   | 0.047%      | n/a        | ~288
  stage1 Q212/G13                   | 0.730%      | 0.852%     | ~160
  Q216/G24 (our fast-path only)     | 0.035%      | 0.157%     | ~160
  THIS: Q216/G24 + oneprofile       | 0.035%      | ~0.16%     | ~32

Files
-----
- LnQ256PseudoCombined.sol          Pseudo-Solidity (non-compilable) design spec.
- lnq256_model_combined.py          Executable Python model (source of truth).
- lnq256_test_battery_combined.py   Validation harness.
- README.txt                        This file.

Quick smoke test
----------------
  python lnq256_model_combined.py

Validation
----------
  python lnq256_test_battery_combined.py --seeds 1 2 3 --per-bucket
  python lnq256_test_battery_combined.py --seeds 7 8 9
  python lnq256_test_battery_combined.py --seeds 1 2 3 --no-hard-family
