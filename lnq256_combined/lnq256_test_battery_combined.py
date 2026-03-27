"""Validation harness for lnq256_model_combined.py.

Default battery (per seed):
- 1..10_000
- every power of two with +/-4 neighbors
- representative coarse bucket boundaries with +/-6 neighbors
- 50k uniform random across bit lengths
- 10k random perturbations around coarse bucket boundaries

Plus hard-boundary family: x_b = round(exp(round(b * ln(2) * 2^256) / 2^256))
for b in [279, 511].
"""

from __future__ import annotations

import argparse
import random
import time
from typing import List

import mpmath as mp

from lnq256_model_combined import (
    floor_ln_q256,
    true_floor_ln_q256,
    hard_boundary_family,
    extract_state,
    FAST_RADIUS_Q,
    G_FAST,
)


def build_battery(random_cases: int, boundary_cases: int, seed: int) -> List[int]:
    rng = random.Random(seed)
    cases: List[int] = []

    cases.extend(range(1, 10_001))

    for e in range(512):
        p2 = 1 << e
        for d in range(-4, 5):
            x = p2 + d
            if x > 0:
                cases.append(x)

    for e in [4, 8, 16, 32, 64, 128, 255, 256, 257, 383, 511]:
        base = 1 << e
        for j in range(16):
            b = ((16 + j) * base) // 16
            for d in range(-6, 7):
                x = b + d
                if base <= x < (1 << (e + 1)):
                    cases.append(x)

    for _ in range(random_cases):
        bits = rng.randrange(1, 513)
        cases.append(rng.getrandbits(bits - 1) | (1 << (bits - 1)))

    for _ in range(boundary_cases):
        e = rng.randrange(4, 512)
        base = 1 << e
        j = rng.randrange(16)
        b = ((16 + j) * base) // 16
        x = b + rng.randint(-1000, 1000)
        if 0 < x < (1 << (e + 1)) and x >= base:
            cases.append(x)

    seen = set()
    uniq: List[int] = []
    for x in cases:
        if x not in seen:
            uniq.append(x)
            seen.add(x)
    return uniq


def merge_batteries(batteries) -> List[int]:
    merged: List[int] = []
    seen = set()
    for battery in batteries:
        for x in battery:
            if x not in seen:
                merged.append(x)
                seen.add(x)
    return merged


def main() -> int:
    ap = argparse.ArgumentParser(description="Validation battery for combined Q216/G24 + oneprofile model")
    ap.add_argument("--random-cases", type=int, default=50_000)
    ap.add_argument("--boundary-cases", type=int, default=10_000)
    ap.add_argument("--seeds", type=int, nargs="+", default=[1, 2, 3])
    ap.add_argument("--include-hard-family", action="store_true", default=True)
    ap.add_argument("--no-hard-family", action="store_true", default=False)
    ap.add_argument("--max-terms", type=int, default=80)
    ap.add_argument("--per-bucket", action="store_true", default=False,
                    help="Print per-bucket fallback breakdown")
    args = ap.parse_args()

    if args.no_hard_family:
        args.include_hard_family = False

    mp.mp.dps = 420

    start_build = time.time()
    batteries = [
        build_battery(args.random_cases, args.boundary_cases, seed)
        for seed in args.seeds
    ]
    if args.include_hard_family:
        batteries.append(hard_boundary_family())
    cases = merge_batteries(batteries)
    build_time = time.time() - start_build

    print(f"configuration: Q216 Remez rational, G_FAST={G_FAST}, oneprofile stage-2")
    print(f"seeds: {args.seeds}")
    print(f"hard boundary family: {'yes' if args.include_hard_family else 'no'}")
    print(f"cases: {len(cases)}")
    print(f"build time: {build_time:.3f}s")
    print()

    fallback_count = 0
    terms_total = 0
    terms_max = 0
    terms_list: List[int] = []
    bucket_fb = [0] * 16
    bucket_total = [0] * 16

    start = time.time()
    for idx, x in enumerate(cases, 1):
        got, used_fallback, terms_used = floor_ln_q256(x, max_terms=args.max_terms)
        truth = true_floor_ln_q256(x)

        if x > 1:
            state = extract_state(x)
            bucket_total[state.bucket] += 1

        if got != truth:
            print(f"FAIL at case {idx}: x={x}")
            print(f"  got   = {got}")
            print(f"  truth = {truth}")
            print(f"  fallback={used_fallback}, terms={terms_used}")
            return 1

        if used_fallback:
            fallback_count += 1
            terms_total += terms_used
            terms_max = max(terms_max, terms_used)
            terms_list.append(terms_used)
            if x > 1:
                bucket_fb[state.bucket] += 1

    elapsed = time.time() - start

    print("all cases passed")
    print(f"fallbacks: {fallback_count}")
    print(f"fallback rate: {fallback_count / len(cases):.6%}")
    print(f"max odd atanh terms used: {terms_max}")
    if terms_list:
        print(f"avg odd atanh terms among fallbacks: {terms_total / len(terms_list):.3f}")
        print(f"avg odd atanh terms per top-level call: {terms_total / len(cases):.6f}")
    else:
        print("avg odd atanh terms among fallbacks: 0.000")
        print("avg odd atanh terms per top-level call: 0.000000")
    print(f"elapsed: {elapsed:.3f}s")

    if args.per_bucket:
        print(f"\n{'bucket':>6} | {'total':>7} | {'fallbacks':>9} | {'fb rate':>10} | {'radius':>8}")
        print("-" * 55)
        for j in range(16):
            n = bucket_total[j]
            fb = bucket_fb[j]
            rate = fb / n if n > 0 else 0
            print(f"  {j:>4} | {n:>7} | {fb:>9} | {rate:>9.4%} | {FAST_RADIUS_Q[j]:>8}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
