"""Validation harness for the relaxed z^5/Q219/G9 lnQ256 bounds model."""

from __future__ import annotations

import argparse
import time

import mpmath as mp

from lnq256_model_stage1_z5_global import bounds_ln_q256
from lnq256_search_stage1_relaxed import build_search_battery


def main() -> int:
    ap = argparse.ArgumentParser(description="Validation battery for the relaxed z^5/Q219/G9 lnQ256 bounds model")
    ap.add_argument("--random-cases", type=int, default=50_000)
    ap.add_argument("--boundary-cases", type=int, default=10_000)
    ap.add_argument("--seeds", type=int, nargs="+", default=[1, 2, 3])
    args = ap.parse_args()

    mp.mp.dps = 420
    scale = mp.mpf(2) ** 256

    start_build = time.time()
    cases = build_search_battery(args.random_cases, args.boundary_cases, args.seeds)
    build_time = time.time() - start_build

    lower_exact = 0
    lower_minus1 = 0
    upper_exact = 0
    upper_plus1 = 0

    start = time.time()
    for idx, x in enumerate(cases, 1):
        y = mp.log(x) * scale
        lower_truth = int(mp.floor(y))
        upper_truth = int(mp.ceil(y))
        lower, upper = bounds_ln_q256(x)

        if lower == lower_truth:
            lower_exact += 1
        elif lower == lower_truth - 1:
            lower_minus1 += 1
        else:
            print(f"LOWER FAIL at case {idx}: x={x}")
            print(f"  got   = {lower}")
            print(f"  truth = {lower_truth} or {lower_truth - 1}")
            return 1

        if upper == upper_truth:
            upper_exact += 1
        elif upper == upper_truth + 1:
            upper_plus1 += 1
        else:
            print(f"UPPER FAIL at case {idx}: x={x}")
            print(f"  got   = {upper}")
            print(f"  truth = {upper_truth} or {upper_truth + 1}")
            return 1

    elapsed = time.time() - start
    print(f"seeds: {args.seeds}")
    print(f"cases: {len(cases)}")
    print(f"build time: {build_time:.3f}s")
    print("all cases passed")
    print(f"lower exact/-1: {lower_exact}/{lower_minus1}")
    print(f"upper exact/+1: {upper_exact}/{upper_plus1}")
    print(f"elapsed: {elapsed:.3f}s")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
