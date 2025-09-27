#!/usr/bin/env python3
"""
Quadratic Overapproximation Optimization for invE Threshold (Fixed-Point Aware)

This script searches for quadratic coefficients expressed in Q12 fixed point
such that the resulting approximation overestimates the measured invE
threshold for every bucket while minimising the average waste.

The polynomial is evaluated as:
    threshold(i) = floor(((a_fp * i + b_fp) * i) / 2^12) + c

where a_fp and b_fp are signed integers in Q12 and c is an integer. The search
enumerates feasible integer coefficients within user-provided bounds, prunes
unsuitable candidates early, and reports the best combination.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from typing import Iterable, List, Tuple


SHIFT = 12


@dataclass
class FixedPointSolution:
    a_fp: int
    b_fp: int
    c: int
    shift: int
    approximations: List[int]
    margins: List[int]
    avg_margin: float
    min_margin: int
    max_margin: int

    @property
    def a(self) -> float:
        return self.a_fp / (1 << self.shift)

    @property
    def b(self) -> float:
        return self.b_fp / (1 << self.shift)


def load_thresholds(filename: str = "threshold_optimization_results.json") -> Tuple[List[int], List[int], dict]:
    """Load bucket thresholds from disk."""
    with open(filename, "r", encoding="utf-8") as fh:
        data = json.load(fh)

    bucket_to_threshold: dict[int, int] = {}
    for bucket_str, bucket_data in data["buckets"].items():
        bucket = int(bucket_str)
        if bucket == 64:
            # Bucket 64 is not used.
            continue

        latest = bucket_data.get("latest")
        if not latest:
            continue

        min_threshold = latest.get("min_threshold")
        if min_threshold is None or latest.get("min_threshold_status") == "TIMEOUT":
            min_threshold = latest.get("safety_threshold", 79)

        bucket_to_threshold[bucket] = int(min_threshold)

    buckets = sorted(bucket_to_threshold)
    thresholds = [bucket_to_threshold[i] for i in buckets]
    return buckets, thresholds, bucket_to_threshold


def fixed_point_base_values(buckets: Iterable[int], a_fp: int, b_fp: int, shift_scale: int) -> List[int]:
    """Compute floor(((a_fp * i + b_fp) * i) / 2^shift) for each bucket."""
    base_values: List[int] = []
    for bucket in buckets:
        inner = a_fp * bucket + b_fp
        numerator = inner * bucket
        base = numerator // shift_scale  # Floor division works for signed values
        base_values.append(base)
    return base_values


def evaluate_candidate(
    base_values: List[int],
    thresholds: List[int],
    c_bounds: Tuple[int, int],
) -> Tuple[int, List[int]] | None:
    """Return the minimal feasible c and margins for this candidate or None if unsafe."""
    lower, upper = c_bounds
    required_c = lower

    for base, threshold in zip(base_values, thresholds):
        required_c = max(required_c, threshold - base)
        if required_c > upper:
            return None

    c = required_c
    approximations = [base + c for base in base_values]
    margins = [approx - threshold for approx, threshold in zip(approximations, thresholds)]

    if min(margins) < 0:
        # Should not happen, but guard against arithmetic surprises.
        return None

    return c, margins


def find_best_fixed_point(
    buckets: List[int],
    thresholds: List[int],
    *,
    shift: int = SHIFT,
    a_bounds: Tuple[int, int] | None = None,
    b_bounds: Tuple[int, int] | None = None,
    c_bounds: Tuple[int, int] | None = None,
) -> FixedPointSolution | None:
    """Enumerate integer coefficients and pick the minimal-average-waste solution."""

    shift_scale = 1 << shift

    if a_bounds is None or b_bounds is None or c_bounds is None:
        approx_a = 0.0195
        approx_b = -2.556
        a_center = int(round(approx_a * shift_scale))
        b_center = int(round(approx_b * shift_scale))
        window = max(32, shift_scale // 256)
        if a_bounds is None:
            a_bounds = (max(0, a_center - window), a_center + window)
        if b_bounds is None:
            b_bounds = (b_center - 8 * window, b_center + 8 * window)
        if c_bounds is None:
            c_bounds = (110, 130)

    print(
        f"Searching shift={shift} (Q{shift}) with a in {a_bounds}, b in {b_bounds}, c in {c_bounds}"
    )
    best: FixedPointSolution | None = None

    for a_fp in range(a_bounds[0], a_bounds[1] + 1):
        base_partial = [a_fp * bucket for bucket in buckets]

        for b_fp in range(b_bounds[0], b_bounds[1] + 1):
            base_values: List[int] = []
            required_c = c_bounds[0]
            unsafe = False

            for bucket, threshold, a_term in zip(buckets, thresholds, base_partial):
                inner = a_term + b_fp
                numerator = inner * bucket
                base = numerator // shift_scale
                base_values.append(base)
                required_c = max(required_c, threshold - base)
                if required_c > c_bounds[1]:
                    unsafe = True
                    break

            if unsafe:
                continue

            evaluated = evaluate_candidate(base_values, thresholds, c_bounds)
            if evaluated is None:
                continue

            c, margins = evaluated
            approximations = [base + c for base in base_values]

            avg_margin = sum(margins) / len(margins)
            min_margin = min(margins)
            max_margin = max(margins)

            candidate = FixedPointSolution(
                a_fp=a_fp,
                b_fp=b_fp,
                c=c,
                shift=shift,
                approximations=approximations,
                margins=margins,
                avg_margin=avg_margin,
                min_margin=min_margin,
                max_margin=max_margin,
            )

            if best is None:
                best = candidate
                continue

            if candidate.avg_margin < best.avg_margin:
                best = candidate
                continue

            if candidate.avg_margin == best.avg_margin and candidate.max_margin < best.max_margin:
                best = candidate

    return best


def print_solution(solution: FixedPointSolution, buckets: List[int]) -> None:
    """Pretty-print the chosen coefficients and statistics."""
    print("\n" + "=" * 70)
    print(f"BEST Q{solution.shift} FIXED-POINT QUADRATIC")
    print("=" * 70)

    print(f"a_fp = {solution.a_fp} (0x{solution.a_fp:x})  ->  a = {solution.a:.12f}")
    abs_b = abs(solution.b_fp)
    print(f"b_fp = {solution.b_fp} (abs = 0x{abs_b:x})  ->  b = {solution.b:.12f}")
    print(f"c    = {solution.c}")

    print("\nMargins (approx - threshold):")
    for bucket, margin in zip(buckets, solution.margins):
        print(f"  bucket {bucket:2d}: {margin}")

    print("\nSummary:")
    print(f"  Min margin  : {solution.min_margin}")
    print(f"  Max margin  : {solution.max_margin}")
    print(f"  Avg margin  : {solution.avg_margin:.6f}")

    print("\nAssembly snippet (use SAR for signed shift):")
    if solution.b_fp >= 0:
        inner_line = f"let inner := add(mul(0x{solution.a_fp:x}, i), 0x{solution.b_fp:x})"
    else:
        inner_line = f"let inner := sub(mul(0x{solution.a_fp:x}, i), 0x{abs_b:x})"

    print("```solidity")
    print(inner_line + f"  // (a*i + b) in Q{solution.shift}")
    print(f"let threshold := add(sar({solution.shift}, mul(i, inner)), {solution.c})")
    print("```")


def save_results(solution: FixedPointSolution) -> None:
    """Persist coefficients to quadratic_coefficients.json."""
    payload = {
        "fixed_point": {
            "shift": solution.shift,
            "a_fp": solution.a_fp,
            "b_fp": solution.b_fp,
            "c": solution.c,
            "avg_margin": solution.avg_margin,
            "min_margin": solution.min_margin,
            "max_margin": solution.max_margin,
        },
        "coefficients": {
            "a": solution.a,
            "b": solution.b,
            "c": solution.c,
        },
    }

    with open("quadratic_coefficients.json", "w", encoding="utf-8") as fh:
        json.dump(payload, fh, indent=2)

    print("\nSaved coefficients to quadratic_coefficients.json")


def main() -> None:
    print("=" * 70)
    print("QUADRATIC OVERAPPROXIMATION (FIXED-POINT SEARCH)")
    print("=" * 70)

    buckets, thresholds, _ = load_thresholds()
    print(f"Loaded {len(buckets)} buckets: {buckets[0]} – {buckets[-1]}")

    shift = 14
    solution = find_best_fixed_point(buckets, thresholds, shift=shift)
    if solution is None:
        print("No feasible fixed-point solution found within the provided bounds.")
        return

    print_solution(solution, buckets)
    save_results(solution)


if __name__ == "__main__":
    main()
