#!/usr/bin/env python3
"""
Optimize sqrt lookup table seeds by empirically testing with Solidity.
Forces invE=79 to test the most fragile case (4 Newton-Raphson iterations).

Usage:
    python3 script/optimize_sqrt_seeds.py --bucket N [M ...]  # Test specific bucket(s)
    python3 script/optimize_sqrt_seeds.py                     # Test problematic buckets (42-46)

Examples:
    python3 script/optimize_sqrt_seeds.py --bucket 44         # Test bucket 44
    python3 script/optimize_sqrt_seeds.py --bucket 42 43 44   # Test buckets 42, 43, 44
    python3 script/optimize_sqrt_seeds.py                     # Test buckets 42-46

The script will:
1. Test each seed by generating Solidity test files and running forge test
2. Find the minimum working seed for each bucket
3. Find the maximum working seed (for understanding limits)
4. Add a +2 safety margin for invE=79 cases
5. Generate new lookup table values
"""

import subprocess
import re
import os
import json
from typing import Tuple, List, Optional

# Current seeds from the modified lookup table
CURRENT_SEEDS = {
    16: 713, 17: 692, 18: 673, 19: 655, 20: 638, 21: 623, 22: 608, 23: 595,
    24: 583, 25: 571, 26: 560, 27: 549, 28: 539, 29: 530, 30: 521, 31: 513,
    32: 505, 33: 497, 34: 490, 35: 483, 36: 476, 37: 469, 38: 463, 39: 457,
    40: 451, 41: 446, 42: 441, 43: 435, 44: 430, 45: 426, 46: 421, 47: 417,
    48: 412, 49: 408, 50: 404, 51: 400, 52: 396, 53: 392, 54: 389, 55: 385,
    56: 382, 57: 378, 58: 375, 59: 372, 60: 369, 61: 366, 62: 363, 63: 360
}

# Original seeds for comparison
ORIGINAL_SEEDS = {
    16: 713, 17: 692, 18: 673, 19: 656, 20: 640, 21: 625, 22: 611, 23: 597,
    24: 585, 25: 574, 26: 563, 27: 552, 28: 543, 29: 533, 30: 524, 31: 516,
    32: 508, 33: 500, 34: 493, 35: 486, 36: 479, 37: 473, 38: 467, 39: 461,
    40: 455, 41: 450, 42: 444, 43: 439, 44: 434, 45: 429, 46: 425, 47: 420,
    48: 416, 49: 412, 50: 408, 51: 404, 52: 400, 53: 396, 54: 392, 55: 389,
    56: 385, 57: 382, 58: 379, 59: 375, 60: 372, 61: 369, 62: 366, 63: 363
}

class SeedOptimizer:
    def __init__(self):
        self.test_contract_path = "test/0.8.25/SqrtSeedOptimizerDynamic.t.sol"
        self.results = {}

    def generate_test_contract(self, bucket: int, seed: int) -> str:
        """Generate a test contract for a specific bucket and seed."""

        # Generate test points for the bucket
        test_cases = []

        if bucket == 44:
            # For bucket 44, ONLY use the known failing case
            # IMPORTANT: This specific input was discovered through fuzzing and represents
            # a worst-case scenario. Generated inputs are not challenging enough - they
            # would suggest seed 431 works, but this specific case needs seed 434.
            test_cases = [
                ("0x000000000000000000000000000000000000000580398dae536e7fe242efe66a",
                 "0x0000000000000000001d9ad7c2a7ff6112e8bfd6cb5a1057f01519d7623fbd4a")
            ]
        else:
            # For other buckets, generate comprehensive test points
            # For invE=79, we need x_hi in range [bucket*2^93, (bucket+1)*2^93)

            # Test lower boundary
            x_hi_low = bucket * (1 << 93)
            test_cases.append((hex(x_hi_low), "0x0"))

            # Test near lower boundary
            x_hi_low_plus = bucket * (1 << 93) + (1 << 80)
            test_cases.append((hex(x_hi_low_plus), "0xffffffffffffffffffffffff"))

            # Test middle
            x_hi_mid = bucket * (1 << 93) + (1 << 92)
            test_cases.append((hex(x_hi_mid), "0x8000000000000000000000000000000000000000000000000000000000000000"))

            # Test near upper boundary
            x_hi_high_minus = (bucket + 1) * (1 << 93) - (1 << 80)
            test_cases.append((hex(x_hi_high_minus), "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"))

            # Test upper boundary
            x_hi_high = (bucket + 1) * (1 << 93) - 1
            test_cases.append((hex(x_hi_high), "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"))

        # Build test functions for each case
        test_functions = []
        for i, (x_hi, x_lo) in enumerate(test_cases):
            test_functions.append(f"""
    function testCase_{i}() private pure {{
        uint256 x_hi = {x_hi};
        uint256 x_lo = {x_lo};

        uint512 x = alloc().from(x_hi, x_lo);
        uint256 r = x.sqrt({bucket}, {seed});

        // Verify: r^2 <= x < (r+1)^2
        (uint256 r2_lo, uint256 r2_hi) = SlowMath.fullMul(r, r);

        // Check r^2 <= x
        bool lower_ok = (r2_hi < x_hi) || (r2_hi == x_hi && r2_lo <= x_lo);
        require(lower_ok, "sqrt too high");

        // Check x < (r+1)^2
        if (r < type(uint256).max) {{
            uint256 r1 = r + 1;
            (uint256 r1_2_lo, uint256 r1_2_hi) = SlowMath.fullMul(r1, r1);
            bool upper_ok = (r1_2_hi > x_hi) || (r1_2_hi == x_hi && r1_2_lo > x_lo);
            require(upper_ok, "sqrt too low");
        }}
    }}""")

        # Build the main test function that calls all test cases
        all_test_calls = "\n        ".join([f"testCase_{i}();" for i in range(len(test_cases))])

        return f"""// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {{uint512, alloc}} from "src/utils/512Math.sol";
import {{SlowMath}} from "test/0.8.25/SlowMath.sol";
import {{Test}} from "@forge-std/Test.sol";

contract TestBucket{bucket}Seed{seed} is Test {{
{"".join(test_functions)}

    function test_bucket_{bucket}_seed_{seed}() public pure {{
        // Test all cases
        {all_test_calls}
    }}
}}"""

    def test_seed(self, bucket: int, seed: int, verbose: bool = True) -> bool:
        """Test if a seed works for a bucket by running Solidity tests."""
        if verbose:
            print(f"    Testing seed {seed}...", end='', flush=True)

        # Write test contract
        with open(self.test_contract_path, 'w') as f:
            f.write(self.generate_test_contract(bucket, seed))

        # Run forge test
        cmd = [
            "forge", "test",
            "--skip", "src/*",
            "--skip", "test/0.8.28/*",
            "--skip", "CrossChainReceiverFactory.t.sol",
            "--skip", "MultiCall.t.sol",
            "--match-path", self.test_contract_path,
            "--match-test", f"test_bucket_{bucket}_seed_{seed}",
            "-vv"
        ]

        try:
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=30,  # Increased timeout
                env={**os.environ, "FOUNDRY_FUZZ_RUNS": "10000"}
            )

            # Check if test passed
            passed = "Suite result: ok" in result.stdout or "1 passed" in result.stdout

            if verbose:
                print(" PASS" if passed else " FAIL")

            return passed
        except subprocess.TimeoutExpired:
            if verbose:
                print(" TIMEOUT")
            return False
        except Exception as e:
            if verbose:
                print(f" ERROR: {e}")
            return False

    def find_min_working_seed(self, bucket: int) -> Optional[int]:
        """Find minimum seed that works for a bucket using binary search."""
        print(f"\n  Finding minimum working seed for bucket {bucket}...")

        current = CURRENT_SEEDS[bucket]
        original = ORIGINAL_SEEDS[bucket]

        # Start with range [current-20, original+10]
        low = max(100, current - 20)  # Seeds shouldn't go below 100
        high = original + 10

        print(f"    Current seed: {current}, Original: {original}")
        print(f"    Search range: [{low}, {high}]")

        # First, check if current seed works
        if self.test_seed(bucket, current):
            print(f"    ✓ Current seed {current} works, searching for minimum...")
            # Binary search to find minimum
            result = current
            while low < current:
                mid = (low + current - 1) // 2
                if self.test_seed(bucket, mid):
                    current = mid
                    result = mid
                else:
                    low = mid + 1
            print(f"    → Minimum working seed: {result}")
            return result
        else:
            print(f"    ✗ Current seed {current} FAILS! Searching upward...")
            # Linear search upward to find first working seed
            for test_seed in range(current + 1, high + 1):
                if self.test_seed(bucket, test_seed):
                    print(f"    → Found working seed: {test_seed}")
                    return test_seed

            print(f"    ✗ ERROR: No working seed found up to {high}")
            return None

    def find_max_useful_seed(self, bucket: int, min_seed: int) -> int:
        """Find maximum seed that still provides benefit."""
        print(f"  Finding maximum useful seed...")

        # Binary search to find maximum working seed
        low = min_seed
        high = min_seed + 20
        result = min_seed

        print(f"    Starting from minimum: {min_seed}")
        print(f"    Testing range: [{low}, {high}]")

        while low <= high:
            mid = (low + high) // 2
            if self.test_seed(bucket, mid):
                result = mid
                low = mid + 1
            else:
                high = mid - 1

        print(f"    → Maximum working seed: {result}")
        return result

    def optimize_bucket(self, bucket: int) -> int:
        """Find optimal seed for a bucket."""
        print(f"\n{'='*60}")
        print(f"OPTIMIZING BUCKET {bucket}")
        print(f"  Original seed: {ORIGINAL_SEEDS[bucket]}")
        print(f"  Current seed:  {CURRENT_SEEDS[bucket]}")

        # Find minimum working seed
        min_seed = self.find_min_working_seed(bucket)
        if min_seed is None:
            print(f"\n  ✗ ERROR: Could not find working seed! Using original.")
            return ORIGINAL_SEEDS[bucket]  # Fallback to original

        # Find maximum useful seed
        max_seed = self.find_max_useful_seed(bucket, min_seed)

        # Choose optimal with safety margin
        # For invE=79 (4 iterations), add +2 safety margin
        optimal = min_seed + 2

        # But don't exceed the maximum that works
        optimal = min(optimal, max_seed)

        print(f"\n  SUMMARY:")
        print(f"    Min working: {min_seed}")
        print(f"    Max working: {max_seed}")
        print(f"    Optimal (min + 2 safety): {optimal}")

        if optimal != CURRENT_SEEDS[bucket]:
            print(f"    → CHANGE NEEDED: {CURRENT_SEEDS[bucket]} → {optimal}")
        else:
            print(f"    → Current seed is already optimal")

        return optimal

    def optimize_buckets(self, buckets: list):
        """Optimize seeds for specified buckets."""
        optimized = {}

        print(f"\n{'='*80}")
        print(f"OPTIMIZING {len(buckets)} BUCKET{'S' if len(buckets) != 1 else ''}")
        print(f"{'='*80}")

        for i, bucket in enumerate(buckets, 1):
            print(f"\n  [{i}/{len(buckets)}] Processing bucket {bucket}")
            optimized[bucket] = self.optimize_bucket(bucket)

        return optimized

    def generate_lookup_tables(self, seeds: dict) -> Tuple[int, int]:
        """Generate table_hi and table_lo from optimized seeds."""
        table_hi = 0
        table_lo = 0

        # Pack seeds into tables
        # Buckets 16-39 go into table_hi
        # Buckets 40-63 go into table_lo

        for i in range(16, 40):
            seed = seeds[i]
            # Position in table_hi
            shift = 390 + 10 * (0 - i)
            table_hi |= (seed & 0x3ff) << shift

        for i in range(40, 64):
            seed = seeds[i]
            # Position in table_lo
            shift = 390 + 10 * (24 - i)
            table_lo |= (seed & 0x3ff) << shift

        return table_hi, table_lo

    def print_results(self, optimized: dict):
        """Print optimization results."""
        print("\n" + "="*80)
        print("OPTIMIZATION RESULTS")
        print("="*80)

        if not optimized:
            print("No buckets were optimized.")
            return

        print("\nBucket | Original | Current | Optimized | Change from Current | Recommendation")
        print("-" * 80)

        for bucket in sorted(optimized.keys()):
            orig = ORIGINAL_SEEDS[bucket]
            curr = CURRENT_SEEDS[bucket]
            opt = optimized[bucket]
            change_from_curr = opt - curr

            if change_from_curr != 0:
                recommendation = f"CHANGE: {curr} → {opt}"
            else:
                recommendation = "OK (no change needed)"

            print(f"  {bucket:2d}   |   {orig:3d}    |   {curr:3d}   |    {opt:3d}    |       {change_from_curr:+3d}        | {recommendation}")

        # Only generate new tables if we have all buckets
        if len(optimized) == 48:
            # Fill in all seeds (using current for non-optimized)
            all_seeds = dict(CURRENT_SEEDS)
            all_seeds.update(optimized)

            table_hi, table_lo = self.generate_lookup_tables(all_seeds)

            print("\n" + "="*80)
            print("NEW LOOKUP TABLES")
            print("="*80)
            print(f"table_hi = 0x{table_hi:064x}")
            print(f"table_lo = 0x{table_lo:064x}")
        else:
            print("\n" + "="*80)
            print("NOTE: To generate new lookup tables, all 48 buckets must be optimized.")
            print("Use --bucket with all bucket numbers 16-63 or test in batches.")

def main():
    import sys

    optimizer = SeedOptimizer()

    # Parse command line arguments
    if "--bucket" in sys.argv:
        try:
            idx = sys.argv.index("--bucket")

            # Collect all bucket numbers after --bucket
            buckets = []
            for i in range(idx + 1, len(sys.argv)):
                if sys.argv[i].startswith("--"):
                    break
                bucket = int(sys.argv[i])
                if bucket < 16 or bucket > 63:
                    print(f"Error: Bucket {bucket} is out of range. Must be between 16 and 63.")
                    sys.exit(1)
                buckets.append(bucket)

            if not buckets:
                print("Error: --bucket requires at least one bucket number")
                print("Usage: python3 script/optimize_sqrt_seeds.py --bucket N [M ...]")
                sys.exit(1)

            # Remove duplicates and sort
            buckets = sorted(set(buckets))

        except ValueError as e:
            print(f"Error: Invalid bucket number")
            print("Usage: python3 script/optimize_sqrt_seeds.py --bucket N [M ...]")
            sys.exit(1)

    else:
        # Default: test problematic buckets around 44
        buckets = [42, 43, 44, 45, 46]
        print("No --bucket specified. Testing default problematic buckets: 42, 43, 44, 45, 46")

    # Run optimization
    optimized = optimizer.optimize_buckets(buckets)

    # Print results
    optimizer.print_results(optimized)

    # Clean up
    if os.path.exists(optimizer.test_contract_path):
        os.remove(optimizer.test_contract_path)

    print("\n✓ Done!")

if __name__ == "__main__":
    main()