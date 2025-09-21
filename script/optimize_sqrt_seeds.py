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
import random
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

    @staticmethod
    def verify_invE_and_bucket(x_hi_hex: str, x_lo_hex: str, expected_invE: int, expected_bucket: int) -> tuple:
        """Verify that a test input has the expected invE and bucket values.

        Returns: (actual_invE, actual_bucket, is_correct)
        """
        x_hi = int(x_hi_hex, 16) if isinstance(x_hi_hex, str) else x_hi_hex
        x_lo = int(x_lo_hex, 16) if isinstance(x_lo_hex, str) else x_lo_hex

        # Calculate invE = (clz(x_hi) + 1) >> 1
        if x_hi == 0:
            clz = 256
        else:
            clz = 256 - x_hi.bit_length()

        invE = (clz + 1) >> 1

        # Calculate bucket from mantissa
        # M is extracted by shifting right by 257 - (invE << 1) bits
        shift_amount = 257 - (invE * 2)

        # Combine x_hi and x_lo for full precision
        x_full = (x_hi << 256) | x_lo

        # Shift to get M
        M = x_full >> shift_amount

        # Get the bucket (top 6 bits of M)
        bucket_bits = (M >> 250) & 0x3F

        is_correct = (invE == expected_invE) and (bucket_bits == expected_bucket)
        return invE, bucket_bits, is_correct

    def generate_test_contract(self, bucket: int, seed: int, invEThreshold: int = 79) -> str:
        """Generate a test contract for a specific bucket and seed.

        Args:
            bucket: The bucket index to test
            seed: The seed value to test
            invEThreshold: The threshold for skipping the 5th N-R iteration (default=79)
                          This is scaffolding for future optimization where we'll search
                          for seeds that admit the lowest invE threshold.
        """

        # Generate test points at the exact threshold
        # We want the most challenging inputs that still skip the 5th iteration
        # That's when invE = invEThreshold exactly
        test_cases = []

        # Generate 5 test points across the bucket range, all with invE = invEThreshold
        for i in ["lo", "hi"] + ["rand"] * 20:
            x_hi, x_lo = self.generate_test_input_for_invE_and_position(bucket, invEThreshold, i)
            test_cases.append((x_hi, x_lo))

            # Verify the generated input
            actual_invE, actual_bucket, _ = self.verify_invE_and_bucket(x_hi, x_lo, invEThreshold, bucket)
            if actual_invE != invEThreshold or actual_bucket != bucket:
                print(f"        WARNING: Generated input {i} has invE={actual_invE} (expected {invEThreshold}), bucket={actual_bucket} (expected {bucket})")

        # Build test functions for each case
        test_functions = []
        for i, (x_hi, x_lo) in enumerate(test_cases):
            test_functions.append(f"""
    function testCase_{i}() private pure {{
        uint256 x_hi = {x_hi};
        uint256 x_lo = {x_lo};

        uint512 x = alloc().from(x_hi, x_lo);
        uint256 r = x.sqrt({bucket}, {seed}, {invEThreshold});

        // Verify: r^2 <= x < (r+1)^2
        (uint256 r2_lo, uint256 r2_hi) = SlowMath.fullMul(r, r);

        // Check r^2 <= x
        bool lower_ok = (r2_hi < x_hi) || (r2_hi == x_hi && r2_lo <= x_lo);
        require(lower_ok, "sqrt too high");

        // Check x < (r+1)^2
        if (~r == 0) {{
            bool at_threshold = x_hi > 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe || (x_hi == 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe && x_lo != 0);
            require(at_threshold, "sqrt too low (overflow)");
        }} else {{
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

    def generate_test_input_for_invE_and_position(self, bucket: int, invEThreshold: int, position: str):
        """Generate test input with specific invE value at different positions within bucket.

        Args:
            bucket: The bucket index to target
            invEThreshold: The desired invE value
            position: Position within bucket (0=low, 1=low+, 2=mid, 3=high-, 4=high)
        """
        # Calculate the shift amount for mantissa extraction
        shift_amount = 257 - (invEThreshold * 2)

        # We want M >> 250 = bucket, where M is the normalized mantissa
        # Construct M with bucket in the top 6 bits
        M = bucket << 250

        # Add bits for different positions within the bucket
        if position == "lo":
            # Lower boundary: just the minimum for this bucket
            pass  # M is already at minimum
        elif position == "hi":
            # Upper boundary: just before next bucket
            M = M | ((1 << 250) - 1)
        else:
            assert position == "rand"
            # if bucket == 44 and invEThreshold == 79:
            #     return ("0x000000000000000000000000000000000000000580398dae536e7fe242efe66a","0x0000000000000000001d9ad7c2a7ff6112e8bfd6cb5a1057f01519d7623fbd4a")
            M = M | random.getrandbits(250)

        # Calculate x = M << shift_amount
        # This gives us the value that, when shifted right by shift_amount, yields M
        x_full = M << shift_amount

        # Split into x_hi and x_lo (512-bit number)
        x_hi = (x_full >> 256) & ((1 << 256) - 1)
        x_lo = x_full & ((1 << 256) - 1)

        return (hex(x_hi), hex(x_lo))

    def test_seed(self, bucket: int, seed: int, verbose: bool = True, invEThreshold: int = 79) -> bool:
        """Test if a seed works for a bucket by running Solidity tests.

        Args:
            bucket: The bucket index to test
            seed: The seed value to test
            verbose: Whether to print progress messages
            invEThreshold: The threshold for skipping the 5th N-R iteration (default=79)
        """
        if verbose:
            print(f"    Testing seed {seed}...", end='', flush=True)

        # Write test contract
        with open(self.test_contract_path, 'w') as f:
            f.write(self.generate_test_contract(bucket, seed, invEThreshold))

        # Run forge test
        cmd = [
            "forge", "test",
            "--skip", "src/*",
            "--skip", "test/0.8.28/*",
            "--skip", "CrossChainReceiverFactory.t.sol",
            "--skip", "MultiCall.t.sol",
            "--match-path", self.test_contract_path,
            "--match-test", f"test_bucket_{bucket}_seed_{seed}",
            "--fail-fast",
            "-vv"
        ]

        try:
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=60,  # Increased timeout
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

    def find_min_working_seed(self, bucket: int, invEThreshold: int = 79) -> Optional[int]:
        """Find minimum seed that works for a bucket using binary search."""
        print(f"\n  Finding minimum working seed for bucket {bucket} (invEThreshold={invEThreshold})...")

        current = CURRENT_SEEDS[bucket]
        original = ORIGINAL_SEEDS[bucket]

        # Start with range [current-20, original+10]
        low = max(100, current - 20)  # Seeds shouldn't go below 100
        high = original + 10

        print(f"    Current seed: {current}, Original: {original}")
        print(f"    Search range: [{low}, {high}]")

        # First, check if current seed works
        if self.test_seed(bucket, current, True, invEThreshold):
            print(f"    ✓ Current seed {current} works, searching for minimum...")
            # Binary search to find minimum
            result = current
            while low < current:
                mid = (low + current - 1) // 2
                if self.test_seed(bucket, mid, True, invEThreshold):
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
                if self.test_seed(bucket, test_seed, True, invEThreshold):
                    print(f"    → Found working seed: {test_seed}")
                    return test_seed

            print(f"    ✗ ERROR: No working seed found up to {high}")
            return None

    def find_max_useful_seed(self, bucket: int, min_seed: int, invEThreshold: int = 79) -> int:
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
            if self.test_seed(bucket, mid, True, invEThreshold):
                result = mid
                low = mid + 1
            else:
                high = mid - 1

        print(f"    → Maximum working seed: {result}")
        return result

    def optimize_bucket(self, bucket: int, invEThreshold: int = 79) -> int:
        """Find optimal seed for a bucket."""
        print(f"\n{'='*60}")
        print(f"OPTIMIZING BUCKET {bucket}")
        print(f"  Original seed: {ORIGINAL_SEEDS[bucket]}")
        print(f"  Current seed:  {CURRENT_SEEDS[bucket]}")

        # Find minimum working seed
        min_seed = self.find_min_working_seed(bucket, invEThreshold)
        if min_seed is None:
            print(f"\n  ✗ ERROR: Could not find working seed! Using original.")
            return ORIGINAL_SEEDS[bucket]  # Fallback to original

        # Find maximum useful seed
        max_seed = self.find_max_useful_seed(bucket, min_seed, invEThreshold)

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

    def optimize_buckets(self, buckets: list, invEThreshold: int = 79):
        """Optimize seeds for specified buckets."""
        optimized = {}

        print(f"\n{'='*80}")
        print(f"OPTIMIZING {len(buckets)} BUCKET{'S' if len(buckets) != 1 else ''}")
        if invEThreshold != 79:
            print(f"Using invEThreshold={invEThreshold}")
        print(f"{'='*80}")

        for i, bucket in enumerate(buckets, 1):
            print(f"\n  [{i}/{len(buckets)}] Processing bucket {bucket}")
            optimized[bucket] = self.optimize_bucket(bucket, invEThreshold)

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

    # Parse invEThreshold parameter
    invEThreshold = 79  # Default threshold
    if "--threshold" in sys.argv:
        try:
            idx = sys.argv.index("--threshold")
            if idx + 1 >= len(sys.argv):
                print("Error: --threshold requires a value")
                sys.exit(1)
            invEThreshold = int(sys.argv[idx + 1])
            if invEThreshold < 1 or invEThreshold > 128:
                print(f"Error: Invalid threshold {invEThreshold}. Must be between 1 and 128.")
                sys.exit(1)
            print(f"Using invEThreshold={invEThreshold}")
        except ValueError:
            print("Error: --threshold must be an integer")
            sys.exit(1)

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
    optimized = optimizer.optimize_buckets(buckets, invEThreshold)

    # Print results
    optimizer.print_results(optimized)

    # Clean up
    if os.path.exists(optimizer.test_contract_path):
        os.remove(optimizer.test_contract_path)

    print("\n✓ Done!")

if __name__ == "__main__":
    main()
