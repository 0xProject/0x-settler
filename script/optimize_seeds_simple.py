#!/usr/bin/env python3
"""
Simplified seed optimizer using the modified sqrt function with override parameters.
Tests with the known failing input that has invE=79 and bucket=44.
"""

import subprocess
import os
import sys

# Known failing input values
FAIL_X_HI = "0x000000000000000000000000000000000000000580398dae536e7fe242efe66a"
FAIL_X_LO = "0x0000000000000000001d9ad7c2a7ff6112e8bfd6cb5a1057f01519d7623fbd4a"

# Current seeds from the modified lookup table
CURRENT_SEEDS = {
    16: 713, 17: 692, 18: 673, 19: 655, 20: 638, 21: 623, 22: 608, 23: 595,
    24: 583, 25: 571, 26: 560, 27: 549, 28: 539, 29: 530, 30: 521, 31: 513,
    32: 505, 33: 497, 34: 490, 35: 483, 36: 476, 37: 469, 38: 463, 39: 457,
    40: 451, 41: 446, 42: 441, 43: 435, 44: 430, 45: 426, 46: 421, 47: 417,
    48: 412, 49: 408, 50: 404, 51: 400, 52: 396, 53: 392, 54: 389, 55: 385,
    56: 382, 57: 378, 58: 375, 59: 372, 60: 369, 61: 366, 62: 363, 63: 360
}

def test_seed(bucket: int, seed: int, verbose: bool = True) -> bool:
    """Test if a seed works for the given bucket using the known failing input."""

    if verbose:
        print(f"    Testing seed {seed}...", end='', flush=True)

    # Create test file
    test_file = f"/tmp/test_bucket_{bucket}_seed_{seed}.sol"
    with open(test_file, 'w') as f:
        f.write(f"""// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {{uint512, alloc}} from "src/utils/512Math.sol";
import {{SlowMath}} from "test/0.8.25/SlowMath.sol";
import {{Test}} from "@forge-std/Test.sol";

contract TestBucket{bucket}Seed{seed} is Test {{
    function test() public pure {{
        uint256 x_hi = {FAIL_X_HI};
        uint256 x_lo = {FAIL_X_LO};

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
    }}
}}""")

    # Run forge test
    cmd = [
        "forge", "test",
        "--match-path", test_file,
        "-vv"
    ]

    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=10,
            env={**os.environ, "FOUNDRY_FUZZ_RUNS": "10000"}
        )

        # Clean up
        if os.path.exists(test_file):
            os.remove(test_file)

        # Check if test passed
        passed = "1 passed" in result.stdout or "ok" in result.stdout.lower()

        if verbose:
            print(" PASS" if passed else " FAIL")

        return passed
    except Exception as e:
        if verbose:
            print(f" ERROR: {e}")
        if os.path.exists(test_file):
            os.remove(test_file)
        return False

def find_optimal_seed(bucket: int) -> int:
    """Find the optimal seed for a bucket using binary search."""

    print(f"\n{'='*60}")
    print(f"OPTIMIZING BUCKET {bucket}")
    print(f"  Current seed: {CURRENT_SEEDS[bucket]}")

    # Quick validation
    print("\n  Validating known values:")
    if bucket == 44:
        # Test known failing seed
        if test_seed(44, 430):
            print("    WARNING: Seed 430 should fail but passed!")
        else:
            print("    ✓ Seed 430 correctly fails")

    # Binary search for minimum working seed
    print("\n  Finding minimum working seed:")
    low = max(100, CURRENT_SEEDS[bucket] - 20)
    high = CURRENT_SEEDS[bucket] + 20

    # First check if current seed works
    if test_seed(bucket, CURRENT_SEEDS[bucket]):
        # Binary search downward
        result = CURRENT_SEEDS[bucket]
        while low < result:
            mid = (low + result - 1) // 2
            if test_seed(bucket, mid):
                result = mid
            else:
                low = mid + 1
        min_seed = result
    else:
        # Linear search upward
        min_seed = None
        for seed in range(CURRENT_SEEDS[bucket] + 1, high + 1):
            if test_seed(bucket, seed):
                min_seed = seed
                break

    if min_seed is None:
        print(f"    ✗ ERROR: No working seed found!")
        return CURRENT_SEEDS[bucket]

    # Add safety margin
    optimal = min_seed + 2

    print(f"\n  RESULTS:")
    print(f"    Minimum working: {min_seed}")
    print(f"    Optimal (+2 safety): {optimal}")

    return optimal

def main():
    if "--quick" in sys.argv:
        print("="*80)
        print("QUICK TEST MODE")
        print("="*80)

        print("\nTesting bucket 44 with known seeds:")
        print("  Seed 430 (should fail):", "FAIL" if not test_seed(44, 430, False) else "UNEXPECTED PASS")
        print("  Seed 434 (original):", "PASS" if test_seed(44, 434, False) else "FAIL")
        print("  Seed 436 (with margin):", "PASS" if test_seed(44, 436, False) else "FAIL")

    else:
        # Find optimal seed for bucket 44
        optimal_44 = find_optimal_seed(44)

        print("\n" + "="*80)
        print("RECOMMENDATION")
        print("="*80)
        print(f"Bucket 44: Change seed from {CURRENT_SEEDS[44]} to {optimal_44}")

        # Test other nearby buckets if requested
        if "--nearby" in sys.argv:
            for bucket in [42, 43, 45, 46]:
                optimal = find_optimal_seed(bucket)
                if optimal != CURRENT_SEEDS[bucket]:
                    print(f"Bucket {bucket}: Change seed from {CURRENT_SEEDS[bucket]} to {optimal}")

    print("\n✓ Done!")

if __name__ == "__main__":
    main()