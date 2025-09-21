#!/usr/bin/env python3
"""
Optimize sqrt lookup table seeds using Foundry's fuzzer.

Usage:
    python3 script/optimize_sqrt_seeds.py --bucket N [--threshold T] [--fuzz-runs R]
    python3 script/optimize_sqrt_seeds.py                # Test problematic buckets (42-46)

Examples:
    python3 script/optimize_sqrt_seeds.py --bucket 44 --threshold 79 --fuzz-runs 100000
    python3 script/optimize_sqrt_seeds.py --bucket 44    # Use defaults
    python3 script/optimize_sqrt_seeds.py                # Test buckets 42-46

The script will:
1. Use Foundry's fuzzer to test seeds with random x inputs
2. Find the minimum and maximum working seeds for each bucket
3. Report exact seed ranges without fudge factors
"""

import subprocess
import os
import sys
import time
from typing import Tuple, Optional

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
    def __init__(self, fuzz_runs: int = 10000):
        self.template_path = "templates/SqrtSeedOptimizerFuzz.t.sol.template"
        self.test_contract_path = "test/0.8.25/SqrtSeedOptimizerGenerated.t.sol"
        self.fuzz_runs = fuzz_runs
        self.results = {}

    def generate_test_contract(self, bucket: int, seed: int, invEThreshold: int = 79) -> str:
        """Generate a test contract from the template with specific parameters."""
        # Read the template
        with open(self.template_path, 'r') as f:
            template = f.read()

        # Replace placeholders
        contract = template.replace("${BUCKET}", str(bucket))
        contract = contract.replace("${SEED}", str(seed))
        contract = contract.replace("${INV_E_THRESHOLD}", str(invEThreshold))

        # Also replace the contract name to avoid conflicts
        contract = contract.replace("SqrtSeedOptimizerFuzz", f"SqrtSeedOptimizerBucket{bucket}Seed{seed}")

        return contract

    def quick_test_seed(self, bucket: int, seed: int, invEThreshold: int = 79, fuzz_runs: int = 100) -> bool:
        """Quick test with fewer fuzz runs for discovery phase."""
        return self._test_seed_impl(bucket, seed, invEThreshold, fuzz_runs, verbose=False)

    def test_seed(self, bucket: int, seed: int, invEThreshold: int = 79, verbose: bool = True) -> bool:
        """Test if a seed works for a bucket using Foundry's fuzzer."""
        return self._test_seed_impl(bucket, seed, invEThreshold, self.fuzz_runs, verbose)

    def _test_seed_impl(self, bucket: int, seed: int, invEThreshold: int, fuzz_runs: int, verbose: bool) -> bool:
        """Internal implementation for testing seeds with configurable parameters."""
        if verbose:
            print(f"    Testing seed {seed} with {fuzz_runs} fuzz runs...", end='', flush=True)

        # Generate and write test contract
        if verbose:
            print(" [generating contract]", end='', flush=True)
        contract_code = self.generate_test_contract(bucket, seed, invEThreshold)
        with open(self.test_contract_path, 'w') as f:
            f.write(contract_code)

        # Run forge test with fuzzing
        cmd = [
            "forge", "test",
            "--skip", "src/*",
            "--skip", "test/0.8.28/*",
            "--skip", "CrossChainReceiverFactory.t.sol",
            "--skip", "MultiCall.t.sol",
            "--match-path", self.test_contract_path,
            "--match-test", "testFuzz_sqrt_seed",
            "-vv"
        ]

        if verbose:
            print(" [running forge test]", end='', flush=True)

        try:
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=120,  # 2 minutes timeout
                env={**os.environ, "FOUNDRY_FUZZ_RUNS": str(fuzz_runs)}
            )

            if verbose:
                print(" [parsing results]", end='', flush=True)

            # Extract runs count if available
            runs_count = 0
            if "runs:" in result.stdout:
                try:
                    # The runs info is after "runs:" in format like "runs: 10, μ: 1234, ~: 1234)"
                    runs_line = result.stdout.split("runs:")[1].split(")")[0]
                    runs_count = int(runs_line.split(",")[0].strip())
                except:
                    runs_count = 0

            # Check if test actually passed - be very specific!
            # Look for "Suite result: ok" and NOT "Suite result: FAILED"
            suite_ok = "Suite result: ok" in result.stdout and "Suite result: FAILED" not in result.stdout

            # Additional check: if we see "failing test" it definitely failed
            if "failing test" in result.stdout.lower():
                suite_ok = False

            # Require at least 1 successful run for a true pass
            passed = suite_ok and runs_count > 0

            if verbose:
                if suite_ok and runs_count == 0:
                    print(f" SKIP (0 runs - no valid inputs found)")
                    # Debug: show a snippet of the output to understand why
                    if "--debug" in sys.argv:
                        print(f"        DEBUG: {result.stdout[:500]}...")
                elif passed:
                    print(f" PASS ({runs_count} runs)")
                else:
                    print(" FAIL")
                    # Show some error details for debugging
                    if result.stderr:
                        print(f"        STDERR: {result.stderr[:200]}...")
                    if "FAIL" in result.stdout or "reverted" in result.stdout:
                        # Extract failure reason
                        lines = result.stdout.split('\n')
                        for line in lines:
                            if "reverted" in line or "Error:" in line:
                                print(f"        {line.strip()}")
                                break

            # Treat 0 runs as a failure - we need actual test coverage
            return passed and runs_count > 0

        except subprocess.TimeoutExpired:
            if verbose:
                print(" TIMEOUT (>120s)")
            return False
        except Exception as e:
            if verbose:
                print(f" ERROR: {e}")
            return False

    def find_working_seed_spiral(self, bucket: int, invEThreshold: int, center_seed: int, max_distance: int = 50) -> Optional[int]:
        """Spiral outward from center_seed to find any working seed."""
        print(f"  Spiral search from seed {center_seed} (max distance {max_distance})...")

        # Try center first
        print(f"    Testing center seed {center_seed}...", end='', flush=True)
        if self.quick_test_seed(bucket, center_seed, invEThreshold, fuzz_runs=200):
            print(" WORKS!")
            return center_seed
        else:
            print(" fails")

        # Spiral outward
        for distance in range(1, max_distance + 1):
            candidates = []

            # Add +distance if within bounds
            if center_seed + distance <= 800:
                candidates.append((center_seed + distance, f"+{distance}"))

            # Add -distance if within bounds
            if center_seed - distance >= 300:
                candidates.append((center_seed - distance, f"-{distance}"))

            # Test candidates for this distance
            for seed, offset in candidates:
                print(f"    Testing {center_seed}{offset} = {seed}...", end='', flush=True)
                if self.quick_test_seed(bucket, seed, invEThreshold, fuzz_runs=200):
                    print(" WORKS!")
                    return seed
                else:
                    print(" fails")

        print(f"    No working seed found within distance {max_distance} of {center_seed}")
        return None

    def find_seed_range(self, bucket: int, invEThreshold: int = 79) -> Tuple[Optional[int], Optional[int]]:
        """Find the minimum and maximum working seeds for a bucket."""
        start_time = time.time()
        print(f"\nFinding seed range for bucket {bucket} (invEThreshold={invEThreshold}):")

        def check_timeout():
            if time.time() - start_time > 600:  # 10 minute timeout
                print(f"  TIMEOUT: Search for bucket {bucket} exceeded 10 minutes")
                return True
            return False

        # Start from ORIGINAL seed (more likely to be good than current modified seed)
        original_seed = ORIGINAL_SEEDS.get(bucket, 450)
        current_seed = CURRENT_SEEDS.get(bucket, 450)

        print(f"  Original seed: {original_seed}, Current seed: {current_seed}")

        # Try spiral search from original seed first
        working_seed = self.find_working_seed_spiral(bucket, invEThreshold, original_seed, max_distance=25)

        # If original doesn't work, try current seed
        if working_seed is None and original_seed != current_seed:
            print(f"  Original seed region failed, trying current seed region...")
            working_seed = self.find_working_seed_spiral(bucket, invEThreshold, current_seed, max_distance=25)

        # If both fail, try broader search around middle range
        if working_seed is None:
            print(f"  Both seed regions failed, trying broader search...")
            middle_seed = 500  # Middle of typical range
            working_seed = self.find_working_seed_spiral(bucket, invEThreshold, middle_seed, max_distance=100)

        if working_seed is None:
            print(f"  ERROR: No working seed found for bucket {bucket}")
            return None, None

        current = working_seed
        print(f"  ✓ Found working seed: {current}")

        # Phase 1: Quick discovery of boundaries with fewer fuzz runs
        print(f"  Phase 1: Quick discovery of seed boundaries...")

        # Binary search for minimum working seed (quick)
        print(f"    Finding min seed (range {300}-{current}) with quick tests...")
        left, right = 300, current
        min_seed = current

        while left <= right:
            if check_timeout():
                return None, None
            mid = (left + right) // 2
            print(f"      Testing [{left}, {right}] → {mid}...", end='', flush=True)
            if self.quick_test_seed(bucket, mid, invEThreshold, fuzz_runs=100):
                min_seed = mid
                right = mid - 1
                print(" works, search lower")
            else:
                left = mid + 1
                print(" fails, search higher")

        print(f"    Quick min seed found: {min_seed}")

        # Binary search for maximum working seed (quick)
        print(f"    Finding max seed (range {current}-800) with quick tests...")
        left, right = current, 800
        max_seed = current

        while left <= right:
            if check_timeout():
                return None, None
            mid = (left + right) // 2
            print(f"      Testing [{left}, {right}] → {mid}...", end='', flush=True)
            if self.quick_test_seed(bucket, mid, invEThreshold, fuzz_runs=100):
                max_seed = mid
                left = mid + 1
                print(" works, search higher")
            else:
                right = mid - 1
                print(" fails, search lower")

        print(f"    Quick max seed found: {max_seed}")

        # Phase 2: Validation with full fuzz runs
        print(f"  Phase 2: Validating boundaries with full fuzz runs...")

        print(f"    Validating min seed {min_seed}...", end='', flush=True)
        if not self.test_seed(bucket, min_seed, invEThreshold, verbose=False):
            print(" FAILED validation!")
            # Try a slightly higher seed
            for candidate in range(min_seed + 1, min_seed + 5):
                if self.test_seed(bucket, candidate, invEThreshold, verbose=False):
                    min_seed = candidate
                    print(f" Using {min_seed} instead")
                    break
            else:
                print(" Could not find valid min seed")
                return None, None
        else:
            print(" validated ✓")

        print(f"    Validating max seed {max_seed}...", end='', flush=True)
        if not self.test_seed(bucket, max_seed, invEThreshold, verbose=False):
            print(" FAILED validation!")
            # Try a slightly lower seed
            for candidate in range(max_seed - 1, max_seed - 5, -1):
                if self.test_seed(bucket, candidate, invEThreshold, verbose=False):
                    max_seed = candidate
                    print(f" Using {max_seed} instead")
                    break
            else:
                print(" Could not find valid max seed")
                return None, None
        else:
            print(" validated ✓")

        print(f"  ✓ Final range: min={min_seed}, max={max_seed}, span={max_seed - min_seed + 1}")

        return min_seed, max_seed

    def optimize_buckets(self, buckets: list, invEThreshold: int = 79):
        """Optimize seeds for multiple buckets."""
        print(f"\nOptimizing seeds for buckets {buckets}")
        print(f"Using invEThreshold={invEThreshold}, fuzz_runs={self.fuzz_runs}")
        print("=" * 60)

        for bucket in buckets:
            min_seed, max_seed = self.find_seed_range(bucket, invEThreshold)

            if min_seed is not None and max_seed is not None:
                self.results[bucket] = {
                    'min': min_seed,
                    'max': max_seed,
                    'current': CURRENT_SEEDS.get(bucket, 0),
                    'original': ORIGINAL_SEEDS.get(bucket, 0),
                    'invEThreshold': invEThreshold
                }
                print(f"  Bucket {bucket}: min={min_seed}, max={max_seed}, range={max_seed - min_seed + 1}")
            else:
                print(f"  Bucket {bucket}: FAILED to find valid range")

        self.print_summary()

    def print_summary(self):
        """Print summary of results."""
        if not self.results:
            return

        print("\n" + "=" * 60)
        print("SUMMARY OF RESULTS")
        print("=" * 60)

        print("\nSeed Ranges (exact, no fudge factor):")
        print("Bucket | Min  | Max  | Range | Current | Original | Status")
        print("-------|------|------|-------|---------|----------|--------")

        for bucket in sorted(self.results.keys()):
            r = self.results[bucket]
            status = "OK" if r['min'] <= r['current'] <= r['max'] else "FAIL"
            print(f"  {bucket:3d}  | {r['min']:4d} | {r['max']:4d} | {r['max'] - r['min'] + 1:5d} | "
                  f"{r['current']:7d} | {r['original']:8d} | {status}")

        print("\nRecommended Seeds (using minimum valid seed):")
        print("{", end="")
        for i, bucket in enumerate(range(16, 64)):
            if i > 0:
                print(",", end="")
            if i % 8 == 0:
                print("\n    ", end="")
            else:
                print(" ", end="")

            if bucket in self.results:
                # Use minimum seed (most conservative)
                seed = self.results[bucket]['min']
            else:
                # Keep current seed if not tested
                seed = CURRENT_SEEDS.get(bucket, 0)

            print(f"{bucket}: {seed}", end="")
        print("\n}")


def main():
    # Parse command line arguments
    fuzz_runs = 10000
    invEThreshold = 79
    buckets = []

    if "--fuzz-runs" in sys.argv:
        idx = sys.argv.index("--fuzz-runs")
        fuzz_runs = int(sys.argv[idx + 1])

    if "--threshold" in sys.argv:
        idx = sys.argv.index("--threshold")
        invEThreshold = int(sys.argv[idx + 1])

    if "--bucket" in sys.argv:
        idx = sys.argv.index("--bucket")
        # Collect all bucket numbers after --bucket until we hit another flag or end
        for i in range(idx + 1, len(sys.argv)):
            if sys.argv[i].startswith("--"):
                break
            buckets.append(int(sys.argv[i]))
    else:
        # Default: test problematic buckets
        buckets = [42, 43, 44, 45, 46]

    # Run optimization
    optimizer = SeedOptimizer(fuzz_runs=fuzz_runs)
    optimizer.optimize_buckets(buckets, invEThreshold)


if __name__ == "__main__":
    main()