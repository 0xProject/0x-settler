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
from enum import Enum

class TestResult(Enum):
    PASS = "PASS"
    FAIL = "FAIL"
    TIMEOUT = "TIMEOUT"

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
        result = self._test_seed_impl(bucket, seed, invEThreshold, fuzz_runs, verbose=False)
        return result == TestResult.PASS

    def test_seed(self, bucket: int, seed: int, invEThreshold: int = 79, verbose: bool = True) -> bool:
        """Test if a seed works for a bucket using Foundry's fuzzer."""
        result = self._test_seed_impl(bucket, seed, invEThreshold, self.fuzz_runs, verbose)
        return result == TestResult.PASS

    def _test_seed_impl(self, bucket: int, seed: int, invEThreshold: int, fuzz_runs: int, verbose: bool) -> TestResult:
        """Internal implementation for testing seeds with configurable parameters."""
        if verbose:
            print(f"    Testing seed {seed} with {fuzz_runs} fuzz runs...", end='', flush=True)

        start_time = time.time()

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

        # Scale timeout based on fuzz runs
        # Based on empirical data: ~125s for 1M runs, ~265s for 2M runs
        # Using 150 seconds per million runs + 60 second buffer for safety
        timeout_seconds = max(120, int(fuzz_runs / 1000000 * 150) + 60)

        try:
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=timeout_seconds,
                env={**os.environ, "FOUNDRY_FUZZ_RUNS": str(fuzz_runs)}
            )

            elapsed_time = time.time() - start_time

            if verbose:
                print(" [parsing results]", end='', flush=True)

            # Extract runs count if available
            runs_count = 0
            if "runs:" in result.stdout:
                try:
                    # The runs info is after "runs:" in format like "runs: 10, μ: 1234, ~: 1234)"
                    runs_line = result.stdout.split("runs:")[1].split(")")[0]
                    runs_count = int(runs_line.split(",")[0].strip())
                except Exception as e:
                    if "--debug" in sys.argv:
                        print(f"\n        DEBUG: Failed to parse runs count: {e}")
                        print(f"        DEBUG: Looking for 'runs:' in output...")
                        for line in result.stdout.split('\n'):
                            if 'runs:' in line:
                                print(f"        DEBUG: Found line: {line.strip()}")
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
                    print(f" SKIP (0 runs - no valid inputs found, {elapsed_time:.1f}s)")
                    # Debug: show a snippet of the output to understand why
                    if "--debug" in sys.argv:
                        print(f"        DEBUG: {result.stdout[:500]}...")
                elif passed:
                    print(f" PASS ({runs_count} runs, {elapsed_time:.1f}s)")
                else:
                    print(f" FAIL ({elapsed_time:.1f}s)")
                    # Enhanced error details for debugging
                    if "--debug" in sys.argv:
                        print(f"        Suite OK: {suite_ok}, Runs: {runs_count}")
                        print(f"        Timeout used: {timeout_seconds}s")
                    if result.stderr:
                        print(f"        STDERR: {result.stderr[:500]}...")
                    if "FAIL" in result.stdout or "reverted" in result.stdout:
                        # Extract failure reason
                        lines = result.stdout.split('\n')
                        for i, line in enumerate(lines):
                            if "reverted" in line or "Error:" in line or "failing test" in line:
                                print(f"        {line.strip()}")
                                # Show a few lines of context
                                if "--debug" in sys.argv and i > 0:
                                    print(f"        Context: {lines[i-1].strip()}")
                                break
                    # Save full output for debugging if requested
                    if "--save-output" in sys.argv:
                        output_file = f"forge_output_bucket{bucket}_seed{seed}_runs{fuzz_runs}.txt"
                        with open(output_file, 'w') as f:
                            f.write(f"Command: {' '.join(cmd)}\n")
                            f.write(f"Env: FOUNDRY_FUZZ_RUNS={fuzz_runs}\n")
                            f.write(f"Exit code: {result.returncode}\n")
                            f.write(f"Elapsed: {elapsed_time:.1f}s\n\n")
                            f.write("STDOUT:\n")
                            f.write(result.stdout)
                            f.write("\n\nSTDERR:\n")
                            f.write(result.stderr)
                        print(f"        Full output saved to {output_file}")

            # Return appropriate test result
            if passed and runs_count > 0:
                return TestResult.PASS
            else:
                return TestResult.FAIL

        except subprocess.TimeoutExpired:
            elapsed_time = time.time() - start_time
            if verbose:
                print(f" TIMEOUT (>{timeout_seconds}s after {elapsed_time:.1f}s)")
                print(f"        Fuzz runs: {fuzz_runs}, Timeout: {timeout_seconds}s")
                print(f"        Note: Timeout is not a test failure, just insufficient time to complete")
            return TestResult.TIMEOUT
        except Exception as e:
            if verbose:
                print(f" ERROR: {e}")
            return TestResult.FAIL

    def find_working_seed_spiral(self, bucket: int, invEThreshold: int, center_seed: int, max_distance: int = 10) -> Optional[int]:
        """Spiral outward from center_seed to find any working seed."""
        print(f"  Spiral search from seed {center_seed} (max distance {max_distance})...")

        # Try center first
        print(f"    Testing center seed {center_seed}...", end='', flush=True)
        if self.quick_test_seed(bucket, center_seed, invEThreshold, fuzz_runs=1000):
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
                if self.quick_test_seed(bucket, seed, invEThreshold, fuzz_runs=1000):
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
        working_seed = self.find_working_seed_spiral(bucket, invEThreshold, original_seed, max_distance=10)

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
            if self.quick_test_seed(bucket, mid, invEThreshold, fuzz_runs=1000):
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
            if self.quick_test_seed(bucket, mid, invEThreshold, fuzz_runs=1000):
                max_seed = mid
                left = mid + 1
                print(" works, search higher")
            else:
                right = mid - 1
                print(" fails, search lower")

        print(f"    Quick max seed found: {max_seed}")

        # Phase 2: Validation with full fuzz runs
        print(f"  Phase 2: Validating boundaries with full fuzz runs...")

        print(f"    Validating min seed {min_seed}...")
        min_result = self._test_seed_impl(bucket, min_seed, invEThreshold, self.fuzz_runs, verbose=True)
        if min_result == TestResult.TIMEOUT:
            print("    TIMEOUT during validation - cannot confirm seed validity")
            print("    Consider using fewer fuzz runs or increasing timeout")
            return None, None
        elif min_result == TestResult.FAIL:
            print("    FAILED validation!")
            # Linear scan upward with full validation until finding a working seed
            print(f"    Searching upward from {min_seed} for valid min seed...")
            found_valid = False
            for candidate in range(min_seed + 1, min_seed + 21):  # Try up to 20 seeds
                print(f"      Testing seed {candidate}...")
                result = self._test_seed_impl(bucket, candidate, invEThreshold, self.fuzz_runs, verbose=True)
                if result == TestResult.TIMEOUT:
                    print("      TIMEOUT - skipping remaining validation")
                    return None, None
                elif result == TestResult.PASS:
                    min_seed = candidate
                    print(f"      SUCCESS! Using {min_seed} as min seed")
                    found_valid = True
                    break
            if not found_valid:
                print("    Could not find valid min seed within 20 attempts")
                return None, None
        else:
            print("    Validated ✓")

        print(f"    Validating max seed {max_seed}...")
        max_result = self._test_seed_impl(bucket, max_seed, invEThreshold, self.fuzz_runs, verbose=True)
        if max_result == TestResult.TIMEOUT:
            print("    TIMEOUT during validation - cannot confirm seed validity")
            print("    Consider using fewer fuzz runs or increasing timeout")
            return None, None
        elif max_result == TestResult.FAIL:
            print("    FAILED validation!")
            # Linear scan downward with full validation until finding a working seed
            print(f"    Searching downward from {max_seed} for valid max seed...")
            found_valid = False
            for candidate in range(max_seed - 1, max_seed - 21, -1):  # Try up to 20 seeds
                print(f"      Testing seed {candidate}...")
                result = self._test_seed_impl(bucket, candidate, invEThreshold, self.fuzz_runs, verbose=True)
                if result == TestResult.TIMEOUT:
                    print("      TIMEOUT - skipping remaining validation")
                    return None, None
                elif result == TestResult.PASS:
                    max_seed = candidate
                    print(f"      SUCCESS! Using {max_seed} as max seed")
                    found_valid = True
                    break
            if not found_valid:
                print("    Could not find valid max seed within 20 attempts")
                return None, None
        else:
            print("    Validated ✓")

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

def main():
    # Parse command line arguments
    fuzz_runs = 10000
    invEThreshold = 79
    buckets = []

    # Special debug mode for testing a specific seed
    if "--debug-seed" in sys.argv:
        idx = sys.argv.index("--debug-seed")
        debug_bucket = int(sys.argv[idx + 1])
        debug_seed = int(sys.argv[idx + 2])

        print(f"DEBUG MODE: Testing bucket {debug_bucket}, seed {debug_seed}")
        print("=" * 60)

        if "--threshold" in sys.argv:
            idx = sys.argv.index("--threshold")
            invEThreshold = int(sys.argv[idx + 1])

        # Test with increasing fuzz runs
        test_runs = [100, 1000, 10000, 100000, 1000000]
        if "--fuzz-runs" in sys.argv:
            idx = sys.argv.index("--fuzz-runs")
            test_runs = [int(sys.argv[idx + 1])]

        optimizer = SeedOptimizer(fuzz_runs=10000)

        for runs in test_runs:
            print(f"\nTesting with {runs} fuzz runs:")
            result = optimizer._test_seed_impl(debug_bucket, debug_seed, invEThreshold, runs, verbose=True)
            print(f"  Result: {result.value}")

        return

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
