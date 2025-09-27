#!/usr/bin/env python3
"""
Find the minimum invEThreshold for sqrt optimization.

This script uses binary search to find the minimum working invEThreshold value
for each bucket, then collects seed ranges for both the minimum threshold and
minimum+1 for safety.

Usage:
    python3 script/find_minimum_threshold.py --bucket N [--fuzz-runs R]
    python3 script/find_minimum_threshold.py --all [--fuzz-runs R]

Examples:
    python3 script/find_minimum_threshold.py --bucket 44 --fuzz-runs 100000
    python3 script/find_minimum_threshold.py --all --fuzz-runs 10000
"""

import subprocess
import os
import sys
import time
import re
import json
from typing import Tuple, Optional, Dict, Any

class ThresholdOptimizer:
    def __init__(self, bucket: int, fuzz_runs: int = 10000):
        self.bucket = bucket
        self.fuzz_runs = fuzz_runs
        self.script_path = "script/optimize_sqrt_seeds.py"

    def test_threshold(self, threshold: int) -> Tuple[str, Optional[int], Optional[int]]:
        """
        Test if a threshold works by calling optimize_sqrt_seeds.py.

        Returns:
            (status, min_seed, max_seed) - status is 'SUCCESS', 'FAILED', or 'TIMEOUT'
        """
        print(f"    Testing invEThreshold {threshold}...", end='', flush=True)

        try:
            # Run the existing optimize_sqrt_seeds.py script
            cmd = [
                "python3", self.script_path,
                "--bucket", str(self.bucket),
                "--threshold", str(threshold),
                "--fuzz-runs", str(self.fuzz_runs)
            ]

            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=3600,  # 60 minute timeout (increased for 2M+ fuzz runs)
                cwd="/home/user/Documents/0x-settler"
            )

            # Parse output to extract results
            output = result.stdout

            # Look for the final results line like:
            # "Bucket 44: min=431, max=438, range=8"
            bucket_pattern = rf"Bucket\s+{self.bucket}:\s+min=(\d+),\s+max=(\d+),\s+range=\d+"
            match = re.search(bucket_pattern, output)

            if match:
                min_seed = int(match.group(1))
                max_seed = int(match.group(2))
                print(f" SUCCESS (seeds {min_seed}-{max_seed})")
                return "SUCCESS", min_seed, max_seed
            else:
                # Check for timeout
                if "TIMEOUT" in output and "cannot confirm seed validity" in output:
                    print(" TIMEOUT (validation incomplete)")
                    return "TIMEOUT", None, None
                # Check if it failed explicitly
                elif f"Bucket {self.bucket}: FAILED" in output:
                    print(" FAILED (no valid seeds)")
                    return "FAILED", None, None
                else:
                    # Unexpected output format
                    print(" UNKNOWN (unexpected output)")
                    if "--debug" in sys.argv:
                        print(f"        DEBUG OUTPUT (first 500 chars): {output[:500]}...")
                        print(f"        DEBUG OUTPUT (last 500 chars): ...{output[-500:]}")
                    return "FAILED", None, None

        except subprocess.TimeoutExpired:
            print(f" TIMEOUT (>{self.fuzz_runs/1000:.0f}k runs took >{script_timeout}s)")
            return "TIMEOUT", None, None
        except Exception as e:
            print(f" ERROR: {e}")
            return "FAILED", None, None

    def find_minimum_threshold(self) -> int:
        """
        Use binary search to find the minimum working invEThreshold.

        Returns:
            The minimum threshold that produces valid seed ranges
        """
        print(f"\nFinding minimum invEThreshold for bucket {self.bucket}:")
        print(f"  Binary search in range [1, 79] with {self.fuzz_runs} fuzz runs...")

        left, right = 1, 79
        last_working = 79  # We know 79 works

        while left <= right:
            mid = (left + right) // 2
            status, _, _ = self.test_threshold(mid)

            if status == "SUCCESS":
                last_working = mid
                right = mid - 1  # Try lower
                print(f"      → Threshold {mid} works, searching lower...")
            elif status == "TIMEOUT":
                print(f"      → Threshold {mid} timed out, treating as uncertain")
                print(f"      → Skipping to higher threshold to avoid more timeouts")
                left = mid + 1   # Try higher
            else:  # FAILED
                left = mid + 1   # Try higher
                print(f"      → Threshold {mid} fails, searching higher...")

        print(f"  ✓ Minimum working threshold: {last_working}")
        return last_working

    def collect_results(self) -> Dict[str, Any]:
        """
        Find minimum threshold and collect seed ranges for min and min+1.

        Returns:
            Dictionary containing all collected data
        """
        # Find the minimum threshold
        min_threshold = self.find_minimum_threshold()

        print(f"\nCollecting seed ranges:")

        # Get detailed seed range for minimum threshold
        print(f"  Getting seed range for minimum threshold {min_threshold}...")
        status_min, min_seed_min, max_seed_min = self.test_threshold(min_threshold)

        # Get detailed seed range for minimum+1 threshold (safety margin)
        safety_threshold = min_threshold + 1
        print(f"  Getting seed range for safety threshold {safety_threshold}...")
        status_safety, min_seed_safety, max_seed_safety = self.test_threshold(safety_threshold)

        results = {
            'bucket': self.bucket,
            'min_threshold': min_threshold,
            'min_threshold_status': status_min,
            'min_threshold_seeds': (min_seed_min, max_seed_min) if status_min == "SUCCESS" else None,
            'safety_threshold': safety_threshold,
            'safety_threshold_status': status_safety,
            'safety_threshold_seeds': (min_seed_safety, max_seed_safety) if status_safety == "SUCCESS" else None,
            'fuzz_runs': self.fuzz_runs
        }

        return results

def print_results(results: Dict[str, Any]):
    """Print formatted results."""
    bucket = results['bucket']
    min_thresh = results['min_threshold']
    safety_thresh = results['safety_threshold']

    print(f"\n{'='*60}")
    print(f"BUCKET {bucket} THRESHOLD OPTIMIZATION RESULTS")
    print(f"{'='*60}")

    print(f"Minimum working invEThreshold: {min_thresh}")
    status = results.get('min_threshold_status', 'UNKNOWN')
    if status == "TIMEOUT":
        print(f"  Status: TIMEOUT - validation incomplete")
        print(f"  Consider using fewer fuzz runs or increasing timeout")
    elif results['min_threshold_seeds']:
        min_seed, max_seed = results['min_threshold_seeds']
        range_size = max_seed - min_seed + 1
        middle_seed = (min_seed + max_seed) // 2
        print(f"  Seed range at threshold {min_thresh}: [{min_seed}, {max_seed}] (size: {range_size})")
        print(f"  Recommended seed: {middle_seed} (middle of range)")
    else:
        print(f"  ERROR: Could not get seed range for minimum threshold!")

    print(f"\nSafety threshold (min+1): {safety_thresh}")
    status = results.get('safety_threshold_status', 'UNKNOWN')
    if status == "TIMEOUT":
        print(f"  Status: TIMEOUT - validation incomplete")
        print(f"  Consider using fewer fuzz runs or increasing timeout")
    elif results['safety_threshold_seeds']:
        min_seed, max_seed = results['safety_threshold_seeds']
        range_size = max_seed - min_seed + 1
        middle_seed = (min_seed + max_seed) // 2
        print(f"  Seed range at threshold {safety_thresh}: [{min_seed}, {max_seed}] (size: {range_size})")
        print(f"  Recommended seed: {middle_seed} (middle of range)")
    else:
        print(f"  ERROR: Could not get seed range for safety threshold!")

    print(f"\nTesting parameters: {results['fuzz_runs']} fuzz runs")

def save_to_json(results_list: list, filename: str = "threshold_optimization_results.json"):
    """Save or append results to JSON file."""

    # Load existing data if file exists
    existing_data = {}
    if os.path.exists(filename):
        try:
            with open(filename, 'r') as f:
                existing_data = json.load(f)
        except (json.JSONDecodeError, FileNotFoundError):
            existing_data = {}

    # Add timestamp and metadata if this is a new file
    if 'metadata' not in existing_data:
        existing_data['metadata'] = {
            'created': time.strftime('%Y-%m-%d %H:%M:%S'),
            'description': 'Sqrt threshold optimization results',
            'format_version': '1.0'
        }

    existing_data['metadata']['last_updated'] = time.strftime('%Y-%m-%d %H:%M:%S')

    # Initialize buckets section if it doesn't exist
    if 'buckets' not in existing_data:
        existing_data['buckets'] = {}

    # Add/update results for each bucket
    for result in results_list:
        bucket_key = str(result['bucket'])

        # Prepare the new test result
        new_test_result = {
            'min_threshold': result['min_threshold'],
            'min_threshold_status': result.get('min_threshold_status', 'UNKNOWN'),
            'safety_threshold': result['safety_threshold'],
            'safety_threshold_status': result.get('safety_threshold_status', 'UNKNOWN'),
            'fuzz_runs_used': result['fuzz_runs'],
            'tested_at': time.strftime('%Y-%m-%d %H:%M:%S')
        }

        # Add seed ranges if they exist
        if result['min_threshold_seeds']:
            min_seed, max_seed = result['min_threshold_seeds']
            new_test_result['min_threshold_seeds'] = {
                'min': min_seed,
                'max': max_seed,
                'range_size': max_seed - min_seed + 1,
                'recommended': (min_seed + max_seed) // 2
            }
        else:
            new_test_result['min_threshold_seeds'] = None

        if result['safety_threshold_seeds']:
            min_seed, max_seed = result['safety_threshold_seeds']
            new_test_result['safety_threshold_seeds'] = {
                'min': min_seed,
                'max': max_seed,
                'range_size': max_seed - min_seed + 1,
                'recommended': (min_seed + max_seed) // 2
            }
        else:
            new_test_result['safety_threshold_seeds'] = None

        # Initialize or update bucket data
        if bucket_key not in existing_data['buckets']:
            # New bucket
            existing_data['buckets'][bucket_key] = {
                'bucket': result['bucket'],
                'history': [new_test_result],
                'latest': new_test_result
            }
        else:
            # Existing bucket - add to history
            existing_data['buckets'][bucket_key]['history'].append(new_test_result)
            existing_data['buckets'][bucket_key]['latest'] = new_test_result

    # Write back to file
    with open(filename, 'w') as f:
        json.dump(existing_data, f, indent=2, sort_keys=True)

    print(f"\n✓ Results saved to {filename}")
    print(f"  Total buckets in database: {len(existing_data['buckets'])}")

def load_and_print_summary(filename: str = "threshold_optimization_results.json"):
    """Load and print a summary of all results from JSON file."""
    if not os.path.exists(filename):
        print(f"No results file found at {filename}")
        return

    with open(filename, 'r') as f:
        data = json.load(f)

    print(f"\n{'='*80}")
    print(f"COMPLETE THRESHOLD OPTIMIZATION SUMMARY")
    print(f"{'='*80}")
    print(f"Last updated: {data['metadata'].get('last_updated', 'Unknown')}")
    print(f"Total buckets tested: {len(data['buckets'])}")

    print(f"\nBucket | Min Thresh | Min Seeds     | Rec | Safety Thresh | Safety Seeds  | Rec")
    print(f"-------|------------|---------------|-----|---------------|---------------|----")

    for bucket_key in sorted(data['buckets'].keys(), key=int):
        bucket_data = data['buckets'][bucket_key]
        bucket = bucket_data['bucket']
        latest = bucket_data['latest']
        history_count = len(bucket_data['history'])

        min_thresh = latest['min_threshold']
        safety_thresh = latest['safety_threshold']

        # Min threshold data
        min_seeds = latest['min_threshold_seeds']
        if min_seeds:
            min_range = f"[{min_seeds['min']}, {min_seeds['max']}]"
            min_rec = str(min_seeds['recommended'])
        else:
            min_range = "FAILED"
            min_rec = "N/A"

        # Safety threshold data
        safety_seeds = latest['safety_threshold_seeds']
        if safety_seeds:
            safety_range = f"[{safety_seeds['min']}, {safety_seeds['max']}]"
            safety_rec = str(safety_seeds['recommended'])
        else:
            safety_range = "FAILED"
            safety_rec = "N/A"

        tested_at = latest['tested_at']
        fuzz_runs = latest['fuzz_runs_used']

        print(f"   {bucket:2d}  |     {min_thresh:2d}     | {min_range:13s} | {min_rec:3s} |      {safety_thresh:2d}       | {safety_range:13s} | {safety_rec:3s}")
        # Show test info for all buckets
        if history_count > 1:
            print(f"       | (tested {history_count} times, latest: {tested_at} with {fuzz_runs} runs)")
        else:
            print(f"       | (tested: {tested_at} with {fuzz_runs} runs)")

    # Print some statistics (using latest results only)
    successful_buckets = [b['latest'] for b in data['buckets'].values()
                         if b['latest']['min_threshold_seeds'] is not None]

    if successful_buckets:
        min_thresholds = [b['min_threshold'] for b in successful_buckets]
        avg_min_thresh = sum(min_thresholds) / len(min_thresholds)

        print(f"\n{'='*80}")
        print(f"STATISTICS (based on latest results)")
        print(f"{'='*80}")
        print(f"Successful bucket tests: {len(successful_buckets)}")
        print(f"Average minimum threshold: {avg_min_thresh:.1f}")
        print(f"Lowest minimum threshold: {min(min_thresholds)}")
        print(f"Highest minimum threshold: {max(min_thresholds)}")

        # Count single-seed buckets
        single_seed_count = sum(1 for b in successful_buckets
                               if b['min_threshold_seeds']['range_size'] == 1)
        print(f"Buckets with single valid seed: {single_seed_count}/{len(successful_buckets)} ({100*single_seed_count/len(successful_buckets):.1f}%)")

        # Show historical test count
        total_tests = sum(len(b['history']) for b in data['buckets'].values())
        print(f"Total test runs across all buckets: {total_tests}")

        # Show buckets with multiple test runs
        multi_test_buckets = [b for b in data['buckets'].values() if len(b['history']) > 1]
        if multi_test_buckets:
            print(f"Buckets with multiple test runs: {len(multi_test_buckets)}")
            for bucket_data in multi_test_buckets:
                bucket_num = bucket_data['bucket']
                test_count = len(bucket_data['history'])
                fuzz_runs = [h['fuzz_runs_used'] for h in bucket_data['history']]
                print(f"  Bucket {bucket_num}: {test_count} tests with fuzz_runs {fuzz_runs}")

def main():
    # Parse command line arguments
    fuzz_runs = 10000
    buckets = []
    json_filename = "threshold_optimization_results.json"

    if "--fuzz-runs" in sys.argv:
        idx = sys.argv.index("--fuzz-runs")
        fuzz_runs = int(sys.argv[idx + 1])

    if "--output" in sys.argv:
        idx = sys.argv.index("--output")
        json_filename = sys.argv[idx + 1]

    if "--summary" in sys.argv:
        # Just print summary from existing JSON file
        load_and_print_summary(json_filename)
        return

    if "--bucket" in sys.argv:
        idx = sys.argv.index("--bucket")
        # Collect all bucket numbers after --bucket until we hit another flag or end
        buckets = []
        for i in range(idx + 1, len(sys.argv)):
            if sys.argv[i].startswith("--"):
                break
            try:
                buckets.append(int(sys.argv[i]))
            except ValueError:
                break
    elif "--all" in sys.argv:
        buckets = list(range(16, 64))  # All buckets
    else:
        print("Error: Must specify either --bucket N, --all, or --summary")
        sys.exit(1)

    print(f"Threshold optimization for buckets {buckets}")
    print(f"Using {fuzz_runs} fuzz runs per test")
    print(f"Results will be saved to {json_filename}")

    all_results = []

    for bucket in buckets:
        optimizer = ThresholdOptimizer(bucket, fuzz_runs)
        results = optimizer.collect_results()
        all_results.append(results)
        print_results(results)

        if len(buckets) > 1:
            print(f"\n{'-'*60}")  # Separator between buckets

    # Save results to JSON
    save_to_json(all_results, json_filename)

    # Summary for multiple buckets
    if len(buckets) > 1:
        print(f"\n{'='*60}")
        print(f"SUMMARY FOR ALL BUCKETS")
        print(f"{'='*60}")

        print("Bucket | Min Thresh | Min Seeds     | Safety Thresh | Safety Seeds")
        print("-------|------------|---------------|---------------|-------------")
        for result in all_results:
            bucket = result['bucket']
            min_t = result['min_threshold']
            safety_t = result['safety_threshold']

            min_seeds = result['min_threshold_seeds']
            min_str = f"[{min_seeds[0]}, {min_seeds[1]}]" if min_seeds else "FAILED"

            safety_seeds = result['safety_threshold_seeds']
            safety_str = f"[{safety_seeds[0]}, {safety_seeds[1]}]" if safety_seeds else "FAILED"

            print(f"   {bucket:2d}  |     {min_t:2d}     | {min_str:13s} |      {safety_t:2d}       | {safety_str}")

if __name__ == "__main__":
    main()
