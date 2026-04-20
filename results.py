import subprocess
import time
import json
import sys
import os
import re
from itertools import combinations
from datetime import datetime

testcases = [
    "arith2::tst::t7",
    "chc::pairingPaperArray::mainTest",
    "chc::leafDrop2::mainTest",
]

extra = [
    "adtDefine",
    #  "pairingDefine"
]

# Mapping of testcases to their valid extra values
# If a testcase is not in this dict, it uses all extra values
# Use None to indicate running without any extra value
testcase_extra_mapping = {
    "arith2::tst::t7": [None],  # Run without extra values for this testcase
}

timeout = 300

features = [
    "newShape",
    "sortENodesByNT",
]

always = [
    "log",
]

# File to store all results persistently
ALL_RESULTS_FILE = "all_test_results.json"


def generate_feature_combinations():
    """
    Generate all feature selection combinations:
    - Select none (empty set)
    - Select one feature at a time
    - Select all features
    """
    combos = []

    # Select none
    combos.append([])

    # Select one feature at a time
    for feature in features:
        combos.append([feature])

    # Select all features
    combos.append(list(features))

    return combos


def build_feature_string(selected_features):
    """Build the feature flag string for cargo test"""
    if not selected_features:
        return ""
    # Combine selected features with always features
    all_features = list(set(selected_features + always))
    return ",".join(all_features)


def extract_timing_from_output(stdout, stderr):
    """
    Extract timing information from test output.
    Looks for patterns like "total time = 6.304352041s" or "total time = Duration { secs: X, nanos: Y }"
    Returns time in seconds, or None if not found.
    """
    # Search in both stdout and stderr
    output = stdout + "\n" + stderr

    # Pattern: "total time = 6.304352041s" (decimal seconds)
    time_pattern = r"total time = ([\d.]+)\s*s(?:ec|ecs)?"
    match = re.search(time_pattern, output, re.IGNORECASE)
    if match:
        value = float(match.group(1))
        return value

    # Pattern: "total time = Duration { secs: X, nanos: Y }"
    duration_pattern = r"total time = Duration \{ secs: (\d+), nanos: (\d+) \}"
    match = re.search(duration_pattern, output, re.IGNORECASE)
    if match:
        secs = int(match.group(1))
        nanos = int(match.group(2))
        total_secs = secs + nanos / 1e9
        return total_secs

    # Pattern: "total time = ...ms"
    ms_pattern = r"total time = ([\d.]+)\s*ms"
    match = re.search(ms_pattern, output, re.IGNORECASE)
    if match:
        value = float(match.group(1))
        return value / 1000

    return None


def save_test_logs(log_dir, testcase, extra_val, features_selected, result, cmd):
    """
    Save test output to log files organized by testcase, extra, and features
    """
    # Create directory structure: logs/testcase/extra/
    testcase_name = testcase.replace("::", "_")
    extra_name = extra_val if extra_val is not None else "no_extra"
    feature_name = "_".join(features_selected) if features_selected else "none"

    test_log_dir = os.path.join(log_dir, testcase_name, extra_name)
    os.makedirs(test_log_dir, exist_ok=True)

    # Prepare command header
    cmd_header = f"Command: {' '.join(cmd)}\n" + "=" * 80 + "\n\n"

    # Save stdout
    if "stdout" in result:
        stdout_file = os.path.join(test_log_dir, f"{feature_name}.stdout")
        with open(stdout_file, "w") as f:
            f.write(cmd_header)
            f.write(result["stdout"])

    # Save stderr
    if "stderr" in result:
        stderr_file = os.path.join(test_log_dir, f"{feature_name}.stderr")
        with open(stderr_file, "w") as f:
            f.write(cmd_header)
            f.write(result["stderr"])

    # Save error message if present
    if "error" in result:
        error_file = os.path.join(test_log_dir, f"{feature_name}.error")
        with open(error_file, "w") as f:
            f.write(cmd_header)
            f.write(result["error"])


def run_test(testcase, extra_val, features_selected):
    """
    Run a single test with the given configuration and return execution time
    extra_val can be a string or None (meaning no extra value)
    Returns both the result and the command that was executed
    Tries to extract timing from test output, falls back to wall-clock time
    """
    feature_str = build_feature_string(features_selected)

    # Add extra_val to features if it's not None
    if extra_val is not None:
        if feature_str:
            feature_str = feature_str + "," + extra_val
        else:
            feature_str = extra_val + "," + always[0]  # Add always features with extra

    # Build cargo test command
    cmd = ["cargo", "test", "--release", "--test", "entry", testcase, "--"]

    # Add feature flag if features are selected
    if feature_str:
        cmd = [
            "cargo",
            "test",
            "--release",
            "--test",
            "entry",
            testcase,
            "--features",
            feature_str,
            "--",
        ]

    # Add timeout
    cmd.extend(["--test-threads=1", "--nocapture"])

    print(f"Running: {' '.join(cmd)}", flush=True)

    try:
        start_time = time.time()
        result = subprocess.run(cmd, timeout=timeout, capture_output=True, text=True)
        elapsed_time = time.time() - start_time

        success = result.returncode == 0

        # Try to extract timing from output
        extracted_time = extract_timing_from_output(result.stdout, result.stderr)
        if extracted_time is not None:
            # Use extracted time from test output
            recorded_time = extracted_time
            time_source = "extracted from output"
        else:
            # Fall back to wall-clock time
            recorded_time = elapsed_time
            time_source = "wall-clock"

        return (
            {
                "success": success,
                "time": recorded_time,
                "wall_clock_time": elapsed_time,
                "time_source": time_source,
                "stdout": result.stdout,
                "stderr": result.stderr,
            },
            cmd,
        )
    except subprocess.TimeoutExpired:
        return (
            {
                "success": False,
                "time": timeout,
                "wall_clock_time": timeout,
                "time_source": "timeout",
                "error": "TIMEOUT",
            },
            cmd,
        )
    except Exception as e:
        return (
            {
                "success": False,
                "time": 0,
                "wall_clock_time": 0,
                "time_source": "error",
                "error": str(e),
            },
            cmd,
        )


def build_all_features(log_dir, feature_combos):
    """
    Pre-build all feature combinations to avoid compilation time during tests
    Includes all extra values
    """
    print("\n" + "=" * 80)
    print("PRE-BUILDING ALL FEATURE COMBINATIONS")
    print("=" * 80 + "\n")

    unique_features = set()
    unique_features.add("")  # Empty features (only always features)

    # Add all feature combinations
    for combo in feature_combos:
        if combo:  # Non-empty
            feature_str = build_feature_string(combo)
            unique_features.add(feature_str)

    # Add all extra values combined with always features
    for extra_val in extra:
        feature_str = extra_val + "," + always[0]
        unique_features.add(feature_str)

    # Add extra values with each feature combination
    for combo in feature_combos:
        for extra_val in extra:
            feature_str = build_feature_string(combo) + "," + extra_val
            unique_features.add(feature_str)

    build_num = 0
    for feature_str in sorted(unique_features):
        build_num += 1

        if feature_str:
            display_str = feature_str
            cmd = ["cargo", "build", "--release", "--features", feature_str]
        else:
            display_str = "default (only log)"
            cmd = ["cargo", "build", "--release"]

        print(f"[{build_num}/{len(unique_features)}] Building: {display_str}")
        print(f"  Command: {' '.join(cmd)}", flush=True)

        try:
            result = subprocess.run(
                cmd, timeout=timeout, capture_output=True, text=True
            )
            if result.returncode == 0:
                print(f"  ✓ Build successful\n")
            else:
                print(f"  ✗ Build failed")
                print(result.stderr[:500])  # Print first 500 chars of error
                print()
        except subprocess.TimeoutExpired:
            print(f"  ✗ Build timeout ({timeout}s)\n")
        except Exception as e:
            print(f"  ✗ Build error: {e}\n")

    print("Pre-build complete!\n")


def load_previous_results():
    """
    Load previously run test results from file.
    Returns a dict mapping (testcase, extra, features_tuple) -> result
    """
    if not os.path.exists(ALL_RESULTS_FILE):
        return {}

    try:
        with open(ALL_RESULTS_FILE, "r") as f:
            all_results = json.load(f)

        # Create a lookup dict by test configuration
        lookup = {}
        for result in all_results:
            # Convert features list to tuple for hashing
            features_tuple = tuple(result["features"])
            key = (result["testcase"], result["extra"], features_tuple)
            lookup[key] = result

        print(f"Loaded {len(lookup)} previous test results from {ALL_RESULTS_FILE}")
        return lookup
    except Exception as e:
        print(f"Error loading previous results: {e}")
        return {}


def save_result_incrementally(result):
    """
    Append a single test result to the persistent results file
    """
    try:
        # Load existing results
        if os.path.exists(ALL_RESULTS_FILE):
            with open(ALL_RESULTS_FILE, "r") as f:
                all_results = json.load(f)
        else:
            all_results = []

        # Append new result
        all_results.append(result)

        # Save back
        with open(ALL_RESULTS_FILE, "w") as f:
            json.dump(all_results, f, indent=2)
    except Exception as e:
        print(f"Warning: Error saving result incrementally: {e}")


def main():
    """Run all test combinations and record results"""

    feature_combos = generate_feature_combinations()

    # Create log directory with timestamp
    log_dir = f"logs_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
    os.makedirs(log_dir, exist_ok=True)

    # Calculate total tests accounting for testcase-specific extra values
    total_tests = 0
    for testcase in testcases:
        extra_vals = testcase_extra_mapping.get(testcase, extra)
        total_tests += len(extra_vals) * len(feature_combos)

    print(f"Total test combinations: {total_tests}")
    print(f"  Testcases: {len(testcases)}")
    print(f"  Feature combinations: {len(feature_combos)}")
    print(f"Logging to: {log_dir}")

    # Pre-build all feature combinations
    build_all_features(log_dir, feature_combos)

    # Load previously run tests
    previous_results = load_previous_results()
    print()

    results = []
    test_num = 0
    skipped_num = 0

    for testcase in testcases:
        # Get extra values for this testcase, or use all if not specified
        extra_vals = testcase_extra_mapping.get(testcase, extra)

        for extra_val in extra_vals:
            for feature_combo in feature_combos:
                test_num += 1

                feature_desc = (
                    f"[{', '.join(feature_combo)}]" if feature_combo else "[none]"
                )

                # Create a key for this test configuration
                features_tuple = tuple(feature_combo)
                test_key = (testcase, extra_val, features_tuple)

                # For testcases with no extra value, show simplified output
                if extra_val is None:
                    print(
                        f"[{test_num}/{total_tests}] {testcase} + features {feature_desc}"
                    )
                else:
                    print(
                        f"[{test_num}/{total_tests}] {testcase} + {extra_val} + features {feature_desc}"
                    )

                # Check if this test has already been run
                if test_key in previous_results:
                    record = previous_results[test_key]
                    results.append(record)
                    status = "✓ PASS" if record["success"] else "✗ FAIL"
                    print(
                        f"  {status} - Time: {record['time']:.2f}s (from previous run, skipped)"
                    )
                    skipped_num += 1
                    print()
                    continue

                # Run the test
                result = run_test(testcase, extra_val, feature_combo)

                # Unpack result and command
                result_data, cmd = result

                # Save test logs
                save_test_logs(
                    log_dir, testcase, extra_val, feature_combo, result_data, cmd
                )

                record = {
                    "test_num": test_num,
                    "testcase": testcase,
                    "extra": extra_val,
                    "features": feature_combo,
                    "features_with_always": list(set(feature_combo + always)),
                    "success": result_data["success"],
                    "time": result_data["time"],
                    "wall_clock_time": result_data.get(
                        "wall_clock_time", result_data["time"]
                    ),
                    "time_source": result_data.get("time_source", "unknown"),
                    "timestamp": datetime.now().isoformat(),
                }

                if "error" in result_data:
                    record["error"] = result_data["error"]

                results.append(record)
                save_result_incrementally(record)

                status = "✓ PASS" if result_data["success"] else "✗ FAIL"
                time_src = result_data.get("time_source", "unknown")
                print(f"  {status} - Time: {result_data['time']:.2f}s ({time_src})")
                print()

    # Save results to JSON file
    output_file = os.path.join(log_dir, "results.json")
    with open(output_file, "w") as f:
        json.dump(results, f, indent=2)

    print(f"\nResults saved to {output_file}")
    print(f"All results accumulated in: {ALL_RESULTS_FILE}")

    if skipped_num > 0:
        print(f"\nSkipped {skipped_num} previously run tests")
        print(f"Newly run: {test_num - skipped_num} tests")

    # Print summary
    passed = sum(1 for r in results if r["success"])
    failed = len(results) - passed
    total_time = sum(r["time"] for r in results)

    # Count timing sources
    timing_sources = {}
    for r in results:
        source = r.get("time_source", "unknown")
        timing_sources[source] = timing_sources.get(source, 0) + 1

    print(f"\n=== SUMMARY ===")
    print(f"Log directory: {log_dir}")
    print(f"Total tests: {len(results)}")
    print(f"Passed: {passed}")
    print(f"Failed: {failed}")
    print(f"Total time (extracted): {total_time:.2f}s")
    print(f"Average time: {total_time/len(results):.2f}s")
    print(f"\nTiming sources:")
    for source, count in sorted(timing_sources.items()):
        print(f"  {source}: {count} tests")

    # Print failure details
    if failed > 0:
        print(f"\n=== FAILURES ===")
        for r in results:
            if not r["success"]:
                print(f"\n{r['testcase']} + {r['extra']} + {r['features']}")
                if "error" in r:
                    print(f"  Error: {r['error']}")


if __name__ == "__main__":
    main()
