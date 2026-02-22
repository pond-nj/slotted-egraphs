#!/usr/bin/env python3
"""
Extract 'total var' and 'total slots' numbers from a log file and plot histograms.
Usage: python plot_symmetry_hist.py <logfile>
"""

import argparse
import re
import sys
import matplotlib.pyplot as plt
import numpy as np


def parse_log_file(filename):
    """
    Parse the log file and return two lists:
    var_numbers: list of integers from 'total var #number1'
    slot_numbers: list of integers from 'total slots #number2'
    """
    var_numbers = []
    slot_numbers = []
    perm_numbers = []

    # Regex patterns: allow optional spaces after the colon/hash
    var_pattern = re.compile(
        r"\[INFO\s+slotted_egraphs::egraph::symmetries\]\s+total var\s+(\d+)"
    )
    slot_pattern = re.compile(
        r"\[INFO\s+slotted_egraphs::egraph::symmetries\]\s+total slots\s+(\d+)"
    )
    perm_pattern = re.compile(
        r"\[INFO\s+slotted_egraphs::egraph::symmetries\]\s+total perm\s+(\d+)"
    )

    try:
        with open(filename, "r") as f:
            for line in f:
                line = line.strip()
                var_match = var_pattern.search(line)
                if var_match:
                    var_numbers.append(int(var_match.group(1)))
                slot_match = slot_pattern.search(line)
                if slot_match:
                    slot_numbers.append(int(slot_match.group(1)))
                perm_match = perm_pattern.search(line)
                if perm_match:
                    perm_numbers.append(float(perm_match.group(1)))
    except FileNotFoundError:
        print(f"Error: File '{filename}' not found.", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"Error reading file: {e}", file=sys.stderr)
        sys.exit(1)

    return var_numbers, slot_numbers, perm_numbers


def plot_histograms(var_data, slot_data, perm_data, logfile):
    """
    Create two histograms side by side.
    """
    fig, (ax1, ax2, ax3) = plt.subplots(1, 3, figsize=(12, 5))

    # Histogram for total var
    if var_data:
        ax1.hist(var_data, bins="auto", edgecolor="black", alpha=0.7)
        ax1.set_title(f"Histogram of total var ({len(var_data)})")
        ax1.set_xlabel("total var")
        ax1.set_ylabel("Frequency")
    else:
        ax1.text(0.5, 0.5, "No data", ha="center", va="center", transform=ax1.transAxes)
        ax1.set_title("total var (no data)")

    # Histogram for total slots
    if slot_data:
        ax2.hist(slot_data, bins="auto", edgecolor="black", alpha=0.7, color="orange")
        ax2.set_title(f"Histogram of total slots ({len(slot_data)})")
        ax2.set_xlabel("total slots")
        ax2.set_ylabel("Frequency")
    else:
        ax2.text(0.5, 0.5, "No data", ha="center", va="center", transform=ax2.transAxes)
        ax2.set_title("total slots (no data)")

    # Histogram for total slots
    max_perm = np.max(perm_data)
    if perm_data:
        ax3.hist(
            perm_data,
            bins=[i for i in range(1, int(max_perm) + 1, int(max_perm) // 100000)],
            edgecolor="black",
            alpha=0.7,
            color="green",
        )
        ax3.set_title(f"Histogram of total perm ({len(perm_data)})")
        ax3.set_xlabel("total perm")
        ax3.set_ylabel("Frequency")
    else:
        ax3.text(0.5, 0.5, "No data", ha="center", va="center", transform=ax2.transAxes)
        ax3.set_title("total perm (no data)")

    filename = logfile.split(".")[0]
    plt.suptitle(filename)
    plt.tight_layout()

    plt.savefig(f"{filename}.png")


def main():
    parser = argparse.ArgumentParser(
        description="Plot histograms of total var and total slots from a log file."
    )
    parser.add_argument("logfile", help="Path to the log file")
    args = parser.parse_args()

    var_numbers, slot_numbers, perm_numbers = parse_log_file(args.logfile)

    if not var_numbers and not slot_numbers and not perm_numbers:
        print("No matching lines found in the log file.", file=sys.stderr)
        sys.exit(1)

    print(f"Found {len(var_numbers)} 'total var' entries.")
    print(f"Found {len(slot_numbers)} 'total slots' entries.")
    print(f"Found {len(perm_numbers)} 'total perm' entries.")

    plot_histograms(var_numbers, slot_numbers, perm_numbers, args.logfile)


if __name__ == "__main__":
    main()
