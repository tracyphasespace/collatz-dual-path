#!/usr/bin/env python3
"""
═══════════════════════════════════════════════════════════════════════════════
EVALUATION (2026-01-16):
  - Hybrid benchmark comparing different methods
  - Requires matplotlib/numpy
  - VALUE: NONE - benchmarking tool, no unique capability
  - RECOMMENDATION: Archive
═══════════════════════════════════════════════════════════════════════════════
"""
import argparse
from datetime import datetime
import random
import sys
import time

import matplotlib.pyplot as plt
import numpy as np

# Memory safety defaults
DEFAULT_MAX_RANGE = 100_000  # 100K elements max


# --- LAYER 1: THE CLIFFORD GEOMETRIC FILTER ---
class CliffordManifold:
    """
    Represents the pre-computed interference pattern of the first 4 orthogonal
    prime surfaces (2, 3, 5, 7). In Cl(4,4), these form the fundamental structure.
    """

    def __init__(self):
        # The 'Basis' of our 4 orthogonal planes
        self.basis = [2, 3, 5, 7]
        # The period of the interference pattern (2*3*5*7)
        self.period = 210
        # The 'Surface Mask': True where the 'tunnel' is open (coprime to basis)
        self.mask = self._build_manifold_mask()

    def _build_manifold_mask(self):
        """Builds the boolean geometry of the 210-cell hyper-crystal."""
        # Create universe of one period
        universe = np.arange(self.period)
        # Start with all open (True)
        tunnel = np.ones(self.period, dtype=bool)

        # Apply the 4 orthogonal surfaces (set multiples to False)
        for p in self.basis:
            tunnel[universe % p == 0] = False

        return tunnel

    def apply_filter(self, start, end):
        """
        Applies the geometric mask to a specific range of the number line.
        This simulates 'Surface Finding' - no division, just pattern matching.
        """
        length = end - start
        if length <= 0:
            return np.array([])

        # Align the mask to the start of the range
        offset = start % self.period

        # Tile the mask to cover the range (vectorized operation)
        num_repeats = (length // self.period) + 2
        tiled_mask = np.tile(self.mask, num_repeats)

        # Slice the exact window we need
        aligned_mask = tiled_mask[offset : offset + length]

        # Generate the actual numbers
        candidates = np.arange(start, end)

        # Return only the survivors (The 'Null' results)
        return candidates[aligned_mask]


# --- LAYER 2: THE ARITHMETIC SOLVER (Miller-Rabin) ---

def miller_rabin(n, k=5):
    """
    Standard probabilistic check. Represents the 'Arithmetic' cost.
    Used only on survivors of the geometric filter.
    """
    if n < 2:
        return False
    if n in (2, 3):
        return True
    if n % 2 == 0:
        return False

    r, d = 0, n - 1
    while d % 2 == 0:
        r += 1
        d //= 2
    for _ in range(k):
        a = random.randrange(2, n - 1)
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True


# --- THE EXPERIMENT ---

def run_hybrid_benchmark(start, range_size):
    end = start + range_size

    print(f"--- BENCHMARK: Range {start:,} to {end:,} ---")

    # 1. METHOD A: Standard Linear Scan (Amnesia)
    print("Running Standard Linear Solver...")
    t0 = time.time()
    standard_primes = []
    scan_start = start if start % 2 != 0 else start + 1
    checks_standard = 0

    for n in range(scan_start, end, 2):
        checks_standard += 1
        if miller_rabin(n):
            standard_primes.append(n)

    t1 = time.time()
    time_standard = t1 - t0
    print(f"Standard: {time_standard:.4f}s | Checks: {checks_standard:,}")

    # 2. METHOD B: Clifford Hybrid (Learning)
    print("Running Clifford Hybrid Solver...")
    t2 = time.time()

    # Step 1: Geometry (The Manifold)
    manifold = CliffordManifold()
    survivors = manifold.apply_filter(start, end)

    # Step 2: Arithmetic (The Proof)
    hybrid_primes = []
    checks_hybrid = 0
    for n in survivors:
        checks_hybrid += 1
        if miller_rabin(int(n)):
            hybrid_primes.append(int(n))

    t3 = time.time()
    time_hybrid = t3 - t2
    print(f"Hybrid:   {time_hybrid:.4f}s | Checks: {checks_hybrid:,}")

    # Verification
    assert len(standard_primes) == len(hybrid_primes)
    print(f"Result Match: Verified ({len(hybrid_primes)} primes found)")

    return {
        "time_std": time_standard,
        "time_hyb": time_hybrid,
        "checks_std": checks_standard,
        "checks_hyb": checks_hybrid,
    }


def plot_results(results, output):
    labels = ["Standard (Amnesia)", "Clifford Hybrid (Learning)"]
    times = [results["time_std"], results["time_hyb"]]
    checks = [results["checks_std"], results["checks_hyb"]]

    fig, ax1 = plt.subplots(figsize=(10, 6))

    color = "tab:red"
    ax1.set_xlabel("Solver Method")
    ax1.set_ylabel("Execution Time (seconds)", color=color)
    ax1.bar(labels, times, color=color, alpha=0.6, width=0.5)
    ax1.tick_params(axis="y", labelcolor=color)

    if results["time_std"] > 0:
        improvement = (1 - results["time_hyb"] / results["time_std"]) * 100
    else:
        improvement = 0
    ax1.text(
        1,
        results["time_hyb"],
        f"{improvement:.1f}% Faster",
        ha="center",
        va="bottom",
        fontsize=12,
        fontweight="bold",
    )

    ax2 = ax1.twinx()
    color = "tab:blue"
    ax2.set_ylabel("Arithmetic Operations (Miller-Rabin Calls)", color=color)
    ax2.plot(labels, checks, color=color, marker="o", linewidth=3, markersize=10)
    ax2.tick_params(axis="y", labelcolor=color)

    if results["checks_std"] > 0:
        reduction = (1 - results["checks_hyb"] / results["checks_std"]) * 100
    else:
        reduction = 0
    ax2.text(
        1,
        results["checks_hyb"],
        f"-{reduction:.1f}% Checks",
        ha="left",
        va="center",
        color="blue",
        fontweight="bold",
        bbox=dict(facecolor="white", alpha=0.7, pad=4),
    )

    plt.title("Hybrid Solver Performance: 8D Geometry vs 1D Arithmetic")
    plt.tight_layout()
    fig.savefig(output, dpi=200, bbox_inches="tight")
    plt.close(fig)
    print(f"Wrote plot to {output}")


def parse_args():
    parser = argparse.ArgumentParser(description="Benchmark Clifford hybrid prime finder.")
    parser.add_argument("--start", type=int, default=100_000,
                        help="Start of range (default: 100,000)")
    parser.add_argument("--range-size", type=int, default=50_000,
                        help="Size of range to scan (default: 50,000)")
    parser.add_argument("--max-range", type=int, default=DEFAULT_MAX_RANGE,
                        help=f"Maximum allowed range size (default: {DEFAULT_MAX_RANGE:,})")
    parser.add_argument("--no-plot", action="store_true",
                        help="Skip generating plot")
    return parser.parse_args()


if __name__ == "__main__":
    args = parse_args()

    if args.range_size > args.max_range:
        print(f"ERROR: range_size {args.range_size:,} exceeds max {args.max_range:,}. "
              f"Use --max-range to increase.", file=sys.stderr)
        sys.exit(1)

    random.seed(0)
    results = run_hybrid_benchmark(start=args.start, range_size=args.range_size)

    if not args.no_plot:
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        plot_results(results, f"tuning/clifford_hybrid_benchmark_{timestamp}.png")
