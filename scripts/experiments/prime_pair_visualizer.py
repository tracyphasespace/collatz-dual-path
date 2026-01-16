#!/usr/bin/env python3
"""
═══════════════════════════════════════════════════════════════════════════════
Prime Pair Visualizer - Informative plots for twin/cousin/sexy primes

Generates PNG images in ./images/ directory:
  1. cumulative.png - Count vs Hardy-Littlewood conjecture
  2. gaps.png - Gap distribution between consecutive pairs
  3. density.png - Density decay across scales
  4. residue.png - Residue class breakdown (mod 6, mod 30)
  5. ratio.png - Actual/Predicted ratio convergence

═══════════════════════════════════════════════════════════════════════════════
"""
import argparse
import math
import os
import sys
from collections import Counter

import matplotlib.pyplot as plt
import matplotlib.ticker as ticker
import numpy as np

# Import from our prime finder
from prime_pair_finder import find_prime_pairs, is_prime

# Output directory
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
IMAGE_DIR = os.path.join(SCRIPT_DIR, "images")

# Twin prime constant C₂ ≈ 0.6601618158...
TWIN_PRIME_CONSTANT = 0.6601618158468695739278121100145557784326233602847334133194484233354056423


def hardy_littlewood_estimate(x):
    """
    Hardy-Littlewood conjecture for twin prime count π₂(x):
    π₂(x) ~ 2 * C₂ * x / (ln x)²
    """
    if x < 3:
        return 0
    ln_x = math.log(x)
    return 2 * TWIN_PRIME_CONSTANT * x / (ln_x * ln_x)


def li2_integral(x, steps=1000):
    """
    Numerical integration of Li₂(x) = ∫₂ˣ dt/(ln t)²
    """
    if x <= 2:
        return 0
    a, b = 2.0, float(x)
    h = (b - a) / steps
    total = 0
    for i in range(steps):
        t1 = a + i * h
        t2 = a + (i + 1) * h
        if t1 > 1 and t2 > 1:
            f1 = 1 / (math.log(t1) ** 2)
            f2 = 1 / (math.log(t2) ** 2)
            total += (f1 + f2) * h / 2
    return 2 * TWIN_PRIME_CONSTANT * total


def save_figure(fig, name, gap_name):
    """Save figure to images directory."""
    os.makedirs(IMAGE_DIR, exist_ok=True)
    filename = f"{gap_name.lower()}_primes_{name}.png"
    filepath = os.path.join(IMAGE_DIR, filename)
    fig.savefig(filepath, dpi=150, bbox_inches='tight', facecolor='white')
    print(f"  Saved: {filepath}")
    plt.close(fig)
    return filepath


def plot_cumulative(pairs, end, gap_name):
    """Plot cumulative count vs Hardy-Littlewood prediction."""
    if not pairs:
        return None

    # Build cumulative data
    x_vals = [p for p, _ in pairs]
    y_actual = list(range(1, len(pairs) + 1))

    # Sample points for smooth prediction curve
    x_pred = np.logspace(np.log10(max(3, x_vals[0])), np.log10(end), 200)
    y_pred = [li2_integral(x) for x in x_pred]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))

    # Left plot: Cumulative count
    ax1.plot(x_vals, y_actual, 'b-', linewidth=1.5, label=f'Actual π₂(x)', alpha=0.8)
    ax1.plot(x_pred, y_pred, 'r--', linewidth=2, label='Hardy-Littlewood prediction')
    ax1.set_xlabel('x', fontsize=12)
    ax1.set_ylabel(f'{gap_name} Prime Count', fontsize=12)
    ax1.set_title(f'{gap_name} Primes: Cumulative Count vs Prediction', fontsize=14)
    ax1.legend(fontsize=10)
    ax1.grid(True, alpha=0.3)
    ax1.set_xscale('log')
    ax1.set_yscale('log')

    # Right plot: Ratio (actual/predicted)
    # Sample at specific points
    checkpoints = []
    for exp in np.linspace(np.log10(max(100, x_vals[0])), np.log10(end), 50):
        checkpoints.append(int(10**exp))
    checkpoints = sorted(set(checkpoints))

    ratios_x = []
    ratios_y = []
    pair_idx = 0
    for cp in checkpoints:
        while pair_idx < len(pairs) and pairs[pair_idx][0] <= cp:
            pair_idx += 1
        actual = pair_idx
        predicted = li2_integral(cp)
        if predicted > 0:
            ratios_x.append(cp)
            ratios_y.append(actual / predicted)

    ax2.plot(ratios_x, ratios_y, 'go-', markersize=4, linewidth=1.5, label='Actual / Predicted')
    ax2.axhline(y=1.0, color='r', linestyle='--', linewidth=2, label='Perfect prediction')
    ax2.set_xlabel('x', fontsize=12)
    ax2.set_ylabel('Ratio', fontsize=12)
    ax2.set_title('Convergence to Hardy-Littlewood Conjecture', fontsize=14)
    ax2.legend(fontsize=10)
    ax2.grid(True, alpha=0.3)
    ax2.set_xscale('log')
    ax2.set_ylim(0.5, 1.5)

    plt.tight_layout()
    return save_figure(fig, 'cumulative', gap_name)


def plot_gaps(pairs, gap_name):
    """Plot gap distribution between consecutive pairs."""
    if len(pairs) < 2:
        return None

    gaps = [pairs[i+1][0] - pairs[i][0] for i in range(len(pairs)-1)]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))

    # Left: Histogram
    ax1.hist(gaps, bins=50, color='steelblue', edgecolor='black', alpha=0.7)
    ax1.set_xlabel('Gap Size', fontsize=12)
    ax1.set_ylabel('Frequency', fontsize=12)
    ax1.set_title(f'Distribution of Gaps Between Consecutive {gap_name} Primes', fontsize=14)
    ax1.axvline(x=np.mean(gaps), color='red', linestyle='--', linewidth=2,
                label=f'Mean: {np.mean(gaps):.1f}')
    ax1.axvline(x=np.median(gaps), color='orange', linestyle='--', linewidth=2,
                label=f'Median: {np.median(gaps):.1f}')
    ax1.legend(fontsize=10)
    ax1.grid(True, alpha=0.3)

    # Right: Most common gaps (bar chart)
    gap_counts = Counter(gaps)
    most_common = gap_counts.most_common(15)
    gap_vals = [g for g, _ in most_common]
    gap_freqs = [c for _, c in most_common]

    ax2.bar(range(len(gap_vals)), gap_freqs, color='coral', edgecolor='black')
    ax2.set_xticks(range(len(gap_vals)))
    ax2.set_xticklabels(gap_vals, rotation=45)
    ax2.set_xlabel('Gap Size', fontsize=12)
    ax2.set_ylabel('Frequency', fontsize=12)
    ax2.set_title('Most Common Gap Sizes', fontsize=14)
    ax2.grid(True, alpha=0.3, axis='y')

    plt.tight_layout()
    return save_figure(fig, 'gaps', gap_name)


def plot_density(pairs, start, end, gap_name):
    """Plot density decay across the range."""
    if not pairs:
        return None

    num_intervals = 20
    interval_size = (end - start) // num_intervals
    if interval_size < 1:
        interval_size = 1

    intervals = []
    densities = []
    expected = []

    pair_idx = 0
    for i in range(num_intervals):
        int_start = start + i * interval_size
        int_end = int_start + interval_size
        int_mid = (int_start + int_end) / 2

        # Count pairs in interval
        count = 0
        while pair_idx < len(pairs) and pairs[pair_idx][0] < int_end:
            if pairs[pair_idx][0] >= int_start:
                count += 1
            pair_idx += 1

        density = count / interval_size
        exp_density = 2 * TWIN_PRIME_CONSTANT / (math.log(int_mid) ** 2) if int_mid > 1 else 0

        intervals.append(int_mid)
        densities.append(density)
        expected.append(exp_density)

    fig, ax = plt.subplots(figsize=(10, 6))

    ax.plot(intervals, densities, 'bo-', markersize=6, linewidth=1.5, label='Actual density')
    ax.plot(intervals, expected, 'r--', linewidth=2, label='Expected: 2C₂/(ln x)²')

    ax.set_xlabel('x', fontsize=12)
    ax.set_ylabel('Density (pairs per integer)', fontsize=12)
    ax.set_title(f'{gap_name} Prime Density Decay', fontsize=14)
    ax.legend(fontsize=10)
    ax.grid(True, alpha=0.3)
    ax.set_xscale('log')
    ax.set_yscale('log')

    plt.tight_layout()
    return save_figure(fig, 'density', gap_name)


def plot_residues(pairs, gap, gap_name):
    """Plot residue class distribution."""
    if not pairs:
        return None

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))

    # Mod 6 analysis
    mod6 = Counter(p % 6 for p, _ in pairs)
    classes6 = sorted(mod6.keys())
    counts6 = [mod6[c] for c in classes6]

    ax1.bar(range(len(classes6)), counts6, color='steelblue', edgecolor='black')
    ax1.set_xticks(range(len(classes6)))
    ax1.set_xticklabels(classes6)
    ax1.set_xlabel('Residue class (mod 6)', fontsize=12)
    ax1.set_ylabel('Count', fontsize=12)
    ax1.set_title(f'First Prime of {gap_name} Pair (mod 6)', fontsize=14)
    ax1.grid(True, alpha=0.3, axis='y')

    # Add percentages
    total = sum(counts6)
    for i, (c, count) in enumerate(zip(classes6, counts6)):
        pct = 100 * count / total
        ax1.text(i, count + total*0.01, f'{pct:.1f}%', ha='center', fontsize=10)

    # Mod 30 analysis
    mod30 = Counter(p % 30 for p, _ in pairs)
    classes30 = sorted([c for c in mod30.keys() if mod30[c] > 0])
    counts30 = [mod30[c] for c in classes30]

    ax2.bar(range(len(classes30)), counts30, color='coral', edgecolor='black')
    ax2.set_xticks(range(len(classes30)))
    ax2.set_xticklabels(classes30, rotation=45)
    ax2.set_xlabel('Residue class (mod 30)', fontsize=12)
    ax2.set_ylabel('Count', fontsize=12)
    ax2.set_title(f'First Prime of {gap_name} Pair (mod 30)', fontsize=14)
    ax2.grid(True, alpha=0.3, axis='y')

    plt.tight_layout()
    return save_figure(fig, 'residue', gap_name)


def plot_locations(pairs, start, end, gap_name):
    """Plot where twin primes occur in the range."""
    if not pairs:
        return None

    fig, ax = plt.subplots(figsize=(14, 4))

    # Plot each pair as a vertical line
    x_vals = [p for p, _ in pairs]
    ax.vlines(x_vals, 0, 1, colors='blue', alpha=0.5, linewidth=0.5)

    ax.set_xlabel('x', fontsize=12)
    ax.set_title(f'{gap_name} Prime Locations ({len(pairs):,} pairs)', fontsize=14)
    ax.set_xlim(start, end)
    ax.set_ylim(0, 1)
    ax.set_yticks([])
    ax.grid(True, alpha=0.3, axis='x')

    plt.tight_layout()
    return save_figure(fig, 'locations', gap_name)


def main():
    parser = argparse.ArgumentParser(description="Visualize prime pair distributions")
    parser.add_argument("--start", type=int, default=1, help="Search start")
    parser.add_argument("--end", type=int, default=100000, help="Search end")
    parser.add_argument("--gap", type=int, default=2, help="Gap (2=twin, 4=cousin, 6=sexy)")
    args = parser.parse_args()

    gap_names = {2: "Twin", 4: "Cousin", 6: "Sexy"}
    gap_name = gap_names.get(args.gap, f"Gap{args.gap}")

    print(f"{'=' * 60}")
    print(f"{gap_name} Prime Visualizer")
    print(f"Range: {args.start:,} to {args.end:,}")
    print(f"Output: {IMAGE_DIR}/")
    print(f"{'=' * 60}")

    # Find pairs
    print("\nFinding prime pairs...")
    pairs = find_prime_pairs(args.start, args.end, gap=args.gap, verbose=False)
    print(f"Found {len(pairs):,} {gap_name.lower()} prime pairs")

    if not pairs:
        print("No pairs found in range.")
        return

    # Generate all plots
    print("\nGenerating plots...")

    plot_cumulative(pairs, args.end, gap_name)
    plot_gaps(pairs, gap_name)
    plot_density(pairs, args.start, args.end, gap_name)
    plot_residues(pairs, args.gap, gap_name)
    plot_locations(pairs, args.start, args.end, gap_name)

    print(f"\nAll plots saved to {IMAGE_DIR}/")

    # Print summary statistics
    print(f"\n{'=' * 60}")
    print("SUMMARY")
    print(f"{'=' * 60}")
    print(f"Total {gap_name.lower()} primes: {len(pairs):,}")
    print(f"First pair: {pairs[0]}")
    print(f"Last pair: {pairs[-1]}")

    predicted = li2_integral(args.end)
    ratio = len(pairs) / predicted if predicted > 0 else 0
    print(f"Hardy-Littlewood prediction: {predicted:.1f}")
    print(f"Actual/Predicted ratio: {ratio:.4f}")
    print(f"Gap from prediction: {100*(ratio-1):+.2f}%")

    if len(pairs) >= 2:
        gaps = [pairs[i+1][0] - pairs[i][0] for i in range(len(pairs)-1)]
        print(f"\nGap statistics:")
        print(f"  Mean gap between pairs: {np.mean(gaps):.1f}")
        print(f"  Median gap: {np.median(gaps):.1f}")
        print(f"  Max gap: {max(gaps)}")


if __name__ == "__main__":
    main()
