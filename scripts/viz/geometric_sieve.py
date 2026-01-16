#!/usr/bin/env python3
"""Visualize primes as the residue of expanding sphere-based sieves."""
from __future__ import annotations

import argparse
from pathlib import Path
from typing import List

import matplotlib.pyplot as plt
import numpy as np


def sphere_subtraction_sieve(max_n: int) -> tuple[List[int], np.ndarray, List[tuple[int, np.ndarray]]]:
    landscape = np.zeros(max_n + 1)
    primes: List[int] = []
    waves: List[tuple[int, np.ndarray]] = []

    for n in range(2, max_n + 1):
        if landscape[n] == 0:
            primes.append(n)
            multiples = np.arange(n * 2, max_n + 1, n)
            landscape[multiples] += 1

            wave = np.zeros(max_n + 1)
            wave[np.arange(n, max_n + 1, n)] = 1
            waves.append((n, wave))

    return primes, landscape, waves


def plot_geometric_sieve(
    max_n: int,
    primes: List[int],
    coverage: np.ndarray,
    waves: List[tuple[int, np.ndarray]],
    output: Path,
    show_plot: bool,
) -> None:
    plt.style.use("dark_background")
    fig, ax = plt.subplots(figsize=(14, 8))

    x = np.arange(max_n + 1)
    ax.bar(x, -coverage, color="cyan", alpha=0.3, width=0.8, label="Sphere overlap depth")
    ax.scatter(
        primes,
        np.zeros(len(primes)),
        color="white",
        edgecolors="lime",
        s=90,
        linewidth=2,
        zorder=10,
        label="Primes (untouched)",
    )

    for idx, (prime, wave) in enumerate(waves[: min(len(waves), 10)]):
        points = np.where(wave > 0)[0]
        y_level = (idx + 1) * 0.4
        label = f"Spheres from {prime}" if idx < 5 else None
        ax.scatter(points, np.full_like(points, y_level), s=18, alpha=0.8, label=label)
        for point in points:
            if point == prime:
                continue
            ax.plot([prime, point], [y_level, y_level], color="white", alpha=0.05, linewidth=0.5)

    ax.axhline(0, color="lime", linewidth=1, linestyle="--", alpha=0.5)
    ax.set_title(
        f"Geometric sieve landscape (N={max_n})\nPrimes appear where no sphere intersected",
        color="white",
    )
    ax.set_xlabel("Number line", color="white")
    ax.set_ylabel("Sphere intersection depth", color="white")
    ax.set_xlim(1, max_n + 1)
    ax.set_yticks([])

    for prime in primes[: min(len(primes), 12)]:
        ax.text(prime, 0.15, str(prime), color="lime", ha="center", fontweight="bold")

    ax.legend(loc="upper right")
    ax.grid(True, axis="x", alpha=0.1)

    output.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output, dpi=300, bbox_inches="tight")
    print(f"Wrote geometric sieve visualization to {output.resolve()}")

    if show_plot:
        plt.show()
    else:
        plt.close(fig)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Geometric sphere subtraction sieve visualization")
    parser.add_argument("--max-n", type=int, default=100, help="Upper bound for the sieve.")
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("tuning/geometric_sieve.png"),
        help="PNG path for the visualization.",
    )
    parser.add_argument("--show", action="store_true", help="Display the plot interactively.")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    primes, coverage, waves = sphere_subtraction_sieve(args.max_n)
    plot_geometric_sieve(
        args.max_n,
        primes,
        coverage,
        waves,
        args.output,
        show_plot=args.show,
    )


if __name__ == "__main__":
    main()
