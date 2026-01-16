#!/usr/bin/env python3
"""Visualize a 6D split-signature magnitude landscape from GA-inspired rotors."""
from __future__ import annotations

import argparse
import math
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np


def prime_sieve(limit: int) -> np.ndarray:
    sieve = np.ones(limit + 1, dtype=bool)
    if limit >= 0:
        sieve[:2] = False
    for value in range(2, math.isqrt(limit) + 1):
        if sieve[value]:
            sieve[value * value : limit + 1 : value] = False
    return sieve


def parse_primes(raw: str) -> list[int]:
    if not raw:
        return []
    return [int(item.strip()) for item in raw.split(",") if item.strip()]


def magnitude_landscape(
    max_n: int, basis_primes: list[int]
) -> tuple[np.ndarray, np.ndarray]:
    n_values = np.arange(1, max_n + 1, dtype=float)
    pos_sq = np.zeros_like(n_values)
    neg_sq = np.zeros_like(n_values)

    for idx, prime in enumerate(basis_primes):
        theta = (2.0 * math.pi * n_values) / prime
        scale = (n_values / prime) ** 2
        if idx < 3:
            pos_sq += (np.cos(theta) ** 2) * scale
        else:
            neg_sq += (np.sin(theta) ** 2) * scale

    magnitudes = np.sqrt(np.abs(pos_sq - neg_sq))
    return n_values, magnitudes


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Plot a 6D split-signature magnitude landscape."
    )
    parser.add_argument(
        "--max-n",
        type=int,
        default=300,
        help="Upper bound for the landscape.",
    )
    parser.add_argument(
        "--basis-primes",
        type=parse_primes,
        default=parse_primes("2,3,5,7,11,13"),
        help="Comma-separated primes used as rotor frequencies.",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("tuning/ga_rotor_magnitude_landscape.png"),
        help="Path for the generated PNG.",
    )
    parser.add_argument("--show", action="store_true", help="Display the plot.")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.max_n < 2:
        raise SystemExit("--max-n must be >= 2.")
    if len(args.basis_primes) < 3:
        raise SystemExit("--basis-primes must include at least 3 primes.")

    n_values, magnitudes = magnitude_landscape(args.max_n, args.basis_primes)
    prime_mask = prime_sieve(args.max_n)[1:]

    plt.style.use("dark_background")
    fig, ax = plt.subplots(figsize=(15, 6))
    ax.fill_between(n_values, magnitudes, color="cyan", alpha=0.25)
    ax.plot(n_values, magnitudes, color="cyan", linewidth=1.0)
    ax.scatter(
        n_values[prime_mask],
        magnitudes[prime_mask],
        color="yellow",
        s=18,
        label="Primes (lattice peaks)",
    )
    ax.set_title(
        "6D Structural Magnitude Landscape (split signature + + + - - -)\n"
        "Primes emerge where phase torque fails to zero out the metric",
        color="white",
    )
    ax.set_xlabel("Number line", color="white")
    ax.set_ylabel("Hyperbolic magnitude (structural value)", color="white")
    ax.legend()

    args.output.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(args.output, dpi=200, bbox_inches="tight")
    print(f"Wrote GA rotor landscape to {args.output.resolve()}")

    if args.show:
        plt.show()
    else:
        plt.close(fig)


if __name__ == "__main__":
    main()
