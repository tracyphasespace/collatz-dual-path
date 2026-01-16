#!/usr/bin/env python3
"""Log-polar transform of the Clifford walk with prime lattice overlay."""
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


def log_polar_prime_lattice(
    max_n: int,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    n_values = np.arange(1, max_n + 1, dtype=float)
    r = np.log(n_values)
    theta = np.cumsum(np.pi / n_values)
    is_prime = prime_sieve(max_n)[1:]
    x = r * np.cos(theta)
    y = r * np.sin(theta)
    return x, y, is_prime, theta


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Render a log-polar prime lattice from the Clifford walk."
    )
    parser.add_argument(
        "--max-n",
        type=int,
        default=20_000,
        help="Upper bound for the harmonic sequence.",
    )
    parser.add_argument(
        "--stride",
        type=int,
        default=1,
        help="Stride for plotting the composite background line.",
    )
    parser.add_argument(
        "--prime-size",
        type=float,
        default=6.0,
        help="Marker size for prime lattice points.",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("tuning/log_polar_prime_lattice.png"),
        help="Path for the generated PNG.",
    )
    parser.add_argument("--show", action="store_true", help="Display the plot.")
    parser.add_argument(
        "--phase-gap",
        action="store_true",
        help="Print summary stats for phase gaps between primes.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.max_n < 2:
        raise SystemExit("--max-n must be >= 2.")
    if args.stride < 1:
        raise SystemExit("--stride must be >= 1.")

    x, y, is_prime, theta = log_polar_prime_lattice(args.max_n)

    plt.style.use("dark_background")
    fig, ax = plt.subplots(figsize=(12, 12))
    ax.plot(
        x[:: args.stride],
        y[:: args.stride],
        color="white",
        alpha=0.12,
        linewidth=0.6,
        label="Composite harmonic flux",
    )
    ax.scatter(
        x[is_prime],
        y[is_prime],
        c="cyan",
        s=args.prime_size,
        alpha=0.85,
        label="Prime lattice points",
    )
    ax.set_title(
        "Log-Polar Prime Lattice\nCompactification of the number line (radius = ln N)",
        color="white",
    )
    ax.set_aspect("equal", adjustable="datalim")
    ax.legend(loc="upper right")

    args.output.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(args.output, dpi=200, bbox_inches="tight")
    print(f"Wrote log-polar lattice plot to {args.output.resolve()}")

    if args.phase_gap:
        prime_theta = theta[is_prime]
        gaps = np.diff(prime_theta)
        if gaps.size:
            print(
                "Phase gaps (rad): "
                f"mean={gaps.mean():.6f}, std={gaps.std():.6f}, "
                f"min={gaps.min():.6f}, max={gaps.max():.6f}"
            )
        else:
            print("Phase gaps (rad): not enough primes for gap statistics.")

    if args.show:
        plt.show()
    else:
        plt.close(fig)


if __name__ == "__main__":
    main()
