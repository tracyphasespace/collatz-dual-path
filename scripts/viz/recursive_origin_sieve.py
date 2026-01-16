#!/usr/bin/env python3
"""Recursive origin sieve visualizer."""
from __future__ import annotations

import argparse
import math
from pathlib import Path
from typing import List

import matplotlib.pyplot as plt


DEFAULT_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]


def generate_primes(count: int) -> List[int]:
    primes: List[int] = []
    candidate = 2
    while len(primes) < count:
        is_prime = True
        limit = int(math.sqrt(candidate))
        for divisor in range(2, limit + 1):
            if candidate % divisor == 0:
                is_prime = False
                break
        if is_prime:
            primes.append(candidate)
        candidate += 1 if candidate == 2 else 2  # skip even numbers after 2
    return primes


def recursive_origin_sieve(primes: List[int]) -> tuple[List[float], List[float]]:
    x_coords = [0.0]
    y_coords = [0.0]

    if not primes:
        return x_coords, y_coords

    max_step = max(primes) - 1
    harmonic = [0.0] * (max_step + 1)
    for k in range(1, max_step + 1):
        harmonic[k] = harmonic[k - 1] + 1.0 / k

    for prime_idx, prime in enumerate(primes):
        current_x = x_coords[-1]
        current_y = y_coords[-1]

        for step in range(1, prime):
            angle = math.pi * harmonic[step]
            sign = 1.0 if prime_idx % 2 == 0 else -1.0
            current_x += step * math.cos(angle) * sign
            current_y += step * math.sin(angle) * sign
            x_coords.append(current_x)
            y_coords.append(current_y)

    return x_coords, y_coords


def plot_recursive_sieve(x: List[float], y: List[float], output: Path, show_plot: bool) -> None:
    plt.style.use("dark_background")
    fig, ax = plt.subplots(figsize=(10, 10))

    ax.plot(x, y, color="yellow", alpha=0.7, linewidth=1.0, label="Recursive genesis path")
    stride = max(1, len(x) // 3000)
    ax.scatter(
        x[::stride],
        y[::stride],
        color="red",
        s=10,
        alpha=0.6,
        label=f"Sampled nodes (stride={stride})",
    )
    ax.set_title("Recursive origin sieve: each prime restarts the walk", color="white")
    ax.set_aspect("equal", adjustable="datalim")
    ax.legend(loc="upper right")

    output.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output, dpi=300, bbox_inches="tight")
    print(f"Wrote recursive origin plot to {output.resolve()}")

    if show_plot:
        plt.show()
    else:
        plt.close(fig)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Recursive origin sieve visualizer")
    parser.add_argument(
        "--num-primes",
        type=int,
        default=8,
        help="Number of seed primes to include (uses defaults when <= len(DEFAULT_PRIMES)).",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("tuning/recursive_origin.png"),
        help="Path for the generated PNG.",
    )
    parser.add_argument("--show", action="store_true", help="Display the plot interactively.")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.num_primes <= len(DEFAULT_PRIMES):
        primes = DEFAULT_PRIMES[: args.num_primes]
    else:
        primes = generate_primes(args.num_primes)
    x, y = recursive_origin_sieve(primes)
    plot_recursive_sieve(x, y, args.output, show_plot=args.show)


if __name__ == "__main__":
    main()
