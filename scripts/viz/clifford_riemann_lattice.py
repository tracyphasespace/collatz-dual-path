#!/usr/bin/env python3
"""Superpose many Riemann zeros to form a lattice-like interference path."""
from __future__ import annotations

import argparse
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, List

import matplotlib.pyplot as plt


@dataclass
class WalkData:
    x: List[float]
    y: List[float]
    prime_x: List[float]
    prime_y: List[float]


def is_prime(value: int) -> bool:
    if value < 2:
        return False
    if value in (2, 3):
        return True
    if value % 2 == 0:
        return False
    limit = math.isqrt(value)
    for factor in range(3, limit + 1, 2):
        if value % factor == 0:
            return False
    return True


def riemann_lattice_walk(steps: int, zeros: Iterable[float]) -> WalkData:
    zero_list = list(zeros)
    if not zero_list:
        raise ValueError("At least one Riemann zero must be provided")

    angles = [0.0] * len(zero_list)
    x, y = [0.0], [0.0]
    prime_x: List[float] = []
    prime_y: List[float] = []
    prime_index = 0

    for n in range(1, steps + 1):
        step_x_sum = 0.0
        step_y_sum = 0.0
        prime = is_prime(n)

        for idx, zero_val in enumerate(zero_list):
            if n % 2 == 0:
                angles[idx] += 180.0
            elif not prime:
                rotation_numerator = zero_val * (180.0 / math.pi)
                angles[idx] += rotation_numerator / n

            r_step = 0.0
            if prime:
                sign = 1.0 if prime_index % 2 else -1.0
                r_step = n * sign

            radians = math.radians(angles[idx])
            step_x_sum += r_step * math.cos(radians)
            step_y_sum += r_step * math.sin(radians)

        if prime:
            prime_index += 1

        new_x = x[-1] + step_x_sum
        new_y = y[-1] + step_y_sum
        x.append(new_x)
        y.append(new_y)

        if prime:
            prime_x.append(new_x)
            prime_y.append(new_y)

    return WalkData(x, y, prime_x, prime_y)


def default_zeros() -> List[float]:
    return [
        14.134725,
        21.022040,
        25.010858,
        30.424876,
        32.935062,
        37.586178,
        40.918719,
        43.327073,
        48.005151,
        49.773832,
        52.970321,
        56.446248,
        59.347044,
        60.831779,
        65.112544,
        67.079811,
        69.546402,
        72.067158,
        75.704691,
        77.144840,
        79.337375,
        82.910381,
        84.735493,
        87.425275,
        88.809111,
        92.545723,
        94.651344,
        95.870634,
        98.831194,
        101.317851,
    ]


def plot_lattice(walk: WalkData, steps: int, zero_count: int, output: Path) -> None:
    plt.style.use("dark_background")
    fig, ax = plt.subplots(figsize=(12, 12))

    ax.plot(walk.x, walk.y, color="fuchsia", alpha=0.5, linewidth=0.5, label="Superposition path")
    ax.scatter(walk.prime_x, walk.prime_y, color="cyan", s=1, alpha=0.8, label="Prime extensions")
    ax.scatter([0], [0], color="white", s=50, label="Origin")

    ax.set_aspect("equal", adjustable="datalim")
    ax.set_title(
        f"Riemann lattice using {zero_count} zeros (N={steps})",
        color="white",
    )
    ax.legend(loc="upper right")
    ax.grid(True, alpha=0.1)

    output.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output, dpi=300, bbox_inches="tight")
    plt.close(fig)

    print(f"Wrote lattice plot to {output.resolve()}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Riemann lattice walk with many zeros")
    parser.add_argument("--steps", type=int, default=3_000, help="Sequence length to simulate.")
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("tuning/riemann_lattice.png"),
        help="Path to the output PNG.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    zeros = default_zeros()
    walk = riemann_lattice_walk(args.steps, zeros)
    plot_lattice(walk, args.steps, len(zeros), args.output)


if __name__ == "__main__":
    main()
