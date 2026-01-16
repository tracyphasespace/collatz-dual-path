#!/usr/bin/env python3
"""Experiment with a Riemann-zero-tuned rotation in the Clifford walk."""
from __future__ import annotations

import argparse
import math
from dataclasses import dataclass
from pathlib import Path
from typing import List

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


def mc_sheery_riemann_tuning(steps: int, zero_val: float) -> WalkData:
    radius = 0.0
    heading = 0.0  # degrees

    x, y = [0.0], [0.0]
    prime_x: List[float] = []
    prime_y: List[float] = []
    prime_index = 0

    rotation_numerator = zero_val * (180.0 / math.pi)

    for n in range(1, steps + 1):
        if n % 2 == 0:
            heading += 180.0
            continue

        if is_prime(n):
            prime_index += 1
            sign = 1.0 if prime_index % 2 else -1.0
            radius = n * sign

            radians = math.radians(heading)
            next_x = radius * math.cos(radians)
            next_y = radius * math.sin(radians)

            x.append(next_x)
            y.append(next_y)
            prime_x.append(next_x)
            prime_y.append(next_y)
        else:
            heading += rotation_numerator / n

    return WalkData(x, y, prime_x, prime_y)


def plot_walk(walk: WalkData, steps: int, zero_val: float, output: Path) -> None:
    plt.style.use("dark_background")
    fig, ax = plt.subplots(figsize=(12, 12))

    ax.plot(walk.x, walk.y, color="lime", alpha=0.4, linewidth=0.5, label="Riemann tuned path")
    ax.scatter(walk.prime_x, walk.prime_y, color="white", s=2, alpha=0.6, label="Prime extensions")
    ax.scatter([0], [0], color="red", s=40, label="Origin")

    ax.set_aspect("equal", adjustable="datalim")
    ax.set_title(
        f"Clifford walk tuned to zero {zero_val:.6f} (N={steps})",
        color="white",
    )
    ax.grid(True, alpha=0.1)
    ax.legend(loc="upper right")

    output.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output, dpi=300, bbox_inches="tight")
    plt.close(fig)

    print(f"Wrote tuned plot to {output.resolve()}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Tune Clifford walk rotations by a Riemann zero")
    parser.add_argument("--steps", type=int, default=10_000, help="Sequence length to simulate.")
    parser.add_argument("--zero", type=float, default=14.134725, help="Riemann zero value to use.")
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("tuning/clifford_riemann_zero.png"),
        help="Path to the output PNG.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    walk = mc_sheery_riemann_tuning(args.steps, args.zero)
    plot_walk(walk, args.steps, args.zero, args.output)


if __name__ == "__main__":
    main()
