#!/usr/bin/env python3
"""Simulate the Clifford walk using superposed rotations from several Riemann zeros."""
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


def riemann_superposition_walk(steps: int, zeros: Iterable[float]) -> WalkData:
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
                sign = 1.0 if prime_index % 2 == 0 else -1.0
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


def plot_superposition(walk: WalkData, steps: int, zeros: List[float], output: Path) -> None:
    plt.style.use("dark_background")
    fig, ax = plt.subplots(figsize=(12, 12))

    ax.plot(walk.x, walk.y, color="cyan", alpha=0.5, linewidth=0.6, label="Superposition path")
    ax.scatter(walk.prime_x, walk.prime_y, color="white", s=2, alpha=0.6, label="Prime extensions")
    ax.scatter([0], [0], color="red", s=50, label="Origin")

    ax.set_aspect("equal", adjustable="datalim")
    zero_str = ", ".join(f"{z:.2f}" for z in zeros)
    ax.set_title(
        f"Superposition of zeros [{zero_str}] (N={steps})",
        color="white",
    )
    ax.legend(loc="upper right")
    ax.grid(True, alpha=0.1)

    output.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output, dpi=300, bbox_inches="tight")
    plt.close(fig)

    print(f"Wrote superposition plot to {output.resolve()}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Riemann zero superposition walk")
    parser.add_argument("--steps", type=int, default=5_000, help="Sequence length to simulate.")
    parser.add_argument(
        "--zeros",
        type=float,
        nargs="*",
        default=[14.134725, 21.02204, 25.010858],
        help="Imaginary parts of Riemann zeros to include.",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("tuning/riemann_superposition.png"),
        help="Path to the output PNG.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    walk = riemann_superposition_walk(args.steps, args.zeros)
    plot_superposition(walk, args.steps, args.zeros, args.output)


if __name__ == "__main__":
    main()
