#!/usr/bin/env python3
"""Analyze the accumulated rotation of the Clifford walk vs. a log trend."""
from __future__ import annotations

import argparse
import math
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np


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


def mc_sheery_phase_analysis(steps: int) -> tuple[list[int], list[float]]:
    theta_total = 0.0
    prime_values: list[int] = []
    prime_angles: list[float] = []

    for n in range(1, steps + 1):
        if n % 2 == 0:
            theta_total += 180.0
        elif not is_prime(n):
            theta_total += 180.0 / n
        else:
            prime_values.append(n)
            prime_angles.append(theta_total)

    return prime_values, prime_angles


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Plot accumulated rotation vs. log trend for the Clifford walk."
    )
    parser.add_argument(
        "--steps",
        type=int,
        default=10_000,
        help="Number sequence length to analyze.",
    )
    parser.add_argument(
        "-o",
        "--output",
        type=Path,
        default=Path("phase_analysis"),
        help="Directory where PNGs will be written.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    steps = args.steps
    output_dir = args.output
    output_dir.mkdir(parents=True, exist_ok=True)

    p_vals, p_angles = mc_sheery_phase_analysis(steps)

    coeffs = np.polyfit(np.log(p_vals), p_angles, 1)
    trend_line = coeffs[0] * np.log(p_vals) + coeffs[1]

    plt.style.use("dark_background")
    fig1, ax1 = plt.subplots(figsize=(12, 6))
    ax1.plot(p_vals, p_angles, color="cyan", linewidth=1.0, label="Accumulated rotation")
    ax1.plot(
        p_vals,
        trend_line,
        color="white",
        linestyle="--",
        alpha=0.5,
        label="Log trend (fit)",
    )
    ax1.set_title(
        f"Clifford Walk phase unrolling (N={steps})\nAngle growth vs. log trend",
        color="white",
    )
    ax1.set_xlabel("Prime value", color="white")
    ax1.set_ylabel("Total accumulated angle (deg)", color="white")
    ax1.grid(True, alpha=0.2)
    ax1.legend()
    fig1.tight_layout()
    fig1.savefig(
        output_dir / f"phase_unrolling_{steps}.png",
        dpi=200,
        bbox_inches="tight",
    )

    residuals = np.array(p_angles) - trend_line
    fig2, ax2 = plt.subplots(figsize=(12, 4))
    ax2.plot(p_vals, residuals, color="red", linewidth=0.8)
    ax2.axhline(0, color="white", alpha=0.3)
    ax2.set_title("Deviation from logarithmic growth", color="white")
    ax2.set_xlabel("Prime value", color="white")
    ax2.set_ylabel("Phase deviation", color="white")
    ax2.grid(True, alpha=0.2)
    fig2.tight_layout()
    fig2.savefig(
        output_dir / f"phase_residuals_{steps}.png",
        dpi=200,
        bbox_inches="tight",
    )

    plt.close(fig1)
    plt.close(fig2)

    print(f"Wrote plots to {output_dir.resolve()}")


if __name__ == "__main__":
    main()
