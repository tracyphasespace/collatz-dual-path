#!/usr/bin/env python3
"""Visualize wheel-factorized prime channels on a polar spiral."""
from __future__ import annotations

import argparse
import math
from pathlib import Path
from typing import List

import matplotlib.pyplot as plt


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


def composite_moire_channels(max_n: int, wheel_size: int) -> tuple[List[float], List[float], List[str], List[float]]:
    thetas: List[float] = []
    radii: List[float] = []
    colors: List[str] = []
    sizes: List[float] = []

    for n in range(1, max_n + 1):
        r = math.sqrt(n)
        theta_rad = (n / wheel_size) * 2 * math.pi

        thetas.append(theta_rad)
        radii.append(r)

        if n % 2 == 0 or n % 3 == 0 or n % 5 == 0:
            colors.append("red")
            sizes.append(5)
        elif is_prime(n):
            colors.append("cyan")
            sizes.append(25)
        else:
            colors.append("gold")
            sizes.append(10)

    return thetas, radii, colors, sizes


def plot_prime_channels(
    thetas: List[float],
    radii: List[float],
    colors: List[str],
    sizes: List[float],
    wheel_size: int,
    output: Path,
    show_plot: bool,
) -> None:
    plt.style.use("dark_background")
    fig = plt.figure(figsize=(12, 12))
    ax = fig.add_subplot(111, projection="polar")

    ax.scatter(thetas, radii, c=colors, s=sizes, alpha=0.6)

    spokes = [1, 7, 11, 13, 17, 19, 23, 29]
    max_r = max(radii)
    for s in spokes:
        angle = (s / wheel_size) * 2 * math.pi
        ax.annotate(
            f"Ray {s}",
            xy=(angle, max_r),
            color="cyan",
            ha="center",
            fontsize=10,
            fontweight="bold",
        )

    ax.set_title(
        f"Prime channels tuned to mod {wheel_size}\nRed=2/3/5 walls, cyan=primes, gold=composites of larger primes",
        color="white",
    )
    ax.set_rticks([])
    ax.set_yticklabels([])
    ax.grid(True, alpha=0.2)

    output.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output, dpi=300, bbox_inches="tight")
    print(f"Wrote prime channel visualization to {output.resolve()}")

    if show_plot:
        plt.show()
    else:
        plt.close(fig)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Prime channel polar visualization")
    parser.add_argument("--max-n", type=int, default=2_000, help="Maximum n to render.")
    parser.add_argument("--wheel", type=int, default=30, help="Wheel size (e.g., 6, 30).")
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("tuning/prime_channels.png"),
        help="Path to output PNG.",
    )
    parser.add_argument("--show", action="store_true", help="Display figure interactively.")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    thetas, radii, colors, sizes = composite_moire_channels(args.max_n, args.wheel)
    plot_prime_channels(
        thetas,
        radii,
        colors,
        sizes,
        args.wheel,
        args.output,
        show_plot=args.show,
    )


if __name__ == "__main__":
    main()
