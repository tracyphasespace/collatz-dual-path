#!/usr/bin/env python3
"""Generate a Clifford Walk PNG via the CLI."""
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
    prime_values: List[int]


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


def clifford_walk(steps: int) -> WalkData:
    if steps < 1:
        raise ValueError("steps must be at least 1")

    radius = 0.0
    heading = 0.0  # degrees, facing east

    x, y = [0.0], [0.0]
    prime_x: List[float] = []
    prime_y: List[float] = []
    prime_values: List[int] = []
    prime_index = 0

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
            prime_values.append(n)
        else:
            heading += 180.0 / n

    return WalkData(x, y, prime_x, prime_y, prime_values)


def plot_walk(
    walk: WalkData,
    steps: int,
    output: Path,
    dpi: int,
    width: float,
    height: float,
    theme: str,
    show_plot: bool,
) -> None:
    if theme == "dark":
        plt.style.use("dark_background")
        colors = {
            "path": "#46C7FF",
            "primes": "#FFE066",
            "origin": "#FF5959",
            "grid_alpha": 0.25,
            "title": "white",
        }
    else:
        plt.style.use("default")
        colors = {
            "path": "#1E7F8C",
            "primes": "#C62828",
            "origin": "#9C27B0",
            "grid_alpha": 0.35,
            "title": "black",
        }

    fig, ax = plt.subplots(figsize=(width, height))
    ax.plot(walk.x, walk.y, color=colors["path"], alpha=0.35, linewidth=0.5, label="Path")
    if walk.prime_x:
        ax.scatter(
            walk.prime_x,
            walk.prime_y,
            color=colors["primes"],
            s=15,
            zorder=5,
            label="Prime extensions",
        )
        # Labels are disabled by default to keep dense plots readable.
        # for px, py, value in zip(walk.prime_x, walk.prime_y, walk.prime_values):
        #     ax.annotate(
        #         str(value),
        #         (px, py),
        #         textcoords="offset points",
        #         xytext=(0, 6),
        #         ha="center",
        #         color=colors["primes"],
        #         fontsize=8,
        #         alpha=0.85,
        #     )
    ax.scatter(
        [walk.x[0]],
        [walk.y[0]],
        color=colors["origin"],
        s=40,
        zorder=6,
        label="Origin",
    )

    ax.set_aspect("equal", adjustable="datalim")
    ax.set_title(
        f"Clifford Walk (N={steps})\nPrimes set ±radius=value | Composites rotate heading",
        color=colors["title"],
    )
    ax.grid(True, alpha=colors["grid_alpha"])
    ax.legend(loc="upper right")

    output.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output, dpi=dpi, bbox_inches="tight")
    print(f"Wrote {output.resolve()}")

    if show_plot:
        plt.show()

    plt.close(fig)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate a Clifford Walk image.")
    parser.add_argument("--steps", type=int, default=5000, help="Number of steps to simulate.")
    parser.add_argument(
        "-o",
        "--output",
        type=Path,
        default=Path("clifford_walk.png"),
        help="Path to the PNG that will be written.",
    )
    parser.add_argument("--dpi", type=int, default=300, help="Image DPI.")
    parser.add_argument("--width", type=float, default=12.0, help="Figure width in inches.")
    parser.add_argument("--height", type=float, default=10.0, help="Figure height in inches.")
    parser.add_argument(
        "--theme",
        choices=("dark", "light"),
        default="dark",
        help="Color theme for the plot.",
    )
    parser.add_argument(
        "--show",
        action="store_true",
        help="Display the plot window after saving the PNG.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    walk = clifford_walk(args.steps)
    plot_walk(
        walk=walk,
        steps=args.steps,
        output=args.output,
        dpi=args.dpi,
        width=args.width,
        height=args.height,
        theme=args.theme,
        show_plot=args.show,
    )


if __name__ == "__main__":
    main()
