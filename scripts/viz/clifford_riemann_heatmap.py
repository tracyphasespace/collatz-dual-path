#!/usr/bin/env python3
"""Render a density heatmap from a Riemann-zero superposition walk."""
from __future__ import annotations

import argparse
import math
from pathlib import Path
from typing import List

import matplotlib.pyplot as plt

try:
    import mpmath

    HAVE_MPMATH = True
except ImportError:  # pragma: no cover - optional dependency
    HAVE_MPMATH = False
    mpmath = None  # type: ignore[assignment]


FALLBACK_ZEROS: List[float] = [
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

RAD_TO_DEG = 180.0 / math.pi


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


def get_zeros(requested: int) -> List[float]:
    if requested < 1:
        raise ValueError("requested zero count must be positive")
    if HAVE_MPMATH:
        print(f"Generating first {requested} Riemann zeros via mpmath…")
        return [float(mpmath.zetazero(idx).imag) for idx in range(1, requested + 1)]

    available = min(requested, len(FALLBACK_ZEROS))
    if requested > len(FALLBACK_ZEROS):
        print(
            f"mpmath not installed; using fallback {available} zeros "
            f"instead of requested {requested}."
        )
    return FALLBACK_ZEROS[:available]


def riemann_heatmap_walk(steps: int, zero_count: int) -> tuple[List[float], List[float]]:
    zeros = get_zeros(zero_count)
    zero_count = len(zeros)
    print(f"Simulating interference of {zero_count} zeros for N={steps}.")

    angles = [0.0] * zero_count
    x, y = [0.0], [0.0]
    prime_index = 0

    for n in range(1, steps + 1):
        step_x_sum = 0.0
        step_y_sum = 0.0
        prime = is_prime(n)

        for idx, zero_val in enumerate(zeros):
            if n % 2 == 0:
                angles[idx] += 180.0
            elif not prime:
                angles[idx] += (zero_val * RAD_TO_DEG) / n

            r_step = 0.0
            if prime:
                sign = 1.0 if prime_index % 2 == 0 else -1.0
                r_step = (n * sign) / math.sqrt(zero_count)

            radians = math.radians(angles[idx])
            step_x_sum += r_step * math.cos(radians)
            step_y_sum += r_step * math.sin(radians)

        if prime:
            prime_index += 1

        new_x = x[-1] + step_x_sum
        new_y = y[-1] + step_y_sum

        x.append(new_x)
        y.append(new_y)

    return x, y


def plot_heatmap(
    x: List[float],
    y: List[float],
    steps: int,
    zero_count: int,
    output: Path,
    gridsize: int,
    overlay: bool,
) -> None:
    plt.style.use("dark_background")
    fig, ax = plt.subplots(figsize=(12, 10))

    hb = ax.hexbin(
        x,
        y,
        gridsize=gridsize,
        cmap="inferno",
        mincnt=1,
        bins="log",
    )
    fig.colorbar(hb, ax=ax, label="Log density of walker")

    if overlay:
        ax.plot(x, y, color="cyan", alpha=0.15, linewidth=0.3, label="Trajectory overlay")

    ax.scatter([0], [0], color="white", s=20, label="Origin")
    ax.set_title(
        f"Riemann quantum lattice (zeros={zero_count}, N={steps})",
        color="white",
    )
    ax.set_aspect("equal", adjustable="datalim")
    ax.grid(True, alpha=0.05)
    ax.legend(loc="upper right")

    output.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output, dpi=300, bbox_inches="tight")
    plt.close(fig)

    print(f"Wrote density plot to {output.resolve()}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Render a heatmap from many Riemann zeros.")
    parser.add_argument("--steps", type=int, default=8_000, help="Sequence length to simulate.")
    parser.add_argument(
        "--zeros",
        type=int,
        default=100,
        help="Number of Riemann zeros to superpose (requires mpmath beyond 30).",
    )
    parser.add_argument(
        "--gridsize",
        type=int,
        default=120,
        help="Hexbin grid resolution for the density plot.",
    )
    parser.add_argument(
        "--no-overlay",
        action="store_true",
        help="Disable plotting the faint trajectory overlay.",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("tuning/riemann_heatmap.png"),
        help="PNG path for the heatmap.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    x, y = riemann_heatmap_walk(args.steps, args.zeros)
    plot_heatmap(
        x,
        y,
        steps=args.steps,
        zero_count=args.zeros,
        output=args.output,
        gridsize=args.gridsize,
        overlay=not args.no_overlay,
    )


if __name__ == "__main__":
    main()
