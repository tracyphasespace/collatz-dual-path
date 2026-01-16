#!/usr/bin/env python3
"""Visualize the Genesis Sieve polar interference map."""
from __future__ import annotations

import argparse
import math
from pathlib import Path
from typing import List

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


def genesis_sieve_simulation(max_n: int) -> tuple[List[int], List[float], List[float], List[float], List[float]]:
    n_values: List[int] = []
    magnitudes: List[float] = []
    phases: List[float] = []
    composite_colors: List[float] = []
    marker_sizes: List[float] = []

    print(f"Running Genesis Sieve up to N={max_n} …")

    for n in range(2, max_n + 1):
        energy_vector = 0 + 0j
        for k in range(1, n):
            angle = (n / k) * 2 * math.pi
            energy_vector += complex(math.cos(angle), math.sin(angle))

        magnitude = abs(energy_vector)
        phase = math.atan2(energy_vector.imag, energy_vector.real)

        n_values.append(n)
        magnitudes.append(magnitude)
        phases.append(phase)

        if is_prime(n):
            composite_colors.append(float("nan"))
            marker_sizes.append(6.0)
            magnitudes[-1] *= 0.5
        else:
            composite_colors.append(magnitude)
            marker_sizes.append(20.0 + magnitude * 2.0)

    return n_values, magnitudes, phases, composite_colors, marker_sizes


def plot_genesis_sieve(
    n_values: List[int],
    magnitudes: List[float],
    phases: List[float],
    composite_colors: List[float],
    marker_sizes: List[float],
    max_n: int,
    output: Path,
    show_plot: bool,
) -> None:
    plt.style.use("dark_background")
    fig = plt.figure(figsize=(12, 12))
    ax = fig.add_subplot(111, projection="polar")

    comp_indices = [i for i, c in enumerate(composite_colors) if not math.isnan(c)]
    comp_phases = np.array(phases)[comp_indices]
    comp_ns = np.array(n_values)[comp_indices]
    comp_colors = np.array(composite_colors)[comp_indices]
    comp_sizes = np.array(marker_sizes)[comp_indices]

    scatter = ax.scatter(
        comp_phases,
        comp_ns,
        c=comp_colors,
        s=comp_sizes,
        cmap="inferno",
        alpha=0.85,
        label="Composite intersections",
    )
    fig.colorbar(scatter, ax=ax, label="Intersection energy magnitude")

    prime_indices = [i for i, c in enumerate(composite_colors) if math.isnan(c)]
    prime_phases = np.array(phases)[prime_indices]
    prime_ns = np.array(n_values)[prime_indices]
    prime_sizes = np.array(marker_sizes)[prime_indices]

    ax.scatter(
        prime_phases,
        prime_ns,
        c="cyan",
        s=prime_sizes,
        alpha=0.9,
        zorder=5,
        label="Prime voids",
    )

    ax.set_title(
        f"Genesis sieve polar map (N={max_n})\nBright = intersections, cyan = primes",
        color="white",
    )
    ax.set_rticks([max_n // 4, max_n // 2, (3 * max_n) // 4, max_n])
    ax.set_rlabel_position(45)
    ax.legend(loc="lower right")

    max_energy_idx = int(np.argmax(np.array(magnitudes)))
    ax.annotate(
        f"N={n_values[max_energy_idx]}\nmax energy",
        xy=(phases[max_energy_idx], n_values[max_energy_idx]),
        xytext=(phases[max_energy_idx] + 0.3, n_values[max_energy_idx] + max_n * 0.1),
        color="yellow",
        fontsize=10,
        arrowprops=dict(arrowstyle="->", color="yellow"),
    )

    output.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output, dpi=300, bbox_inches="tight")
    print(f"Wrote Genesis sieve plot to {output.resolve()}")

    if show_plot:
        plt.show()
    else:
        plt.close(fig)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Genesis sieve polar visualization")
    parser.add_argument("--max-n", type=int, default=2_000, help="Maximum N to simulate.")
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("tuning/genesis_sieve.png"),
        help="Path to the output PNG.",
    )
    parser.add_argument("--show", action="store_true", help="Display the plot interactively.")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    n_values, magnitudes, phases, composite_colors, marker_sizes = genesis_sieve_simulation(args.max_n)
    plot_genesis_sieve(
        n_values,
        magnitudes,
        phases,
        composite_colors,
        marker_sizes,
        args.max_n,
        args.output,
        show_plot=args.show,
    )


if __name__ == "__main__":
    main()
