#!/usr/bin/env python3
from datetime import datetime

import matplotlib.pyplot as plt
import numpy as np


def compare_sieve_performance(limit=100000, output=None):
    """
    Simulates the cost/performance of 'Amnesia' (Standard) vs 'Learning' (High-D Topology).
    """
    # 1. SETUP
    candidates = np.arange(1, limit + 1)
    _ = candidates  # keep explicit variable for clarity

    # --- MODEL A: STANDARD AMNESIA (Trial Division / Sequential Sieve) ---
    amnesia_ops = []
    amnesia_cumulative_ops = 0

    # --- MODEL B: CLIFFORD LEARNING (Orthogonal Projection) ---
    basis_sets = [
        ("Cl(2,2) 4D Filter", [2, 3], "lightskyblue"),
        ("Cl(3,3) 6D Filter", [2, 3, 5], "deepskyblue"),
        ("Cl(4,4) 8D Filter", [2, 3, 5, 7], "cyan"),
        ("Cl(5,5) 10D Filter", [2, 3, 5, 7, 11], "mediumspringgreen"),
        ("Cl(6,6) 12D Filter", [2, 3, 5, 7, 11, 13], "lime"),
    ]

    # Simulating the scan
    step = 1000
    x_axis = []

    clifford_curves = {label: [] for label, _, _ in basis_sets}
    clifford_cumulative = {label: 0.0 for label, _, _ in basis_sets}

    for n in range(step, limit + 1, step):
        current_batch = np.arange(n - step, n)
        _ = current_batch

        # --- AMNESIA COST CALCULATION ---
        log_n = np.log(n) if n > 1 else 1
        _ = n / log_n

        factor = np.log(np.log(n)) if n > 2 else 1
        batch_ops_amnesia = step * factor * 5
        amnesia_cumulative_ops += batch_ops_amnesia
        amnesia_ops.append(amnesia_cumulative_ops)

        # --- CLIFFORD COST CALCULATION (6D / 8D) ---
        for label, primes, _ in basis_sets:
            geometry_overhead = step * 1.5
            basis_product = 1
            for p in primes:
                basis_product *= p
            phi = basis_product
            for p in primes:
                phi *= (p - 1)
                phi //= p
            survivors_ratio = phi / basis_product
            survivors = step * survivors_ratio
            residual_ops = survivors * factor * 5

            clifford_batch_total = geometry_overhead + residual_ops
            clifford_cumulative[label] += clifford_batch_total
            clifford_curves[label].append(clifford_cumulative[label])

        x_axis.append(n)

    # --- PLOTTING ---
    fig, ax = plt.subplots(figsize=(10, 6))

    ax.plot(x_axis, amnesia_ops, label="Standard Sieve ('Amnesia')", color="red", linestyle="--")
    for label, _, color in basis_sets:
        ax.plot(
            x_axis,
            clifford_curves[label],
            label=label,
            color=color,
            linewidth=2,
        )

    ax.fill_between(
        x_axis,
        amnesia_ops,
        clifford_curves[basis_sets[-1][0]],
        color="cyan",
        alpha=0.1,
    )

    ax.set_title("Cost vs Performance: 1D Arithmetic vs 8D Geometry")
    ax.set_xlabel("Search Frontier (N)")
    ax.set_ylabel("Cumulative Computational Operations (Cost)")
    ax.legend()
    ax.grid(True, alpha=0.3)

    ax.text(
        limit * 0.05,
        max(amnesia_ops) * 0.8,
        "Standard: Linear cost increase\n(Must re-check factors)",
        color="red",
    )
    ax.text(
        limit * 0.4,
        max(amnesia_ops) * 0.3,
        "Cl(n,n): Orthogonal pre-sieves\n"
        "remove candidates by modular gates",
        color="teal",
        bbox=dict(facecolor="white", alpha=0.8),
    )

    fig.tight_layout()
    if output:
        fig.savefig(output, dpi=200, bbox_inches="tight")
        print(f"Wrote plot to {output}")
        plt.close(fig)
    else:
        plt.show()


if __name__ == "__main__":
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    compare_sieve_performance(
        limit=1_000_000,
        output=f"tuning/clifford_efficiency_{timestamp}.png",
    )
