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

    # --- MODEL A: STANDARD AMNESIA (Trial Division / Sequential Sieve) ---
    amnesia_ops = []
    amnesia_cumulative_ops = 0

    # --- MODEL B: CLIFFORD LEARNING (Orthogonal Projection) ---
    clifford_ops = []
    clifford_cumulative_ops = 0

    # Basis Primes for the 8D Manifold (4 Orthogonal Planes)
    basis_primes = [2, 3, 5, 7]
    basis_product = 2 * 3 * 5 * 7  # 210

    # Simulating the scan
    step = 1000
    x_axis = []

    for n in range(step, limit + 1, step):
        current_batch = np.arange(n - step, n)
        _ = current_batch  # placeholder to keep variable usage explicit

        # --- AMNESIA COST CALCULATION ---
        batch_ops_amnesia = step * np.log(np.log(n)) * 5
        amnesia_cumulative_ops += batch_ops_amnesia
        amnesia_ops.append(amnesia_cumulative_ops)

        # --- CLIFFORD COST CALCULATION ---
        geometry_overhead = step * 1.5

        survivors = step * (48 / basis_product)
        residual_ops = survivors * np.log(np.log(n)) * 5

        clifford_batch_total = geometry_overhead + residual_ops
        clifford_cumulative_ops += clifford_batch_total
        clifford_ops.append(clifford_cumulative_ops)

        x_axis.append(n)

    # --- PLOTTING ---
    fig, ax = plt.subplots(figsize=(10, 6))

    ax.plot(
        x_axis,
        amnesia_ops,
        label="Standard Sieve ('Amnesia')",
        color="red",
        linestyle="--",
    )
    ax.plot(
        x_axis,
        clifford_ops,
        label="Cl(4,4) Orthogonal Filter ('Learning')",
        color="cyan",
        linewidth=2,
    )

    ax.fill_between(x_axis, amnesia_ops, clifford_ops, color="cyan", alpha=0.1)

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
        max(clifford_ops) * 0.3,
        "Cl(4,4): The Manifold 'Pre-Sieves'\n"
        "77% of candidates instantly\nvia Orthogonal Intersection",
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
        output=f"tuning/clifford_sieve_perf_{timestamp}.png",
    )
