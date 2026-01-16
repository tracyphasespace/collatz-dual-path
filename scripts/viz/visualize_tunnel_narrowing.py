#!/usr/bin/env python3
from datetime import datetime

import matplotlib.pyplot as plt
import numpy as np


def visualize_tunnel_narrowing(limit=1000, output=None):
    """
    Demonstrates how adding prime surfaces reduces the search space
    from a random cloud to a deterministic tunnel.
    """
    # 1. Start with the "Universe" (All integers)
    universe = np.arange(1, limit + 1)
    # We define the "Search Space" as initially 100% of the universe
    valid_candidates = np.ones(limit, dtype=bool)

    # We will track the "Entropy" (Search Space Size) as we add primes
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    history = []

    fig, axes = plt.subplots(1, 2, figsize=(15, 6))

    # --- VISUALIZATION 1: The Tunnel (1D Barcode) ---
    # We'll plot the first 100 numbers as a "Barcode" to show gaps appearing
    barcode_limit = 100
    barcode_data = []

    current_valid = np.ones(barcode_limit, dtype=bool)

    for p in primes:
        # 2. Apply the Surface (Remove multiples of p)
        # In logic: valid = valid AND (n % p != 0)
        # In geometry: This is an intersection of the current space with the "Not-P" manifold
        mask = (universe % p != 0) | (universe == p)  # Keep the prime itself
        valid_candidates &= mask

        # Track volume remaining
        remaining_volume = np.sum(valid_candidates)
        history.append(remaining_volume)

        # Update barcode data
        mask_barcode = (np.arange(1, barcode_limit + 1) % p != 0) | (
            np.arange(1, barcode_limit + 1) == p
        )
        current_valid &= mask_barcode
        barcode_data.append(current_valid.copy())

    # Plotting the Entropy Drop
    ax1 = axes[0]
    ax1.plot(primes, history, marker="o", linestyle="-", color="cyan", linewidth=2)
    ax1.set_title("Search Space Reduction (The 'Crossover' Approach)")
    ax1.set_xlabel("Surface Added (Prime P)")
    ax1.set_ylabel("Remaining Candidate Volume (Search Space)")
    ax1.grid(True, alpha=0.3)

    # Add annotation explaining the curve
    ax1.text(primes[2], history[2], "Exponential Drop\n(Initial Filtering)", color="yellow")
    ax1.text(primes[-1], history[-1], "Asymptotic Tail\n(The 'Tunnel' forms)", color="lime")

    # Plotting the Barcode Tunnel
    ax2 = axes[1]
    barcode_data = np.array(barcode_data)
    # Invert for plotting: Black = Eliminated (Wall), White = Valid (Tunnel)
    ax2.imshow(barcode_data, aspect="auto", cmap="binary_r", interpolation="nearest")

    ax2.set_title("The 'Tunnel' Forming in Real-Time")
    ax2.set_xlabel("Number Line (1 to 100)")
    ax2.set_ylabel("Surfaces Applied (2 -> 29)")
    ax2.set_yticks(range(len(primes)))
    ax2.set_yticklabels(primes)

    plt.tight_layout()
    if output:
        fig.savefig(output, dpi=200, bbox_inches="tight")
        print(f"Wrote plot to {output}")
        plt.close(fig)
    else:
        plt.show()


if __name__ == "__main__":
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    visualize_tunnel_narrowing(
        limit=5000,
        output=f"tuning/tunnel_narrowing_{timestamp}.png",
    )
