#!/usr/bin/env python3
from datetime import datetime

import matplotlib.pyplot as plt
import numpy as np


def generate_fractal_wheel(limit_prime_index=6):
    """
    Generates the 'Dust' pattern of admissible prime locations
    by recursively growing the constellation.
    NO SIEVING. PURE PREDICTION.
    """
    constellation = [0]
    primorial = 1

    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]

    history_density = []

    print("--- Fractal Growth of the Prime Tunnel ---")

    for i in range(limit_prime_index):
        p = primes[i]

        # 1. CLONE
        new_constellation = []
        for k in range(p):
            shift = k * primorial
            for c in constellation:
                new_constellation.append(c + shift)

        # 2. PREDICT & PRUNE
        survivors = []
        for x in new_constellation:
            if (x % p) != 0:
                survivors.append(x)

        constellation = survivors
        primorial *= p

        density = len(constellation) / primorial
        history_density.append(density)

        print(
            f"Level {p}: Period {primorial:,} | Survivors {len(constellation):,} | "
            f"Density {density:.4f}"
        )

    return primes[:limit_prime_index], history_density


def visualize_fractal_density(primes, density, output=None):
    plt.figure(figsize=(10, 6))

    theoretical = []
    val = 1.0
    for p in primes:
        val *= (1 - 1 / p)
        theoretical.append(val)

    plt.plot(primes, density, marker="o", label="Fractal Dust Density", color="cyan", linewidth=3)
    plt.plot(
        primes,
        theoretical,
        linestyle="--",
        color="white",
        alpha=0.5,
        label="Theoretical Limit (1-1/p)",
    )

    plt.title("The 'Zero Volume' Convergence")
    plt.xlabel("Fractal Iteration (Prime Surface Added)")
    plt.ylabel("Tunnel Density (Volume)")
    plt.grid(True, alpha=0.3)
    plt.legend()

    plt.tight_layout()
    if output:
        plt.savefig(output, dpi=200, bbox_inches="tight")
        print(f"Wrote plot to {output}")
        plt.close()
    else:
        plt.show()


if __name__ == "__main__":
    p_list, densities = generate_fractal_wheel(limit_prime_index=6)
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    visualize_fractal_density(
        p_list,
        densities,
        output=f"tuning/fractal_wheel_density_{timestamp}.png",
    )
