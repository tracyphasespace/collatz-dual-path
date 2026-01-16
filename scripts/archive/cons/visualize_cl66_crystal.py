#!/usr/bin/env python3
from datetime import datetime

import matplotlib.pyplot as plt
import numpy as np


def miller_rabin(n):
    if n < 2:
        return False
    if n == 2 or n == 3:
        return True
    if n % 2 == 0:
        return False
    r, d = 0, n - 1
    while d % 2 == 0:
        r += 1
        d //= 2
    for _ in range(5):
        a = np.random.randint(2, n - 1)
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True


def visualize_cl66_crystal(start=100000, end=105000, output=None):
    # We map N into the Phase Space of Cl(6,6) (Mod 11, 13, 17)
    data_primes = []
    data_composites = []

    for n in range(start, end):
        # The coordinates in the 3-Torus
        x = n % 11
        y = n % 13
        z = n % 17

        # Check if it hits the "Walls" of this specific sub-manifold
        on_wall = (x == 0) or (y == 0) or (z == 0)

        is_p = miller_rabin(n)

        if is_p:
            data_primes.append([x, y, z])
        elif on_wall:
            data_composites.append([x, y, z])

    primes = np.array(data_primes)
    walls = np.array(data_composites)

    fig = plt.figure(figsize=(12, 10))
    ax = fig.add_subplot(111, projection="3d")

    if len(walls):
        ax.scatter(
            walls[:, 0],
            walls[:, 1],
            walls[:, 2],
            c="black",
            alpha=0.05,
            marker="s",
            s=100,
            label="Composite Walls (11,13,17)",
        )

    if len(primes):
        ax.scatter(
            primes[:, 0],
            primes[:, 1],
            primes[:, 2],
            c="cyan",
            edgecolors="blue",
            s=50,
            alpha=0.8,
            label="Primes (The Vacuum)",
        )

    ax.set_xlabel("Phase Dimension 11")
    ax.set_ylabel("Phase Dimension 13")
    ax.set_zlabel("Phase Dimension 17")
    ax.set_title('Inside the Cl(6,6) Crystal: Primes as "Vacuum Bubbles"')

    ax.text(
        0,
        0,
        20,
        "Insight: Primes exist only in the\n'Safe Volumes' between the walls.",
        color="blue",
    )

    plt.legend()
    plt.tight_layout()

    if output:
        fig.savefig(output, dpi=200, bbox_inches="tight")
        print(f"Wrote plot to {output}")
        plt.close(fig)
    else:
        plt.show()


if __name__ == "__main__":
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    visualize_cl66_crystal(output=f"tuning/cl66_crystal_{timestamp}.png")
