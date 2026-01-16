#!/usr/bin/env python3
"""Generate the recursive origin path and its spectral resonance."""
from __future__ import annotations

import argparse
import math
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np


def generate_primes(limit: int) -> list[int]:
    if limit < 2:
        return []
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for value in range(2, math.isqrt(limit) + 1):
        if sieve[value]:
            start = value * value
            step = value
            sieve[start : limit + 1 : step] = b"\x00" * (
                (limit - start) // step + 1
            )
    return [index for index, is_prime in enumerate(sieve) if is_prime]


def generate_recursive_spectral_data(
    max_n: int,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    primes = generate_primes(max_n)
    total_steps = int(sum(primes))
    origin_x = np.empty(len(primes) + 1, dtype=float)
    origin_y = np.empty(len(primes) + 1, dtype=float)
    path_x = np.empty(total_steps + 1, dtype=float)
    path_y = np.empty(total_steps + 1, dtype=float)
    residuals = np.empty(total_steps, dtype=float)
    current_theta = 0.0
    curr_x = 0.0
    curr_y = 0.0
    step_index = 0

    origin_x[0] = 0.0
    origin_y[0] = 0.0
    path_x[0] = 0.0
    path_y[0] = 0.0

    for prime_idx, prime in enumerate(primes):
        sign = 1.0 if prime_idx % 2 == 0 else -1.0
        origin_index = prime_idx + 1
        expected_theta = math.log(origin_index) if origin_index > 1 else 0.0

        for step in range(1, prime + 1):
            current_theta += math.pi / step
            curr_x += step * math.cos(current_theta) * sign
            curr_y += step * math.sin(current_theta) * sign
            step_index += 1
            path_x[step_index] = curr_x
            path_y[step_index] = curr_y
            residuals[step_index - 1] = current_theta - expected_theta

        origin_x[prime_idx + 1] = curr_x
        origin_y[prime_idx + 1] = curr_y

    return (
        path_x,
        path_y,
        origin_x,
        origin_y,
        residuals,
    )


def parse_zeros(value: str) -> list[float]:
    if not value:
        return []
    return [float(item.strip()) for item in value.split(",") if item.strip()]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Plot recursive genesis path and FFT spectrum."
    )
    parser.add_argument(
        "--max-n",
        type=int,
        default=2000,
        help="Upper bound for primes used in the recursive walk.",
    )
    parser.add_argument(
        "--freq-scale",
        type=float,
        default=100.0,
        help="Scale factor applied to FFT frequencies for display.",
    )
    parser.add_argument(
        "--max-freq",
        type=float,
        default=50.0,
        help="Maximum frequency shown on the spectrum panel.",
    )
    parser.add_argument(
        "--zeros",
        type=parse_zeros,
        default=parse_zeros("14.13,21.02,25.01"),
        help="Comma-separated expected zero positions for annotation.",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("tuning/spectral_genesis.png"),
        help="Path for the generated PNG.",
    )
    parser.add_argument("--show", action="store_true", help="Display the plot.")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    (
        path_x,
        path_y,
        origin_x,
        origin_y,
        residuals,
    ) = generate_recursive_spectral_data(args.max_n)

    if residuals.size == 0:
        raise SystemExit("No residuals generated; increase --max-n.")

    spectrum = np.fft.rfft(residuals)
    freqs = np.fft.rfftfreq(residuals.size, d=1.0)
    amplitude = 2.0 / residuals.size * np.abs(spectrum)

    plt.style.use("dark_background")
    fig = plt.figure(figsize=(16, 10))

    ax1 = fig.add_subplot(121)
    ax1.plot(path_x, path_y, color="yellow", alpha=0.6, linewidth=0.5)
    ax1.scatter(
        origin_x,
        origin_y,
        c=np.arange(len(origin_x)),
        cmap="plasma",
        s=10,
        alpha=0.8,
        label="Prime origins",
    )
    ax1.set_title(
        "Recursive Genesis Path\n(Primes as New Big Bang Origins)",
        color="white",
    )
    ax1.set_aspect("equal", adjustable="datalim")
    ax1.legend(loc="upper right")

    ax2 = fig.add_subplot(122)
    ax2.plot(freqs * args.freq_scale, amplitude, color="cyan", linewidth=1.0)
    ax2.set_xlim(0, args.max_freq)
    ax2.set_title(
        "Spectral Resonance Analysis\n(Identifying Hidden Frequencies)",
        color="white",
    )
    ax2.set_xlabel(f"Frequency (scaled by {args.freq_scale:g})", color="white")
    ax2.set_ylabel("Amplitude", color="white")

    if args.zeros:
        peak_height = float(amplitude.max()) if amplitude.size else 1.0
        for zero in args.zeros:
            ax2.axvline(x=zero, color="red", linestyle="--", alpha=0.5)
            ax2.text(
                zero,
                peak_height * 0.9,
                f"$\\gamma$={zero:g}",
                color="red",
                rotation=90,
                ha="right",
                va="top",
            )

    fig.tight_layout()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(args.output, dpi=200, bbox_inches="tight")
    print(f"Wrote spectral genesis plot to {args.output.resolve()}")

    if args.show:
        plt.show()
    else:
        plt.close(fig)


if __name__ == "__main__":
    main()
