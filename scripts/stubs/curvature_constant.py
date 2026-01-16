#!/usr/bin/env python3
"""Compute the cumulative curvature constant for the Clifford spiral."""
from __future__ import annotations

import argparse
import math
from pathlib import Path


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


def calculate_curvature_constant(max_n: int) -> tuple[float, float, int]:
    total_theta = 0.0
    prime_count = 0

    for n in range(1, max_n + 1):
        total_theta += math.pi / n
        if is_prime(n):
            prime_count += 1

    curvature_constant = total_theta / math.log(max_n)
    return curvature_constant, total_theta, prime_count


def write_summary(
    max_n: int,
    curvature_constant: float,
    total_theta: float,
    prime_count: int,
    output: Path,
) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("w", encoding="utf-8") as fh:
        fh.write(f"Max N: {max_n}\n")
        fh.write(f"Prime count π(N): {prime_count}\n")
        fh.write(f"Total rotation θ(N): {total_theta:.12f} rad\n")
        fh.write(f"θ(N)/ln N = {curvature_constant:.12f}\n")
        fh.write(f"θ(N)/π = {total_theta / math.pi:.12f}\n")
        fh.write(f"ln(N): {math.log(max_n):.12f}\n")
    print(f"Wrote curvature summary to {output.resolve()}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Calculate the Clifford spiral curvature constant")
    parser.add_argument("--max-n", type=int, default=100_000, help="Upper bound for the harmonic sum.")
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("tuning/curvature_summary.txt"),
        help="Where to store the numeric summary.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    curvature_constant, total_theta, prime_count = calculate_curvature_constant(args.max_n)
    print(f"Max N: {args.max_n}")
    print(f"Prime count π(N): {prime_count}")
    print(f"Total rotation θ(N): {total_theta:.12f} rad")
    print(f"Curvature constant C = θ(N)/ln N: {curvature_constant:.12f}")
    write_summary(args.max_n, curvature_constant, total_theta, prime_count, args.output)


if __name__ == "__main__":
    main()
