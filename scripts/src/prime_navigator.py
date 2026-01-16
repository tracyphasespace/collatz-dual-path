#!/usr/bin/env python3
"""Predict prime jumps using a log-polar spectral heuristic and score accuracy."""
from __future__ import annotations

import argparse
import math
from pathlib import Path

import numpy as np


def prime_sieve(limit: int) -> list[int]:
    if limit < 2:
        return []
    sieve = np.ones(limit + 1, dtype=bool)
    sieve[:2] = False
    for value in range(2, math.isqrt(limit) + 1):
        if sieve[value]:
            sieve[value * value : limit + 1 : value] = False
    return np.flatnonzero(sieve).tolist()


def ensure_primes(limit: int, primes: list[int], current_limit: int) -> tuple[list[int], int]:
    if limit <= current_limit:
        return primes, current_limit
    primes = prime_sieve(limit)
    return primes, limit


def is_prime(value: int, primes: list[int], prime_limit: int) -> tuple[bool, list[int], int]:
    if value < 2:
        return False, primes, prime_limit
    if value in (2, 3):
        return True, primes, prime_limit
    if value % 2 == 0:
        return False, primes, prime_limit
    needed_limit = math.isqrt(value)
    primes, prime_limit = ensure_primes(needed_limit, primes, prime_limit)
    for prime in primes:
        if prime * prime > value:
            break
        if value % prime == 0:
            return False, primes, prime_limit
    return True, primes, prime_limit


def next_prime(value: int, primes: list[int], prime_limit: int) -> tuple[int, list[int], int]:
    if value < 2:
        return 2, primes, prime_limit
    candidate = value + 1
    if candidate == 3:
        return 3, primes, prime_limit
    if candidate % 2 == 0:
        candidate += 1
    while True:
        is_p, primes, prime_limit = is_prime(candidate, primes, prime_limit)
        if is_p:
            return candidate, primes, prime_limit
        candidate += 2


def parse_zeros(raw: str) -> list[float]:
    if not raw:
        return []
    return [float(item.strip()) for item in raw.split(",") if item.strip()]


def spectral_wobble(log_p: float, zeros: list[float]) -> float:
    if not zeros:
        return 0.0
    wobble = 0.0
    for gamma in zeros:
        wobble += math.sin(gamma * log_p) / gamma
    return wobble / len(zeros)


def predict_next_prime_gap(
    current_prime: int,
    zeros: list[float],
    curvature_constant: float,
) -> int:
    log_p = math.log(current_prime)
    base_gap = log_p
    wobble = spectral_wobble(log_p, zeros)
    predicted_increment = base_gap * (1.0 + wobble / curvature_constant)
    if predicted_increment < 1.0:
        predicted_increment = 1.0
    return int(math.ceil(predicted_increment))


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Prime navigation heuristic based on log-polar spectral phase."
    )
    parser.add_argument(
        "--start",
        type=int,
        default=10_007,
        help="Starting value (will snap to next prime if needed).",
    )
    parser.add_argument(
        "--count",
        type=int,
        default=200,
        help="Number of prime steps to evaluate.",
    )
    parser.add_argument(
        "--window",
        type=int,
        default=10,
        help="Window size after the predicted jump to count as a hit.",
    )
    parser.add_argument(
        "--curvature",
        type=float,
        default=3.299,
        help="Curvature constant used in the phase-lock heuristic.",
    )
    parser.add_argument(
        "--zeros",
        type=parse_zeros,
        default=parse_zeros("14.1347,21.0220,25.0109"),
        help="Comma-separated Riemann zero frequencies.",
    )
    parser.add_argument(
        "--samples",
        type=int,
        default=5,
        help="Number of per-step samples to print.",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=None,
        help="Optional CSV output path for detailed results.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    primes, prime_limit = ensure_primes(
        math.isqrt(max(3, args.start + args.count * 50)),
        [],
        0,
    )

    current = args.start
    is_p, primes, prime_limit = is_prime(current, primes, prime_limit)
    if not is_p:
        current, primes, prime_limit = next_prime(current, primes, prime_limit)
        print(f"Adjusted start to next prime: {current}")

    rows: list[str] = []
    hits = 0
    abs_errors: list[int] = []
    signed_errors: list[int] = []

    for step in range(args.count):
        predicted_gap = predict_next_prime_gap(current, args.zeros, args.curvature)
        predicted_target = current + predicted_gap
        actual_next, primes, prime_limit = next_prime(current, primes, prime_limit)
        actual_gap = actual_next - current
        hit = predicted_target <= actual_next <= predicted_target + args.window
        error = predicted_target - actual_next

        hits += int(hit)
        abs_errors.append(abs(error))
        signed_errors.append(error)

        if step < args.samples:
            print(
                f"p={current} | predicted_gap={predicted_gap} | "
                f"actual_gap={actual_gap} | error={error} | hit={hit}"
            )

        if args.output:
            rows.append(
                f"{current},{predicted_gap},{actual_gap},{predicted_target},"
                f"{actual_next},{error},{int(hit)}"
            )

        current = actual_next

    hit_rate = hits / args.count if args.count else 0.0
    abs_errors_np = np.array(abs_errors, dtype=float)
    signed_errors_np = np.array(signed_errors, dtype=float)
    print(
        "Summary: "
        f"steps={args.count}, hit_rate={hit_rate:.3f}, "
        f"mae={abs_errors_np.mean():.3f}, "
        f"median_abs={np.median(abs_errors_np):.3f}, "
        f"bias={signed_errors_np.mean():.3f}"
    )

    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        header = "prime,predicted_gap,actual_gap,predicted_target,actual_next,error,hit"
        args.output.write_text(header + "\n" + "\n".join(rows) + "\n")
        print(f"Wrote CSV to {args.output.resolve()}")


if __name__ == "__main__":
    main()
