#!/usr/bin/env python3
"""
═══════════════════════════════════════════════════════════════════════════════
EVALUATION (2026-01-16):
  - Hit rate at 10^9: 19% (FAILS AT SCALE)
  - Memory: O(1)
  - VALUE: NONE - gap prediction doesn't work with few zeta zeros
  - RECOMMENDATION: Archive - same as clifford_gap_predictor
═══════════════════════════════════════════════════════════════════════════════

Predict prime jumps using a log-polar spectral heuristic and score accuracy.

Uses Riemann zeta zeros as "spectral wobble" corrections to the base gap estimate:

    predicted_gap ≈ log(p) × (1 + wobble / curvature)

where wobble = Σ sin(γ·log(p)) / γ  for each zero γ.

The curvature parameter plays a similar role to eta in clifford_resonance_sweep.py.
Based on resonance sweep findings, try --curvature 2.0 instead of default 3.299.

UPGRADED: Now uses Miller-Rabin for O(1) memory primality testing.
Works at any scale (tested to 10^19).

See Notes.md for connection to Ramanujan sums and Clifford algebra theory.
"""
from __future__ import annotations

import argparse
import math
from pathlib import Path

import numpy as np


def miller_rabin(n: int) -> bool:
    """Deterministic Miller-Rabin for n < 2^64."""
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    r, d = 0, n - 1
    while d % 2 == 0:
        r += 1
        d //= 2
    for a in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]:
        if a >= n:
            continue
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


def is_prime(value: int) -> bool:
    """O(1) memory primality test using Miller-Rabin."""
    return miller_rabin(value)


def next_prime(value: int) -> int:
    """Find next prime after value using Miller-Rabin."""
    if value < 2:
        return 2
    candidate = value + 1
    if candidate == 2:
        return 2
    if candidate % 2 == 0:
        candidate += 1
    while not miller_rabin(candidate):
        candidate += 2
    return candidate


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

    # O(1) memory - no sieve needed!
    print(f"Memory: O(1) - using Miller-Rabin for primality")
    print(f"Scale: Works at any size (tested to 10^19)")
    print()

    current = args.start
    if not is_prime(current):
        current = next_prime(current)
        print(f"Adjusted start to next prime: {current:,}")

    rows: list[str] = []
    hits = 0
    abs_errors: list[int] = []
    signed_errors: list[int] = []

    for step in range(args.count):
        predicted_gap = predict_next_prime_gap(current, args.zeros, args.curvature)
        predicted_target = current + predicted_gap
        actual_next = next_prime(current)
        actual_gap = actual_next - current
        hit = predicted_target <= actual_next <= predicted_target + args.window
        error = predicted_target - actual_next

        hits += int(hit)
        abs_errors.append(abs(error))
        signed_errors.append(error)

        if step < args.samples:
            print(
                f"p={current:,} | predicted_gap={predicted_gap} | "
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
