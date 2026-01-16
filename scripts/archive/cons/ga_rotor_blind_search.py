#!/usr/bin/env python3
"""Blind-search prime candidates from a GA rotor magnitude landscape."""
from __future__ import annotations

import argparse
import math
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np


def prime_sieve(limit: int) -> np.ndarray:
    sieve = np.ones(limit + 1, dtype=bool)
    if limit >= 0:
        sieve[:2] = False
    for value in range(2, math.isqrt(limit) + 1):
        if sieve[value]:
            sieve[value * value : limit + 1 : value] = False
    return sieve


def parse_primes(raw: str) -> list[int]:
    if not raw:
        return []
    return [int(item.strip()) for item in raw.split(",") if item.strip()]


def magnitude_landscape(n_values: np.ndarray, basis_primes: list[int]) -> np.ndarray:
    pos_sq = np.zeros_like(n_values)
    neg_sq = np.zeros_like(n_values)

    for idx, prime in enumerate(basis_primes):
        theta = (2.0 * math.pi * n_values) / prime
        scale = (n_values / prime) ** 2
        if idx < 3:
            pos_sq += (np.cos(theta) ** 2) * scale
        else:
            neg_sq += (np.sin(theta) ** 2) * scale

    return np.sqrt(np.abs(pos_sq - neg_sq))


def local_peaks(values: np.ndarray) -> np.ndarray:
    if values.size < 3:
        return np.array([], dtype=int)
    left = values[:-2]
    mid = values[1:-1]
    right = values[2:]
    return np.where((mid > left) & (mid >= right))[0] + 1


def select_candidates_quantile(
    n_values: np.ndarray,
    magnitudes: np.ndarray,
    count: int,
    quantile: float,
    relax: float,
) -> tuple[np.ndarray, float]:
    peak_indices = local_peaks(magnitudes)
    if peak_indices.size == 0:
        return np.array([], dtype=int), quantile

    peak_mags = magnitudes[peak_indices]
    current_q = quantile
    while current_q >= 0.0:
        threshold = float(np.quantile(peak_mags, current_q))
        candidates = n_values[peak_indices][peak_mags >= threshold]
        if candidates.size >= count:
            return candidates.astype(int), current_q
        current_q -= relax
    return n_values[peak_indices].astype(int), max(current_q, 0.0)


def select_candidates_local(
    n_values: np.ndarray,
    magnitudes: np.ndarray,
    count: int,
    window: int,
) -> np.ndarray:
    peak_indices = local_peaks(magnitudes)
    if peak_indices.size == 0:
        return np.array([], dtype=int)

    peak_values = n_values[peak_indices].astype(int)
    peak_mags = magnitudes[peak_indices]
    start = int(n_values[0])
    end = int(n_values[-1])

    candidates: list[int] = []
    for window_start in range(start, end + 1, window):
        window_end = window_start + window - 1
        in_window = (peak_values >= window_start) & (peak_values <= window_end)
        if not np.any(in_window):
            continue
        window_mags = peak_mags[in_window]
        window_peaks = peak_values[in_window]
        candidates.append(int(window_peaks[np.argmax(window_mags)]))
        if len(candidates) >= count:
            break

    return np.array(candidates, dtype=int)


def basis_primes_for(end: int, basis_primes: list[int], basis_up_to: int) -> list[int]:
    if basis_primes:
        return basis_primes
    limit = basis_up_to if basis_up_to > 0 else math.isqrt(end)
    if limit < 2:
        return []
    sieve = prime_sieve(limit)
    return np.flatnonzero(sieve).tolist()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Blind-search prime candidates using GA rotor magnitude peaks."
    )
    parser.add_argument(
        "--start",
        type=int,
        default=100_000,
        help="Starting integer for the blind search.",
    )
    parser.add_argument(
        "--count",
        type=int,
        default=10,
        help="Number of primes to predict and score.",
    )
    parser.add_argument(
        "--span",
        type=int,
        default=5_000,
        help="Initial span to search beyond the start.",
    )
    parser.add_argument(
        "--step",
        type=int,
        default=5_000,
        help="Span growth step if predictions are insufficient.",
    )
    parser.add_argument(
        "--max-span",
        type=int,
        default=50_000,
        help="Maximum span allowed for the blind search.",
    )
    parser.add_argument(
        "--quantile",
        type=float,
        default=0.75,
        help="Quantile threshold applied to peak magnitudes.",
    )
    parser.add_argument(
        "--relax",
        type=float,
        default=0.05,
        help="Quantile decrement if not enough peaks are found.",
    )
    parser.add_argument(
        "--peak-mode",
        choices=("local", "quantile"),
        default="local",
        help="Peak selection strategy.",
    )
    parser.add_argument(
        "--peak-window",
        type=int,
        default=100,
        help="Window size for local peak selection.",
    )
    parser.add_argument(
        "--window",
        type=int,
        default=10,
        help="Hit window (absolute error <= window counts as a hit).",
    )
    parser.add_argument(
        "--basis-primes",
        type=parse_primes,
        default=parse_primes(""),
        help="Comma-separated primes used as rotor frequencies.",
    )
    parser.add_argument(
        "--basis-up-to",
        type=int,
        default=0,
        help="Upper bound for auto basis primes (defaults to sqrt(end)).",
    )
    parser.add_argument(
        "--normalize-log",
        dest="normalize_log",
        action="store_true",
        default=True,
        help="Normalize magnitudes by log(n).",
    )
    parser.add_argument(
        "--no-normalize-log",
        dest="normalize_log",
        action="store_false",
        help="Disable log normalization.",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=None,
        help="Optional CSV output path for detailed results.",
    )
    parser.add_argument(
        "--plot",
        type=Path,
        default=Path("tuning/ga_rotor_blind_search.png"),
        help="Optional PNG output path for visualization.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.count <= 0:
        raise SystemExit("--count must be > 0.")
    if args.span <= 0 or args.step <= 0:
        raise SystemExit("--span and --step must be > 0.")
    if args.max_span < args.span:
        raise SystemExit("--max-span must be >= --span.")
    if args.peak_window < 1:
        raise SystemExit("--peak-window must be >= 1.")

    span = args.span
    candidates = np.array([], dtype=int)
    actual_primes = np.array([], dtype=int)
    used_quantile = args.quantile
    basis_limit = 0

    while span <= args.max_span:
        end = args.start + span
        n_values = np.arange(args.start, end + 1, dtype=float)
        basis_primes = basis_primes_for(end, args.basis_primes, args.basis_up_to)
        if not basis_primes:
            raise SystemExit("No basis primes available for the rotor model.")
        basis_limit = max(basis_primes)
        magnitudes = magnitude_landscape(n_values, basis_primes)
        if args.normalize_log:
            magnitudes = magnitudes / np.log(n_values)
        if args.peak_mode == "local":
            candidates = select_candidates_local(
                n_values, magnitudes, args.count, args.peak_window
            )
        else:
            candidates, used_quantile = select_candidates_quantile(
                n_values, magnitudes, args.count, args.quantile, args.relax
            )

        prime_mask = prime_sieve(end)
        actual_primes = np.flatnonzero(prime_mask[args.start : end + 1]) + args.start

        if candidates.size >= args.count and actual_primes.size >= args.count:
            break
        span += args.step

    if candidates.size < args.count or actual_primes.size < args.count:
        raise SystemExit(
            "Unable to gather enough candidates/primes within max span. "
            "Increase --max-span or relax thresholds."
        )

    predicted = candidates[: args.count]
    actual = actual_primes[: args.count]
    errors = predicted - actual
    hits = np.abs(errors) <= args.window

    print("Blind search results (predicted vs actual):")
    for idx, (p_pred, p_actual, error, hit) in enumerate(
        zip(predicted, actual, errors, hits), start=1
    ):
        print(
            f"{idx:02d}. predicted={p_pred} | actual={p_actual} | "
            f"error={error:+d} | hit={bool(hit)}"
        )

    hit_rate = hits.mean()
    mae = np.mean(np.abs(errors))
    bias = np.mean(errors)
    print(
        "Summary: "
        f"count={args.count}, hit_rate={hit_rate:.3f}, "
        f"mae={mae:.3f}, bias={bias:.3f}, "
        f"span_used={span}, basis_limit={basis_limit}, "
        f"peak_mode={args.peak_mode}, quantile_used={used_quantile:.2f}, "
        f"log_normalized={args.normalize_log}"
    )

    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        header = "index,predicted,actual,error,hit"
        rows = [
            f"{idx},{predicted[idx]},{actual[idx]},{errors[idx]},{int(hits[idx])}"
            for idx in range(args.count)
        ]
        args.output.write_text(header + "\n" + "\n".join(rows) + "\n")
        print(f"Wrote CSV to {args.output.resolve()}")

    if args.plot:
        plt.style.use("dark_background")
        fig, ax = plt.subplots(figsize=(14, 6))
        ax.plot(n_values, magnitudes, color="cyan", alpha=0.6, linewidth=0.8)
        ax.scatter(
            predicted,
            magnitudes[predicted - args.start],
            color="red",
            s=35,
            marker="^",
            label="Predicted peaks",
        )
        ax.scatter(
            actual,
            magnitudes[actual - args.start],
            color="yellow",
            s=25,
            label="Actual primes",
        )
        ax.set_title(
            "GA Rotor Blind Search: Predicted Peaks vs Actual Primes",
            color="white",
        )
        ax.set_xlabel("Number line", color="white")
        ylabel = "Log-normalized magnitude" if args.normalize_log else "Hyperbolic magnitude"
        ax.set_ylabel(ylabel, color="white")
        ax.legend()
        args.plot.parent.mkdir(parents=True, exist_ok=True)
        fig.savefig(args.plot, dpi=200, bbox_inches="tight")
        plt.close(fig)
        print(f"Wrote plot to {args.plot.resolve()}")


if __name__ == "__main__":
    main()
