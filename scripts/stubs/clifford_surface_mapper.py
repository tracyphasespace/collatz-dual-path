#!/usr/bin/env python3
import argparse
import math
import random
import time
from pathlib import Path


def build_basis(limit, mode, cutoff, sample_size, seed):
    if limit < 2:
        return [], [], 1.0

    cutoff = min(cutoff, limit)
    base = list(range(2, cutoff + 1))
    if mode == "full" or cutoff >= limit or sample_size <= 0:
        return base, [], 1.0

    population_start = cutoff + 1
    population_size = limit - cutoff
    sample_size = min(sample_size, population_size)
    rng = random.Random(seed)
    sample = rng.sample(range(population_start, limit + 1), sample_size)
    scale = population_size / sample_size
    return base, sample, scale


def map_surface(start, end, base, sample, scale):
    two_pi = 2 * math.pi
    base_factors = [two_pi / r for r in base]
    sample_factors = [two_pi / r for r in sample]

    data = []
    for n in range(start, end + 1):
        total = 0.0
        for r, factor in zip(base, base_factors):
            total += 1.0 - math.cos(factor * (n % r))
        for r, factor in zip(sample, sample_factors):
            total += (1.0 - math.cos(factor * (n % r))) * scale
        data.append((n, total))
    return data


def find_peaks(data, threshold_ratio):
    if len(data) < 3:
        return []
    max_energy = max(energy for _, energy in data)
    threshold = max_energy * threshold_ratio
    peaks = []
    for idx in range(1, len(data) - 1):
        prev_energy = data[idx - 1][1]
        curr_energy = data[idx][1]
        next_energy = data[idx + 1][1]
        if curr_energy > prev_energy and curr_energy > next_energy and curr_energy >= threshold:
            peaks.append(data[idx])
    return peaks


def write_csv(path, data):
    path.write_text("n,energy\n" + "\n".join(f"{n},{energy:.8f}" for n, energy in data) + "\n")


def parse_args():
    parser = argparse.ArgumentParser(
        description="Map the Clifford surface using a blind integer rotor basis."
    )
    parser.add_argument("--start", type=int, default=1000, help="Start of window.")
    parser.add_argument("--end", type=int, default=1100, help="End of window (inclusive).")
    parser.add_argument(
        "--mode",
        choices=("full", "sampled"),
        default="full",
        help="Full basis (2..sqrtN) or sampled basis for scale.",
    )
    parser.add_argument(
        "--cutoff",
        type=int,
        default=10000,
        help="Always include rotors up to this value.",
    )
    parser.add_argument(
        "--sample-size",
        type=int,
        default=20000,
        help="Number of sampled rotors above cutoff in sampled mode.",
    )
    parser.add_argument("--seed", type=int, default=0, help="RNG seed for sampling.")
    parser.add_argument(
        "--threshold",
        type=float,
        default=0.95,
        help="Peak threshold as ratio of max energy.",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=None,
        help="Optional CSV output path.",
    )
    return parser.parse_args()


def main():
    args = parse_args()
    if args.end < args.start:
        raise SystemExit("--end must be >= --start.")

    limit = math.isqrt(args.end) + 1
    base, sample, scale = build_basis(
        limit, args.mode, args.cutoff, args.sample_size, args.seed
    )
    print(
        f"Basis: base={len(base)}, sample={len(sample)}, "
        f"scale={scale:.3f}, limit={limit}"
    )

    t0 = time.perf_counter()
    data = map_surface(args.start, args.end, base, sample, scale)
    t1 = time.perf_counter()
    peaks = find_peaks(data, args.threshold)
    t2 = time.perf_counter()

    print(f"Mapped {len(data)} points in {t1 - t0:.4f}s")
    print(f"Peaks found: {len(peaks)} (threshold={args.threshold:.2f})")

    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        write_csv(args.output, data)
        print(f"Wrote CSV to {args.output.resolve()}")

    if peaks:
        print("Sample peaks:")
        for n, energy in peaks[: min(10, len(peaks))]:
            print(f"  {n} -> {energy:.6f}")

    print(f"Timing: map={t1 - t0:.4f}s, peak_scan={t2 - t1:.4f}s")


if __name__ == "__main__":
    main()
