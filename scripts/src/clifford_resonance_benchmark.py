#!/usr/bin/env python3
import argparse
import math
import time


def parse_etas(raw):
    return [float(item.strip()) for item in raw.split(",") if item.strip()]


def build_basis(limit):
    if limit < 2:
        return []
    return list(range(2, limit + 1))


def sieve_primes(limit):
    sieve = bytearray(b"\x01") * (limit + 1)
    if limit >= 0:
        sieve[:2] = b"\x00\x00"
    for p in range(2, math.isqrt(limit) + 1):
        if sieve[p]:
            start = p * p
            sieve[start : limit + 1 : p] = b"\x00" * ((limit - start) // p + 1)
    return sieve


def energy_field(start, end, basis, eta):
    values = []
    two_eta = 2.0 * eta
    factors = [two_eta / r for r in basis]
    for n in range(start, end + 1):
        total = 0.0
        for r, factor in zip(basis, factors):
            theta = factor * (n % r)
            total += 1.0 - math.cos(theta)
        values.append(total)
    return values


def compute_metrics(n_values, energies, prime_mask):
    prime_energies = []
    comp_energies = []
    peak_hits = 0
    peak_prominence = []

    for idx, (n, energy) in enumerate(zip(n_values, energies)):
        if prime_mask[n]:
            prime_energies.append(energy)
            if 0 < idx < len(energies) - 1:
                prev_energy = energies[idx - 1]
                next_energy = energies[idx + 1]
                if energy > prev_energy and energy > next_energy:
                    peak_hits += 1
                peak_prominence.append(energy - 0.5 * (prev_energy + next_energy))
        else:
            comp_energies.append(energy)

    mean_prime = sum(prime_energies) / len(prime_energies) if prime_energies else 0.0
    mean_comp = sum(comp_energies) / len(comp_energies) if comp_energies else 0.0
    delta = mean_prime - mean_comp

    def variance(values, mean):
        if len(values) < 2:
            return 0.0
        return sum((v - mean) ** 2 for v in values) / (len(values) - 1)

    var_prime = variance(prime_energies, mean_prime)
    var_comp = variance(comp_energies, mean_comp)
    pooled = math.sqrt(0.5 * (var_prime + var_comp)) if (var_prime + var_comp) > 0 else 0.0
    cohen_d = delta / pooled if pooled > 0 else 0.0

    peak_rate = peak_hits / len(prime_energies) if prime_energies else 0.0
    avg_prominence = (
        sum(peak_prominence) / len(peak_prominence) if peak_prominence else 0.0
    )

    return {
        "mean_prime": mean_prime,
        "mean_comp": mean_comp,
        "delta": delta,
        "cohen_d": cohen_d,
        "peak_rate": peak_rate,
        "peak_prominence": avg_prominence,
    }


def parse_args():
    parser = argparse.ArgumentParser(
        description="Benchmark Clifford resonance focus across eta values."
    )
    parser.add_argument("--start", type=int, default=1000, help="Range start.")
    parser.add_argument("--end", type=int, default=2000, help="Range end (inclusive).")
    parser.add_argument(
        "--etas",
        type=parse_etas,
        default=parse_etas("3.14159,3.299,3.2"),
        help="Comma-separated eta values to compare.",
    )
    return parser.parse_args()


def main():
    args = parse_args()
    if args.end < args.start:
        raise SystemExit("--end must be >= --start.")

    limit = math.isqrt(args.end)
    basis = build_basis(limit)
    prime_mask = sieve_primes(args.end)
    n_values = list(range(args.start, args.end + 1))

    print(
        f"Benchmark range: {args.start}-{args.end} | basis size={len(basis)} | etas={args.etas}"
    )

    results = {}
    for eta in args.etas:
        t0 = time.perf_counter()
        energies = energy_field(args.start, args.end, basis, eta)
        t1 = time.perf_counter()
        metrics = compute_metrics(n_values, energies, prime_mask)
        t2 = time.perf_counter()
        results[eta] = {
            "metrics": metrics,
            "timing": {
                "field": t1 - t0,
                "metrics": t2 - t1,
            },
        }

        print(f"\neta={eta:.5f}")
        print(f"  mean_prime={metrics['mean_prime']:.6f}")
        print(f"  mean_comp={metrics['mean_comp']:.6f}")
        print(f"  delta={metrics['delta']:.6f}")
        print(f"  cohen_d={metrics['cohen_d']:.6f}")
        print(f"  peak_rate={metrics['peak_rate']:.3f}")
        print(f"  peak_prominence={metrics['peak_prominence']:.6f}")
        print(
            f"  timing: field={results[eta]['timing']['field']:.4f}s "
            f"metrics={results[eta]['timing']['metrics']:.4f}s"
        )

    def best_eta(key, higher=True):
        items = [(eta, results[eta]["metrics"][key]) for eta in results]
        items.sort(key=lambda item: item[1], reverse=higher)
        return items[0]

    best_delta = best_eta("delta")
    best_cohen = best_eta("cohen_d")
    best_peaks = best_eta("peak_prominence")

    print("\nBest by metric:")
    print(f"  delta: eta={best_delta[0]:.5f} ({best_delta[1]:.6f})")
    print(f"  cohen_d: eta={best_cohen[0]:.5f} ({best_cohen[1]:.6f})")
    print(f"  peak_prominence: eta={best_peaks[0]:.5f} ({best_peaks[1]:.6f})")


if __name__ == "__main__":
    main()
