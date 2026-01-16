#!/usr/bin/env python3
import argparse
import math
import time


def parse_etas(raw):
    return [float(item.strip()) for item in raw.split(",") if item.strip()]


def parse_ranges(raw):
    ranges = []
    for chunk in raw.split(","):
        chunk = chunk.strip()
        if not chunk:
            continue
        if "-" in chunk:
            start_str, end_str = chunk.split("-", 1)
        elif ":" in chunk:
            start_str, end_str = chunk.split(":", 1)
        else:
            raise ValueError(f"Invalid range '{chunk}'. Use start-end.")
        start = int(start_str.strip())
        end = int(end_str.strip())
        if end < start:
            raise ValueError(f"Range end < start: {chunk}")
        ranges.append((start, end))
    return ranges


def sieve_primes(limit):
    sieve = bytearray(b"\x01") * (limit + 1)
    if limit >= 0:
        sieve[:2] = b"\x00\x00"
    for p in range(2, math.isqrt(limit) + 1):
        if sieve[p]:
            start = p * p
            sieve[start : limit + 1 : p] = b"\x00" * ((limit - start) // p + 1)
    return sieve


def build_basis(limit):
    if limit < 2:
        return []
    return list(range(2, limit + 1))


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


def compute_metrics(start, energies, prime_mask):
    prime_energies = []
    comp_energies = []
    peak_hits = 0
    peak_prominence = []

    for idx, energy in enumerate(energies):
        n = start + idx
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


def summarize(values):
    if not values:
        return 0.0, 0.0
    mean = sum(values) / len(values)
    if len(values) < 2:
        return mean, 0.0
    var = sum((v - mean) ** 2 for v in values) / (len(values) - 1)
    return mean, math.sqrt(var)


def parse_args():
    parser = argparse.ArgumentParser(
        description="Sweep Clifford resonance metrics across ranges and eta values."
    )
    parser.add_argument(
        "--ranges",
        type=parse_ranges,
        default=parse_ranges("1000-2000,3000-4000,5000-6000,7000-8000,9000-10000"),
        help="Comma-separated ranges, e.g. 1000-2000,5000-6000.",
    )
    parser.add_argument(
        "--etas",
        type=parse_etas,
        default=parse_etas("3.14159,3.299,3.2"),
        help="Comma-separated eta values to compare.",
    )
    parser.add_argument(
        "--eta-step",
        type=float,
        default=0.0001,
        help="Delta applied to eta for differential coherence.",
    )
    return parser.parse_args()


def main():
    args = parse_args()
    ranges = args.ranges
    etas = args.etas

    max_end = max(end for _, end in ranges)
    prime_mask = sieve_primes(max_end)

    results = {
        eta: {
            "energy": {"delta": [], "cohen_d": [], "peak_prominence": []},
            "diff": {"delta": [], "cohen_d": [], "peak_prominence": []},
        }
        for eta in etas
    }
    wins = {
        "energy": {
            metric: {eta: 0 for eta in etas}
            for metric in ("delta", "cohen_d", "peak_prominence")
        },
        "diff": {
            metric: {eta: 0 for eta in etas}
            for metric in ("delta", "cohen_d", "peak_prominence")
        },
    }

    print(f"Ranges: {ranges}")
    print(f"Etas: {etas}")

    for start, end in ranges:
        basis = build_basis(math.isqrt(end))
        print(f"\nRange {start}-{end} | basis size={len(basis)}")

        per_eta = {}
        for eta in etas:
            t0 = time.perf_counter()
            energies = energy_field(start, end, basis, eta)
            t1 = time.perf_counter()
            metrics = compute_metrics(start, energies, prime_mask)
            energies_tweak = energy_field(start, end, basis, eta + args.eta_step)
            diff_energies = [
                abs((base - tweak) / base) if base != 0.0 else 0.0
                for base, tweak in zip(energies, energies_tweak)
            ]
            diff_metrics = compute_metrics(start, diff_energies, prime_mask)
            t2 = time.perf_counter()
            per_eta[eta] = metrics
            print(
                f"  eta={eta:.5f} delta={metrics['delta']:.6f} "
                f"cohen_d={metrics['cohen_d']:.6f} "
                f"peak_prom={metrics['peak_prominence']:.6f} "
                f"time={t1 - t0:.4f}s"
            )
            print(
                f"    diff delta={diff_metrics['delta']:.6f} "
                f"cohen_d={diff_metrics['cohen_d']:.6f} "
                f"peak_prom={diff_metrics['peak_prominence']:.6f}"
            )
            results[eta]["energy"]["delta"].append(metrics["delta"])
            results[eta]["energy"]["cohen_d"].append(metrics["cohen_d"])
            results[eta]["energy"]["peak_prominence"].append(metrics["peak_prominence"])
            results[eta]["diff"]["delta"].append(diff_metrics["delta"])
            results[eta]["diff"]["cohen_d"].append(diff_metrics["cohen_d"])
            results[eta]["diff"]["peak_prominence"].append(
                diff_metrics["peak_prominence"]
            )

        for metric in wins["energy"]:
            best_eta = max(etas, key=lambda e: per_eta[e][metric])
            wins["energy"][metric][best_eta] += 1
        for metric in wins["diff"]:
            best_eta = max(etas, key=lambda e: results[e]["diff"][metric][-1])
            wins["diff"][metric][best_eta] += 1

    print("\nSummary across ranges:")
    for eta in etas:
        delta_mean, delta_std = summarize(results[eta]["energy"]["delta"])
        d_mean, d_std = summarize(results[eta]["energy"]["cohen_d"])
        prom_mean, prom_std = summarize(results[eta]["energy"]["peak_prominence"])
        diff_delta_mean, diff_delta_std = summarize(results[eta]["diff"]["delta"])
        diff_d_mean, diff_d_std = summarize(results[eta]["diff"]["cohen_d"])
        diff_prom_mean, diff_prom_std = summarize(
            results[eta]["diff"]["peak_prominence"]
        )
        print(
            f"eta={eta:.5f} | "
            f"energy delta={delta_mean:.6f}±{delta_std:.6f} "
            f"cohen_d={d_mean:.6f}±{d_std:.6f} "
            f"peak_prom={prom_mean:.6f}±{prom_std:.6f}"
        )
        print(
            f"          | diff delta={diff_delta_mean:.6f}±{diff_delta_std:.6f} "
            f"cohen_d={diff_d_mean:.6f}±{diff_d_std:.6f} "
            f"peak_prom={diff_prom_mean:.6f}±{diff_prom_std:.6f}"
        )

    print("\nWins by metric (energy):")
    for metric, counts in wins["energy"].items():
        tally = ", ".join(f"{eta:.5f}:{count}" for eta, count in counts.items())
        print(f"  {metric}: {tally}")

    print("\nWins by metric (diff):")
    for metric, counts in wins["diff"].items():
        tally = ", ".join(f"{eta:.5f}:{count}" for eta, count in counts.items())
        print(f"  {metric}: {tally}")


if __name__ == "__main__":
    main()
