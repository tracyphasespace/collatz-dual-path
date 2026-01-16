#!/usr/bin/env python3
"""
═══════════════════════════════════════════════════════════════════════════════
EVALUATION (2026-01-16):
  - Memory: O(N) - requires full range in memory
  - VALUE: PEDAGOGICAL - demonstrates energy separation concept
  - Not scalable beyond ~10^7
  - RECOMMENDATION: Archive - visualization only
═══════════════════════════════════════════════════════════════════════════════

Clifford Resonance Sweep - Prime/Composite Separation via Proximity Detection

THEORY:
    This implements a "smoothed proximity detector" for primality, not a sieve.

    For each integer n, we compute an energy:

        E(n) = Σ_r [1 - cos(2η · (n mod r) / r)]

    Key insight: this measures "how close to divisible" rather than "is divisible".

    - When n mod r = 0 (divisible): cos(0) = 1, energy contribution = 0
    - When n mod r = r/2 (maximally far): cos(2η·0.5) contributes most
    - When n mod r = 1 (just missed): cos(2η/r) ≈ 1 for large r, energy ≈ 0

    Primes have no small divisors, so they accumulate energy from every rotor.
    Composites have divisors that contribute zero energy.

    HOWEVER: Primes of form (highly_composite + 1) are "fooled" because they
    satisfy n ≡ 1 (mod many small r), giving near-zero contribution per rotor.
    Example: 1009 = 2⁴×3²×7 + 1 has LOW energy despite being prime.

OPTIMAL ETA:
    Empirical sweeps (2026-01-15) found:

    | eta range | Cohen's d | Notes                    |
    |-----------|-----------|--------------------------|
    | 0.01-1.0  | ~0.477    | Flat plateau             |
    | 1.0-2.0   | 0.48→0.50 | Gradual rise             |
    | 2.0       | 0.5045    | PEAK (optimal)           |
    | 2.0-3.0   | 0.50→0.29 | Sharp cliff              |
    | π, 3.299  | ~0.25     | Poor (originally guessed)|

    At eta=2.0, the phase argument spans 4 radians over one period.
    This appears to minimize sensitivity to the "just missed divisibility" edge cases.

CONNECTION TO CLIFFORD ALGEBRA:
    In the Riemann project's Cl(N,N) framework, each prime p corresponds to
    an orthogonal generator γ_p. The "resonance" here is analogous to the
    interference pattern when projecting onto these orthogonal subspaces.
    The energy function acts like a soft projection detecting prime structure.

    See: Lean/CLAUDE.md, Lean/GA/PrimeClifford.lean

RELATIONSHIP TO RAMANUJAN SUMS:
    The classical Ramanujan sum is: cq(n) = Σ e^(2πi·a·n/q) where gcd(a,q)=1

    Our formula is related but differs in key ways:
    - We use ALL integers as rotors, not just coprime residues
    - We use η=2.0 (empirical) instead of 2π (theoretical)
    - We compute real energy 1-cos(θ) instead of complex e^(iθ)
    - We measure "proximity to divisibility" not exact character sums

    Ramanujan sums are used in Vinogradov's theorem and signal processing
    of arithmetic sequences. This implementation is a novel experimental
    variant optimized for statistical prime/composite separation.

    References:
    - Ramanujan, S. (1918). "On certain trigonometrical sums..."
    - https://en.wikipedia.org/wiki/Ramanujan's_sum
    - scripts/experiments/Notes.md for full comparison
"""
import argparse
import math
import sys
import time

# Memory safety defaults
DEFAULT_MAX_SIEVE = 50_000_000  # 50MB bytearray max
DEFAULT_MAX_RANGE = 100_000     # 100K elements per window


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


def sieve_primes(limit, max_sieve=DEFAULT_MAX_SIEVE):
    if limit > max_sieve:
        print(f"ERROR: Sieve limit {limit:,} exceeds max {max_sieve:,}. Use --max-sieve to increase.", file=sys.stderr)
        sys.exit(1)
    sieve = bytearray(b"\x01") * (limit + 1)
    if limit >= 0:
        sieve[:2] = b"\x00\x00"
    for p in range(2, math.isqrt(limit) + 1):
        if sieve[p]:
            start = p * p
            sieve[start : limit + 1 : p] = b"\x00" * ((limit - start) // p + 1)
    return sieve


def build_basis(limit, mode="blind"):
    """Build the rotor basis up to limit.

    Modes:
    - "blind": All integers 2..limit (original, degrades at large N)
    - "prime": Only primes 2..limit (recommended for N > 100K)

    The prime basis removes redundant rotors (4 is redundant with 2, etc.)
    and dramatically improves performance at large scales.
    At 100M: blind gives Cohen's d ≈ 0, prime gives Cohen's d ≈ 0.20
    """
    if limit < 2:
        return []
    if mode == "prime":
        # Sieve for primes
        sieve = bytearray(b"\x01") * (limit + 1)
        sieve[:2] = b"\x00\x00"
        for p in range(2, int(limit**0.5) + 1):
            if sieve[p]:
                sieve[p*p:limit+1:p] = b"\x00" * ((limit - p*p) // p + 1)
        return [i for i, is_p in enumerate(sieve) if is_p]
    else:  # blind
        return list(range(2, limit + 1))


def energy_field(start, end, basis, eta):
    """Compute resonance energy for each n in [start, end].

    Formula: E(n) = Σ_r [1 - cos(2η · (n mod r) / r)]

    The term (n mod r) / r normalizes the remainder to [0, 1).
    Multiplying by 2η scales the phase:
        - eta=2.0 → phase spans [0, 4) radians (optimal)
        - eta=π   → phase spans [0, 2π) radians (one full cycle, poor)

    Why 1 - cos(θ)?
        - Ranges from 0 (θ=0, divisible) to 2 (θ=π, maximally distant)
        - Smooth gradient rewards "far from divisible"
        - Primes accumulate many small positive contributions
        - Composites have zeros that drag down their total
    """
    values = []
    two_eta = 2.0 * eta
    factors = [two_eta / r for r in basis]  # Precompute 2η/r for each rotor
    for n in range(start, end + 1):
        total = 0.0
        for r, factor in zip(basis, factors):
            # theta = 2η · (n mod r) / r
            theta = factor * (n % r)
            # 1 - cos(theta): zero when divisible, positive otherwise
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
        default=parse_etas("2.0,4.5,3.14159"),
        help="Comma-separated eta values to compare. 2.0 optimal at small N, 4.5 at large N.",
    )
    parser.add_argument(
        "--eta-step",
        type=float,
        default=0.0001,
        help="Delta applied to eta for differential coherence.",
    )
    parser.add_argument(
        "--max-sieve",
        type=int,
        default=DEFAULT_MAX_SIEVE,
        help=f"Maximum sieve size in bytes (default: {DEFAULT_MAX_SIEVE:,}).",
    )
    parser.add_argument(
        "--max-range",
        type=int,
        default=DEFAULT_MAX_RANGE,
        help=f"Maximum range size per window (default: {DEFAULT_MAX_RANGE:,}).",
    )
    parser.add_argument(
        "--basis-mode",
        choices=["blind", "prime"],
        default="blind",
        help="Rotor basis: 'blind' (all integers) or 'prime' (primes only, recommended for N>100K).",
    )
    return parser.parse_args()


def main():
    args = parse_args()
    ranges = args.ranges
    etas = args.etas

    # Validate range sizes
    for start, end in ranges:
        if end - start > args.max_range:
            print(f"ERROR: Range {start}-{end} exceeds max {args.max_range:,}. Use --max-range to increase.", file=sys.stderr)
            sys.exit(1)

    max_end = max(end for _, end in ranges)
    prime_mask = sieve_primes(max_end, max_sieve=args.max_sieve)

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
        basis = build_basis(math.isqrt(end), mode=args.basis_mode)
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
