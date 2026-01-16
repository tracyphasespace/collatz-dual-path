#!/usr/bin/env python3
"""
Memory-Efficient Clifford Resonance - Segmented Sieve Version

═══════════════════════════════════════════════════════════════════════════════
EVALUATION (2026-01-16):
  - Memory: O(√N) - 46KB vs 0.9GB at 10^9 (21000x savings)
  - Computes energy differentials (Cohen's d) between primes/composites
  - VALUE: NONE - this is just a standard segmented sieve
  - The "energy" framing doesn't provide predictive power
  - RECOMMENDATION: Archive - segmented sieve is textbook algorithm
═══════════════════════════════════════════════════════════════════════════════

Uses segmented sieve to test arbitrary ranges with minimal memory:
- Only stores primes up to √N (tiny: ~6000 primes for N=3B)
- Sieves test range in small segments
- Memory: O(√N) instead of O(N)

Example memory comparison for N = 3 billion:
- Original: 3.1 GB (full sieve)
- Segmented: ~3 MB (primes up to √N + segment buffer)

This allows testing at 100B+ on a laptop!
"""
import argparse
import math
import sys
import time

# Small segment size for memory efficiency
SEGMENT_SIZE = 100_000


def sieve_small_primes(limit):
    """Sieve primes up to limit. Used for √N which is small."""
    if limit < 2:
        return []
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, math.isqrt(limit) + 1):
        if sieve[p]:
            sieve[p*p:limit+1:p] = b"\x00" * ((limit - p*p) // p + 1)
    return [i for i, is_p in enumerate(sieve) if is_p]


def segmented_sieve_range(start, end, small_primes):
    """
    Sieve a range [start, end] using precomputed small primes.
    Returns a bytearray where 1 = prime, 0 = composite.

    Memory: O(end - start) only
    """
    size = end - start + 1
    is_prime = bytearray(b"\x01") * size

    # Mark 0 and 1 as not prime if in range
    if start <= 0:
        is_prime[0 - start] = 0
    if start <= 1 <= end:
        is_prime[1 - start] = 0

    # Sieve using small primes
    for p in small_primes:
        # Find first multiple of p >= start
        first = ((start + p - 1) // p) * p
        if first < p * p:
            first = p * p
        if first > end:
            continue

        # Mark all multiples of p in range
        for j in range(first - start, size, p):
            is_prime[j] = 0

    return is_prime


def energy_field_segmented(start, end, prime_basis, eta):
    """
    Compute resonance energy for each n in [start, end].
    Uses precomputed prime basis (not sieved on the fly).
    """
    values = []
    two_eta = 2.0 * eta
    factors = [two_eta / r for r in prime_basis]

    for n in range(start, end + 1):
        total = 0.0
        for r, factor in zip(prime_basis, factors):
            theta = factor * (n % r)
            total += 1.0 - math.cos(theta)
        values.append(total)

    return values


def compute_metrics(start, energies, prime_mask):
    """Compute Cohen's d and other metrics."""
    prime_energies = []
    comp_energies = []

    for idx, energy in enumerate(energies):
        n = start + idx
        if prime_mask[idx]:
            prime_energies.append(energy)
        else:
            comp_energies.append(energy)

    if not prime_energies or not comp_energies:
        return {"cohen_d": 0.0, "n_primes": len(prime_energies)}

    mean_prime = sum(prime_energies) / len(prime_energies)
    mean_comp = sum(comp_energies) / len(comp_energies)
    delta = mean_prime - mean_comp

    def variance(values, mean):
        if len(values) < 2:
            return 0.0
        return sum((v - mean) ** 2 for v in values) / (len(values) - 1)

    var_prime = variance(prime_energies, mean_prime)
    var_comp = variance(comp_energies, mean_comp)
    pooled = math.sqrt(0.5 * (var_prime + var_comp)) if (var_prime + var_comp) > 0 else 1.0
    cohen_d = delta / pooled if pooled > 0 else 0.0

    return {
        "cohen_d": cohen_d,
        "delta": delta,
        "n_primes": len(prime_energies),
        "n_comp": len(comp_energies),
        "mean_prime": mean_prime,
        "mean_comp": mean_comp,
    }


def parse_ranges(raw):
    """Parse comma-separated ranges like '1000-2000,3000-4000'"""
    ranges = []
    for chunk in raw.split(","):
        chunk = chunk.strip()
        if not chunk:
            continue
        if "-" in chunk:
            a, b = chunk.split("-", 1)
        elif ":" in chunk:
            a, b = chunk.split(":", 1)
        else:
            raise ValueError(f"Invalid range: {chunk}")
        ranges.append((int(a.strip()), int(b.strip())))
    return ranges


def main():
    parser = argparse.ArgumentParser(
        description="Memory-efficient Clifford resonance using segmented sieve."
    )
    parser.add_argument(
        "--ranges",
        type=parse_ranges,
        default=parse_ranges("1000000000-1000000200"),
        help="Comma-separated ranges to test",
    )
    parser.add_argument(
        "--eta",
        type=float,
        default=2.0,
        help="Eta parameter (default: 2.0 optimal)",
    )
    parser.add_argument(
        "--max-range",
        type=int,
        default=10000,
        help="Maximum range size per window",
    )
    parser.add_argument(
        "--basis-limit",
        type=int,
        default=0,
        help="Limit basis to first N primes (0 = use all). Recommended: 100-500 for large scales.",
    )
    args = parser.parse_args()

    # Find the maximum value we need to handle
    max_n = max(end for _, end in args.ranges)
    sqrt_max = math.isqrt(max_n) + 1

    print("=" * 70)
    print("MEMORY-EFFICIENT CLIFFORD RESONANCE (Segmented Sieve)")
    print("=" * 70)
    print(f"Max N: {max_n:,}")
    print(f"√N: {sqrt_max:,}")

    # Step 1: Sieve small primes (this is tiny - a few MB at most)
    t0 = time.perf_counter()
    small_primes = sieve_small_primes(sqrt_max)
    t1 = time.perf_counter()

    # The prime basis - optionally truncated for better SNR at large scales
    if args.basis_limit > 0:
        prime_basis = small_primes[:args.basis_limit]
        print(f"Basis TRUNCATED to first {args.basis_limit} primes (up to {prime_basis[-1]})")
    else:
        prime_basis = small_primes

    print(f"Prime basis: {len(prime_basis):,} primes up to {sqrt_max:,}")
    print(f"Memory for basis: ~{len(prime_basis) * 8 / 1024:.1f} KB")
    print(f"Sieve time: {t1-t0:.3f}s")
    print()

    all_results = []

    for start, end in args.ranges:
        range_size = end - start + 1

        if range_size > args.max_range:
            print(f"Skipping {start:,}-{end:,}: exceeds max_range {args.max_range:,}")
            continue

        print(f"Range: {start:,} - {end:,} ({range_size:,} numbers)")
        print("-" * 50)

        # Step 2: Sieve just this range (small memory)
        t2 = time.perf_counter()
        prime_mask = segmented_sieve_range(start, end, small_primes)
        t3 = time.perf_counter()

        # Step 3: Compute resonance energies
        energies = energy_field_segmented(start, end, prime_basis, args.eta)
        t4 = time.perf_counter()

        # Step 4: Compute metrics
        metrics = compute_metrics(start, energies, prime_mask)

        print(f"  Primes in range: {metrics['n_primes']}")
        print(f"  Cohen's d: {metrics['cohen_d']:.4f}")
        print(f"  Delta: {metrics['delta']:.4f}")
        print(f"  Sieve time: {t3-t2:.4f}s, Energy time: {t4-t3:.4f}s")
        print()

        all_results.append({
            "start": start,
            "end": end,
            **metrics
        })

        # Cleanup
        del prime_mask, energies

    # Summary
    if len(all_results) > 1:
        print("=" * 70)
        print("SUMMARY")
        print("=" * 70)
        avg_d = sum(r["cohen_d"] for r in all_results) / len(all_results)
        print(f"Average Cohen's d: {avg_d:.4f}")

    # Memory estimate
    print()
    print("=" * 70)
    print("MEMORY USAGE ESTIMATE")
    print("=" * 70)
    basis_mem = len(prime_basis) * 8  # 8 bytes per int
    range_mem = args.max_range * 2  # 1 byte mask + 8 bytes energy, amortized
    total_mem = basis_mem + range_mem
    print(f"Prime basis: {basis_mem / 1024:.1f} KB")
    print(f"Range buffer: {range_mem / 1024:.1f} KB")
    print(f"Total: {total_mem / 1024:.1f} KB ({total_mem / 1024 / 1024:.2f} MB)")
    print()
    print(f"Compare to full sieve: {max_n / 1024 / 1024 / 1024:.1f} GB")
    print(f"Memory savings: {max_n / total_mem:.0f}x")


if __name__ == "__main__":
    main()
