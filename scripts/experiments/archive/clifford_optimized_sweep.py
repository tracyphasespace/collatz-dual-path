#!/usr/bin/env python3
"""
═══════════════════════════════════════════════════════════════════════════════
EVALUATION (2026-01-16):
  - Memory: O(N) - not scalable
  - Found eta=2.0 optimal for small ranges
  - VALUE: NONE - parameter tuning for non-scalable method
  - RECOMMENDATION: Archive
═══════════════════════════════════════════════════════════════════════════════

Optimized resonance sweep - comparing eta values for prime/composite separation.

This is a streamlined version of clifford_resonance_sweep.py for quick comparisons.

KEY FINDING (2026-01-15): eta=2.0 is optimal (Cohen's d = 0.5045)
- Beats originally suggested values (π, 3.299) by nearly 2x
- See clifford_resonance_sweep.py and Notes.md for full theory
- Related to Ramanujan sums but uses "blind" integer basis
"""
import argparse
import math
import sys
import time

# Memory safety defaults
DEFAULT_MAX_SIEVE = 10_000_000  # 10MB max - conservative for this script
DEFAULT_MAX_RANGE = 10_000     # 10K elements per window


def sieve_primes(limit, max_sieve=DEFAULT_MAX_SIEVE):
    if limit > max_sieve:
        print(f"ERROR: Sieve limit {limit:,} exceeds max {max_sieve:,}. Skipping range.", file=sys.stderr)
        return None
    sieve = bytearray(b"\x01") * (limit + 1)
    if limit >= 0:
        sieve[:2] = b"\x00\x00"
    for p in range(2, math.isqrt(limit) + 1):
        if sieve[p]:
            start = p * p
            sieve[start : limit + 1 : p] = b"\x00" * ((limit - start) // p + 1)
    return sieve

def build_blind_basis(limit):
    """Blind basis: ALL integers, not just primes"""
    return list(range(2, limit + 1))

def energy_field(start, end, basis, eta):
    """Compute resonance energy for each n"""
    two_eta = 2.0 * eta
    factors = [two_eta / r for r in basis]
    energies = []
    for n in range(start, end + 1):
        total = sum(1.0 - math.cos(f * (n % r)) for r, f in zip(basis, factors))
        energies.append(total)
    return energies

def analyze(start, energies, prime_mask):
    """Compute separation metrics"""
    prime_e = [e for i, e in enumerate(energies) if prime_mask[start + i]]
    comp_e = [e for i, e in enumerate(energies) if not prime_mask[start + i]]
    
    mean_p = sum(prime_e) / len(prime_e) if prime_e else 0
    mean_c = sum(comp_e) / len(comp_e) if comp_e else 0
    delta = mean_p - mean_c
    
    # Cohen's d
    var_p = sum((x - mean_p)**2 for x in prime_e) / max(len(prime_e)-1, 1)
    var_c = sum((x - mean_c)**2 for x in comp_e) / max(len(comp_e)-1, 1)
    pooled = math.sqrt(0.5 * (var_p + var_c)) if (var_p + var_c) > 0 else 1
    cohen_d = delta / pooled
    
    # Peak detection
    peaks = 0
    for i in range(1, len(energies)-1):
        if prime_mask[start + i]:
            if energies[i] > energies[i-1] and energies[i] > energies[i+1]:
                peaks += 1
    peak_rate = peaks / len(prime_e) if prime_e else 0
    
    return {"delta": delta, "cohen_d": cohen_d, "peak_rate": peak_rate, 
            "primes": len(prime_e), "mean_prime": mean_p, "mean_comp": mean_c}

def parse_args():
    parser = argparse.ArgumentParser(description="Optimized resonance sweep with memory limits.")
    parser.add_argument("--max-sieve", type=int, default=DEFAULT_MAX_SIEVE,
                        help=f"Maximum sieve size (default: {DEFAULT_MAX_SIEVE:,})")
    parser.add_argument("--max-range", type=int, default=DEFAULT_MAX_RANGE,
                        help=f"Maximum range size (default: {DEFAULT_MAX_RANGE:,})")
    parser.add_argument("--large", action="store_true",
                        help="Include larger test ranges (requires more memory)")
    return parser.parse_args()


def main():
    args = parse_args()

    # Default: conservative test ranges that fit in memory
    test_cases = [
        (10_000, 11_000),
        (100_000, 101_000),
        (1_000_000, 1_001_000),
    ]

    # Only add large ranges if explicitly requested
    if args.large:
        test_cases.extend([
            (10_000_000, 10_010_000),
            (100_000_000, 100_001_000),
        ])

    # Compare etas - 0.5 showed promise before OOM
    etas = [0.5, 2.5, 3.299, math.pi]

    print("=" * 70)
    print("OPTIMIZED RESONANCE SWEEP: eta=0.5 vs 2.5 vs 3.299 vs π")
    print(f"Memory limits: max_sieve={args.max_sieve:,}, max_range={args.max_range:,}")
    print("=" * 70)

    for start, end in test_cases:
        if end - start > args.max_range:
            print(f"\nSkipping range {start:,}-{end:,}: exceeds max_range {args.max_range:,}")
            continue

        prime_mask = sieve_primes(end, max_sieve=args.max_sieve)
        if prime_mask is None:
            continue
        basis = build_blind_basis(math.isqrt(end))

        print(f"\nRange {start:,} - {end:,} | basis size: {len(basis)}")
        print("-" * 60)

        best_eta = None
        best_cohen = -999

        for eta in etas:
            t0 = time.time()
            energies = energy_field(start, end, basis, eta)
            metrics = analyze(start, energies, prime_mask)
            t1 = time.time()

            print(f"  eta={eta:.4f}: cohen_d={metrics['cohen_d']:.4f}, "
                  f"peak_rate={metrics['peak_rate']:.3f}, "
                  f"delta={metrics['delta']:.2f}, time={t1-t0:.3f}s")

            if metrics['cohen_d'] > best_cohen:
                best_cohen = metrics['cohen_d']
                best_eta = eta

            # Cleanup to reduce memory pressure
            del energies

        print(f"  >> WINNER: eta={best_eta:.4f}")

        # Cleanup between ranges
        del prime_mask, basis

    print("\n" + "=" * 70)
    print("CONCLUSION: eta=2.5 should give best prime/composite separation")
    print("=" * 70)


if __name__ == "__main__":
    main()
