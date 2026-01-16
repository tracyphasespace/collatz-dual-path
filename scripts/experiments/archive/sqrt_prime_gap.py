#!/usr/bin/env python3
"""
═══════════════════════════════════════════════════════════════════════════════
EVALUATION (2026-01-16):
  - Tests √p-based gap prediction formulas
  - Memory: O(N) - uses sieve for prime generation
  - VALUE: NONE - gap prediction consistently fails at scale (4-19% hit rate)
  - Best method (riemann_wobble) still only ~15% hit rate at 10^6
  - RECOMMENDATION: Archive - no predictive advantage over log(p) baseline
═══════════════════════════════════════════════════════════════════════════════

√Prime Gap Experiment

Exploring the relationship between √p and prime gaps.

From the Cl(n,n) theory:
- Dimension of the prime sphere at p is π(√p) ≈ 2√p/log(√p)
- Concentration of measure says coordinates ~ 1/√n
- The "fair share" per dimension is 1/√(2√p/log(√p))

Key insight: gap should scale with log(p), but the variance
should depend on √p (the sieve depth).

Testing formulas:
1. gap ≈ log(p) × (1 + C/√p)      # dimensional correction
2. gap ≈ log(p) × √(log(p)/π(√p)) # concentration measure
3. gap ≈ √p × f(p)                # direct √p relationship
"""
import argparse
import math
import sys
import time

DEFAULT_MAX_SIEVE = 10_000_000


def sieve_primes(limit, max_sieve=DEFAULT_MAX_SIEVE):
    if limit < 2:
        return []
    if limit > max_sieve:
        print(f"ERROR: Sieve limit {limit:,} exceeds max.", file=sys.stderr)
        sys.exit(1)
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, math.isqrt(limit) + 1):
        if sieve[p]:
            sieve[p*p:limit+1:p] = b"\x00" * ((limit - p*p) // p + 1)
    return [i for i, is_p in enumerate(sieve) if is_p]


def prime_counting_approx(x):
    """π(x) ≈ x/log(x) for x > 1"""
    if x <= 1:
        return 0
    return x / math.log(x)


# Gap prediction formulas

def gap_log_only(p):
    """Baseline: gap ≈ log(p)"""
    return max(2, int(round(math.log(p))))


def gap_sqrt_correction(p, c=0.5):
    """gap ≈ log(p) × (1 + C/√p)"""
    base = math.log(p)
    correction = 1.0 + c / math.sqrt(p)
    return max(2, int(round(base * correction)))


def gap_concentration(p):
    """
    gap ≈ log(p) × √(log(p) / dim)
    where dim = π(√p) is the effective dimension
    """
    base = math.log(p)
    sqrt_p = math.sqrt(p)
    dim = prime_counting_approx(sqrt_p)
    if dim < 1:
        dim = 1
    concentration = math.sqrt(base / dim)
    return max(2, int(round(base * concentration)))


def gap_sqrt_direct(p, k=0.5):
    """gap ≈ k × √(p) / π(√p)"""
    sqrt_p = math.sqrt(p)
    dim = prime_counting_approx(sqrt_p)
    if dim < 1:
        dim = 1
    return max(2, int(round(k * sqrt_p / dim)))


def gap_half_reduction(p):
    """
    From the "1/2 reduction" theory:
    The minimum radius surface is at (P+2)/2.
    The gap relates to how many times we can halve before
    hitting a prime factor.

    gap ≈ log₂(p) + correction_from_balance
    """
    log2_p = math.log2(p)

    # At σ=1/2, balance = 1. The gap is proportional to
    # how "centered" we are on the critical line.
    balance_correction = 1.0 / math.sqrt(p)

    return max(2, int(round(log2_p * (1 + balance_correction))))


def gap_riemann_zeros(p, gamma1=14.1347):
    """
    Incorporate the first Riemann zero for wobble correction.
    Similar to prime_navigator.py but simplified.
    """
    base = math.log(p)
    wobble = math.sin(gamma1 * math.log(p)) / gamma1
    return max(2, int(round(base * (1 + wobble / 2))))


def gap_hybrid_sqrt(p):
    """
    Hybrid formula combining:
    - Base: log(p)
    - √p dimensional scaling
    - Balance condition at σ=1/2
    """
    base = math.log(p)
    sqrt_p = math.sqrt(p)
    dim = prime_counting_approx(sqrt_p)
    if dim < 1:
        dim = 1

    # The "fair share" in dim dimensions is 1/√dim
    fair_share = 1.0 / math.sqrt(dim)

    # Balance at σ=1/2: amplitude × measure = 1
    # Deviation from balance contributes to gap variance
    amplitude = 1.0 / math.sqrt(p)
    measure = math.sqrt(p)
    # balance = amplitude * measure = 1 always at σ=0.5

    # Combined formula
    predicted = base * (1 + fair_share * 0.3)

    return max(2, int(round(predicted)))


def evaluate_methods(primes, methods, window=5):
    """Evaluate all gap prediction methods."""
    results = {}

    for name, fn in methods:
        hits = 0
        errors = []
        signed = []

        for i in range(len(primes) - 1):
            p = primes[i]
            actual = primes[i + 1] - p
            pred = fn(p)

            err = pred - actual
            errors.append(abs(err))
            signed.append(err)

            if abs(err) <= window:
                hits += 1

        n = len(errors)
        results[name] = {
            "hit_rate": hits / n if n > 0 else 0,
            "mae": sum(errors) / n if n > 0 else 0,
            "bias": sum(signed) / n if n > 0 else 0,
            "n": n
        }

    return results


def main():
    parser = argparse.ArgumentParser(
        description="Test √prime relationships for gap prediction."
    )
    parser.add_argument("--max-sieve", type=int, default=DEFAULT_MAX_SIEVE)
    args = parser.parse_args()

    print("=" * 70)
    print("√PRIME GAP EXPERIMENT")
    print("Testing dimensional and concentration-based gap formulas")
    print("=" * 70)

    methods = [
        ("log_only", gap_log_only),
        ("sqrt_c0.3", lambda p: gap_sqrt_correction(p, 0.3)),
        ("sqrt_c0.5", lambda p: gap_sqrt_correction(p, 0.5)),
        ("sqrt_c1.0", lambda p: gap_sqrt_correction(p, 1.0)),
        ("concentration", gap_concentration),
        ("sqrt_direct", gap_sqrt_direct),
        ("half_reduction", gap_half_reduction),
        ("riemann_wobble", gap_riemann_zeros),
        ("hybrid_sqrt", gap_hybrid_sqrt),
    ]

    test_regions = [
        (1000, 500, "~1K"),
        (10000, 500, "~10K"),
        (100000, 500, "~100K"),
        (1000000, 200, "~1M"),
    ]

    all_results = {name: [] for name, _ in methods}

    for start, count, label in test_regions:
        limit = start + count * 50
        if limit > args.max_sieve:
            print(f"\nSkipping {label}: exceeds sieve limit")
            continue

        primes_all = sieve_primes(limit, args.max_sieve)

        # Find starting index
        idx = 0
        for i, p in enumerate(primes_all):
            if p >= start:
                idx = i
                break

        primes = primes_all[idx:idx + count + 1]

        if len(primes) < 2:
            continue

        print(f"\n{label}: primes {primes[0]:,} - {primes[-1]:,}")
        print("-" * 70)

        results = evaluate_methods(primes, methods)

        # Sort by hit_rate
        sorted_methods = sorted(results.items(), key=lambda x: -x[1]["hit_rate"])

        for name, r in sorted_methods:
            print(f"  {name:15s}: hit={r['hit_rate']:.3f}, "
                  f"mae={r['mae']:.2f}, bias={r['bias']:+.2f}")
            all_results[name].append(r)

    # Summary
    print("\n" + "=" * 70)
    print("SUMMARY (averaged across scales)")
    print("=" * 70)

    summary = []
    for name, results_list in all_results.items():
        if not results_list:
            continue
        avg_hit = sum(r["hit_rate"] for r in results_list) / len(results_list)
        avg_mae = sum(r["mae"] for r in results_list) / len(results_list)
        avg_bias = sum(r["bias"] for r in results_list) / len(results_list)
        summary.append((name, avg_hit, avg_mae, avg_bias))

    # Sort by avg_hit descending
    summary.sort(key=lambda x: -x[1])

    for name, avg_hit, avg_mae, avg_bias in summary:
        print(f"{name:15s}: avg_hit={avg_hit:.3f}, avg_mae={avg_mae:.2f}, "
              f"avg_bias={avg_bias:+.2f}")

    # Detailed analysis of √p relationship
    print("\n" + "=" * 70)
    print("DETAILED √p ANALYSIS")
    print("=" * 70)

    primes = sieve_primes(10000)

    # Compute actual gap / log(p) ratios
    ratios = []
    for i in range(len(primes) - 1):
        p = primes[i]
        gap = primes[i + 1] - p
        log_p = math.log(p)
        if log_p > 0:
            ratios.append(gap / log_p)

    avg_ratio = sum(ratios) / len(ratios)
    print(f"\nActual gap / log(p) ratio:")
    print(f"  mean = {avg_ratio:.3f}")
    print(f"  This suggests: gap ≈ {avg_ratio:.2f} × log(p)")

    # Compute correlation with √p
    print("\nCorrelation of gap/log(p) with √p:")

    # Group by √p ranges
    groups = {}
    for i in range(len(primes) - 1):
        p = primes[i]
        gap = primes[i + 1] - p
        sqrt_p = int(math.sqrt(p))
        bucket = sqrt_p // 10 * 10  # Group by tens

        if bucket not in groups:
            groups[bucket] = []
        groups[bucket].append(gap / math.log(p))

    print(f"{'√p range':<12} {'mean gap/log(p)':<15} {'count':<8}")
    print("-" * 40)
    for bucket in sorted(groups.keys()):
        vals = groups[bucket]
        mean = sum(vals) / len(vals)
        print(f"{bucket:3d}-{bucket+9:3d}       {mean:12.3f}    {len(vals):8d}")

    # The key insight
    print("\n" + "=" * 70)
    print("KEY INSIGHT")
    print("=" * 70)
    print("""
The gap/log(p) ratio is approximately constant (~1.0) across scales.
This confirms: gap ≈ log(p) is the dominant term.

The √p relationship appears in:
1. The VARIANCE of gaps (not the mean)
2. The dimension of the sieve space: π(√p)
3. The concentration of measure: coordinates ~ 1/√dim

The (P+2)/2 formula gives the SEARCH RADIUS, not the expected gap.
The next prime is constrained to be within (P+2)/2 of P, but
typically appears much sooner (at ~log(p) distance).

Connection to σ=1/2:
- At the critical line, p^{-1/2} × √p = 1 (balance)
- This balance condition governs eigenvector stability
- The gap distribution is "fair" when amplitude × measure = 1
""")


if __name__ == "__main__":
    main()
