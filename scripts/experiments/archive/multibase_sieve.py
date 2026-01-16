#!/usr/bin/env python3
"""
═══════════════════════════════════════════════════════════════════════════════
EVALUATION (2026-01-16):
  - Visualization of Chinese Remainder Theorem geometry
  - Memory: O(N) - not scalable
  - VALUE: PEDAGOGICAL - helps understand multi-dimensional coordinates
  - RECOMMENDATION: Archive - overlaps with dimensional_sieve
═══════════════════════════════════════════════════════════════════════════════

Multi-Base Prime View - Menger Sponge Analogy

Each prime p defines a dimension. A number n's "coordinate" in that dimension
is its last digit in base p, which equals n mod p.

Primes have non-zero last digit in ALL prime bases (up to √n).
Composites have at least one zero (divisible by that prime).

This is the Chinese Remainder Theorem geometrized.
"""
import math

def last_digit_in_base(n, base):
    """Last digit of n in given base = n mod base"""
    return n % base

def prime_coordinates(n, bases):
    """Return n's coordinates in each prime base (the last digits)"""
    return [n % b for b in bases]

def residue_sum(n, limit):
    """Sum of all residues - simpler than cosine formula"""
    return sum(n % r for r in range(2, limit + 1))

def is_prime_simple(n):
    """Simple primality check"""
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    for i in range(3, int(math.sqrt(n)) + 1, 2):
        if n % i == 0:
            return False
    return True

def main():
    print("=" * 70)
    print("MULTI-BASE PRIME VIEW")
    print("Primes have non-zero last digit in every prime base")
    print("=" * 70)

    # Small primes as our "dimensions"
    prime_bases = [2, 3, 5, 7, 11, 13]

    print(f"\nBases (dimensions): {prime_bases}")
    print(f"{'n':>4} {'prime?':>6} | coordinates (n mod base) | residue_sum")
    print("-" * 70)

    # Show coordinates for numbers 2-50
    for n in range(2, 51):
        coords = prime_coordinates(n, prime_bases)
        is_p = is_prime_simple(n)

        # Check: primes should have all non-zero coords (for bases < n)
        relevant_bases = [b for b in prime_bases if b < n]
        relevant_coords = [n % b for b in relevant_bases]
        all_nonzero = all(c != 0 for c in relevant_coords)

        # Residue sum (using integers, not just primes)
        rsum = residue_sum(n, min(n-1, 10))

        coord_str = " ".join(f"{c}" for c in coords)
        marker = "✓" if is_p else ""

        print(f"{n:4d} {marker:>6} | [{coord_str:17}] | {rsum:4d}")

    # Statistical analysis
    print("\n" + "=" * 70)
    print("RESIDUE SUM ANALYSIS")
    print("=" * 70)

    # Test: do primes have higher residue sums?
    prime_rsums = []
    composite_rsums = []

    for n in range(10, 1000):
        rsum = residue_sum(n, int(math.sqrt(n)))
        if is_prime_simple(n):
            prime_rsums.append(rsum)
        else:
            composite_rsums.append(rsum)

    avg_prime = sum(prime_rsums) / len(prime_rsums)
    avg_comp = sum(composite_rsums) / len(composite_rsums)

    print(f"\nRange 10-1000, residue sum up to √n:")
    print(f"  Primes (n={len(prime_rsums)}):     avg residue_sum = {avg_prime:.2f}")
    print(f"  Composites (n={len(composite_rsums)}): avg residue_sum = {avg_comp:.2f}")
    print(f"  Difference: {avg_prime - avg_comp:.2f}")
    print(f"  Ratio: {avg_prime / avg_comp:.3f}")

    # Normalized by number of terms
    print("\n" + "-" * 70)
    print("Normalized residue sum (divide by √n):")

    prime_norm = []
    comp_norm = []

    for n in range(10, 1000):
        sqrt_n = int(math.sqrt(n))
        rsum = residue_sum(n, sqrt_n)
        normalized = rsum / sqrt_n if sqrt_n > 0 else 0

        if is_prime_simple(n):
            prime_norm.append(normalized)
        else:
            comp_norm.append(normalized)

    avg_prime_n = sum(prime_norm) / len(prime_norm)
    avg_comp_n = sum(comp_norm) / len(comp_norm)

    print(f"  Primes:     avg normalized = {avg_prime_n:.2f}")
    print(f"  Composites: avg normalized = {avg_comp_n:.2f}")
    print(f"  Ratio: {avg_prime_n / avg_comp_n:.3f}")

    # The multi-base "Menger" view
    print("\n" + "=" * 70)
    print("MENGER SPONGE VIEW: Which coordinates are zero?")
    print("=" * 70)

    print(f"\n{'n':>4} {'type':>10} | zero positions (divisible by)")
    print("-" * 50)

    for n in range(2, 40):
        zeros = [b for b in prime_bases if n % b == 0 and b <= n]

        if is_prime_simple(n):
            ntype = "PRIME"
        elif len(zeros) >= 3:
            ntype = "highly_comp"
        else:
            ntype = "composite"

        zero_str = ", ".join(str(z) for z in zeros) if zeros else "(none)"
        print(f"{n:4d} {ntype:>10} | {zero_str}")

    print("\n" + "=" * 70)
    print("KEY INSIGHT")
    print("=" * 70)
    print("""
Primes: zero coordinates at position 'self' only (n mod n = 0)
        All other coordinates non-zero → survives all "surfaces"

Composites: zero coordinates at their factors
            Removed by at least one "surface"

The Menger sponge removes middle-third in base 3.
The prime sieve removes last-digit-zero in each prime base.

Both create fractal-like structures through repeated "surface removal".
""")


if __name__ == "__main__":
    main()
