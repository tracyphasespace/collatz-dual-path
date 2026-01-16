#!/usr/bin/env python3
"""
═══════════════════════════════════════════════════════════════════════════════
EVALUATION (2026-01-16):
  - Twin prime finder with O(1) memory using Miller-Rabin
  - Memory: O(1) in walker mode - scales to 10^18+
  - VALUE: UTILITY - finds twin primes at any scale
  - RECOMMENDATION: KEEP - active tool for prime pair research
═══════════════════════════════════════════════════════════════════════════════

Prime Pair Finder - Twin Primes and Beyond

Finds prime pairs (p, p+k) where both p and p+k are prime.

Currently implemented:
  - Twin primes: k=2 (p, p+2) e.g., (3,5), (5,7), (11,13), (17,19)

═══════════════════════════════════════════════════════════════════════════════
FUTURE PLANS:
  - Cousin primes: k=4 (p, p+4) e.g., (3,7), (7,11), (13,17)
  - Sexy primes: k=6 (p, p+6) e.g., (5,11), (7,13), (11,17)
  - Prime triplets: (p, p+2, p+6) or (p, p+4, p+6)
  - Prime quadruplets: (p, p+2, p+6, p+8)
  - Sophie Germain primes: p where 2p+1 is also prime
  - Custom gap searching: arbitrary k values
  - Statistical analysis of gap distributions
═══════════════════════════════════════════════════════════════════════════════

CLI:
  python3 prime_pair_finder.py --start 1000 --end 10000
  python3 prime_pair_finder.py --start 1000000000000 --end 1000000001000 --gap 2
  python3 prime_pair_finder.py --start 10000 --end 100000 --gap 6  # sexy primes
"""
import argparse
import math
import sys
import time

# Memory safety defaults
WALKER_BASIS_SIZE = 200  # Fixed basis for quick filtering


def miller_rabin(n):
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


def sieve_small_primes(limit):
    """Sieve primes up to limit - used for quick filtering basis."""
    if limit < 2:
        return []
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, math.isqrt(limit) + 1):
        if sieve[p]:
            sieve[p*p:limit+1:p] = b"\x00" * ((limit - p*p) // p + 1)
    return [i for i, is_p in enumerate(sieve) if is_p]


def is_prime(n):
    """O(1) memory primality test."""
    return miller_rabin(n)


def find_prime_pairs(start, end, gap=2, basis_size=WALKER_BASIS_SIZE, verbose=True):
    """
    O(1) memory scan for prime pairs (p, p+gap).

    Args:
        start: Beginning of search range
        end: End of search range (inclusive for first prime of pair)
        gap: Distance between primes (2=twin, 4=cousin, 6=sexy)
        basis_size: Number of small primes for quick filtering
        verbose: Print progress and results

    Returns:
        List of tuples (p, p+gap) where both are prime
    """
    # Build small fixed basis for quick filtering
    small_primes = sieve_small_primes(2000)[:basis_size]

    if verbose:
        gap_names = {2: "Twin", 4: "Cousin", 6: "Sexy"}
        gap_name = gap_names.get(gap, f"Gap-{gap}")
        print(f"{'=' * 70}")
        print(f"{gap_name} Prime Finder (gap = {gap})")
        print(f"{'=' * 70}")
        print(f"Range: {start:,} to {end:,}")
        print(f"Filter basis: {len(small_primes)} small primes")
        print(f"Memory: O(1) - scale independent")
        print(f"{'=' * 70}\n")

    prime_pairs = []
    candidates_checked = 0
    mr_checks = 0

    # For gap=2 (twin primes), we can skip even numbers
    # For other gaps, we need to be more careful
    if gap == 2:
        # Twin primes: both must be odd (except 2,3 edge case)
        if start <= 2 and end >= 2:
            # Check (2, 4) - not a twin prime since 4 is not prime
            pass
        if start <= 3 and end >= 3:
            # Check (3, 5) - this IS a twin prime
            if is_prime(3) and is_prime(5):
                prime_pairs.append((3, 5))
                if verbose:
                    print(f"Found: (3, 5)")

        # For n > 3, twin primes are (6k-1, 6k+1)
        # Start from appropriate position
        n = max(start, 5)
        if n % 2 == 0:
            n += 1  # Make odd
    else:
        n = start

    while n <= end:
        candidates_checked += 1

        # Quick filter: check if n is divisible by any small prime
        is_composite = False
        for p in small_primes:
            if p >= n:
                break
            if n % p == 0:
                is_composite = True
                break

        if not is_composite:
            # n passed quick filter - check with Miller-Rabin
            mr_checks += 1
            if miller_rabin(n):
                # n is prime, now check n + gap
                n_plus_gap = n + gap

                # Quick filter for n + gap
                is_composite_2 = False
                for p in small_primes:
                    if p >= n_plus_gap:
                        break
                    if n_plus_gap % p == 0:
                        is_composite_2 = True
                        break

                if not is_composite_2:
                    mr_checks += 1
                    if miller_rabin(n_plus_gap):
                        # Found a prime pair!
                        prime_pairs.append((n, n_plus_gap))
                        if verbose and len(prime_pairs) <= 20:
                            print(f"Found: ({n:,}, {n_plus_gap:,})")
                        elif verbose and len(prime_pairs) == 21:
                            print("... (suppressing further output)")

        # Increment: for twin primes, skip evens
        if gap == 2:
            n += 2
        else:
            n += 1

    if verbose:
        print(f"\n{'=' * 70}")
        print(f"Search Complete")
        print(f"{'=' * 70}")
        print(f"Prime pairs found: {len(prime_pairs)}")
        print(f"Candidates checked: {candidates_checked:,}")
        print(f"Miller-Rabin checks: {mr_checks:,}")
        if prime_pairs:
            print(f"First pair: {prime_pairs[0]}")
            print(f"Last pair: {prime_pairs[-1]}")

    return prime_pairs


def verify_pairs(pairs, gap):
    """Verify all found pairs are actually prime pairs."""
    errors = 0
    for p1, p2 in pairs:
        if not is_prime(p1):
            print(f"ERROR: {p1} is not prime")
            errors += 1
        if not is_prime(p2):
            print(f"ERROR: {p2} is not prime")
            errors += 1
        if p2 - p1 != gap:
            print(f"ERROR: gap between {p1} and {p2} is {p2-p1}, expected {gap}")
            errors += 1

    if errors == 0:
        print(f"Verification PASSED: All {len(pairs)} pairs verified.")
    else:
        print(f"Verification FAILED: {errors} errors found.")

    return errors == 0


def parse_args():
    parser = argparse.ArgumentParser(
        description="Find prime pairs (p, p+k) with O(1) memory."
    )
    parser.add_argument("--start", type=int, default=1000,
                        help="Search start.")
    parser.add_argument("--end", type=int, default=10000,
                        help="Search end (inclusive for first prime of pair).")
    parser.add_argument("--gap", type=int, default=2,
                        help="Gap between primes: 2=twin, 4=cousin, 6=sexy (default: 2)")
    parser.add_argument("--no-verify", action="store_true",
                        help="Skip verification step.")
    parser.add_argument("--quiet", action="store_true",
                        help="Minimal output.")
    parser.add_argument("--walker-basis", type=int, default=WALKER_BASIS_SIZE,
                        help=f"Basis size for quick filtering (default: {WALKER_BASIS_SIZE}).")
    return parser.parse_args()


def main():
    args = parse_args()

    if args.end < args.start:
        raise SystemExit("--end must be >= --start.")

    if args.gap < 1:
        raise SystemExit("--gap must be >= 1.")

    t0 = time.perf_counter()
    pairs = find_prime_pairs(
        args.start,
        args.end,
        gap=args.gap,
        basis_size=args.walker_basis,
        verbose=not args.quiet
    )
    t1 = time.perf_counter()

    print(f"\nTiming: search={t1 - t0:.4f}s")

    if not args.no_verify and pairs:
        t2 = time.perf_counter()
        verify_pairs(pairs, args.gap)
        t3 = time.perf_counter()
        print(f"Timing: verify={t3 - t2:.4f}s")

    # Summary statistics
    if pairs and not args.quiet:
        gaps_between_pairs = [pairs[i+1][0] - pairs[i][0] for i in range(len(pairs)-1)]
        if gaps_between_pairs:
            avg_gap = sum(gaps_between_pairs) / len(gaps_between_pairs)
            max_gap = max(gaps_between_pairs)
            min_gap = min(gaps_between_pairs)
            print(f"\nGap statistics between consecutive pairs:")
            print(f"  Min: {min_gap}, Max: {max_gap}, Avg: {avg_gap:.1f}")


if __name__ == "__main__":
    main()
