#!/usr/bin/env python3
"""
═══════════════════════════════════════════════════════════════════════════════
EVALUATION (2026-01-16):
  - Visualization of multi-dimensional sieve structure
  - Memory: O(N) - not scalable
  - VALUE: PEDAGOGICAL - helps understand the geometry
  - Connects to Lean: BivectorStructure.e_orthogonal
  - RECOMMENDATION: Archive - visualization only
═══════════════════════════════════════════════════════════════════════════════

Dimensional Sieve - Understanding What Each Prime Dimension Does

Key insight: Each prime p adds a new "dimension" to the sieve.
The survivors are the INTERSECTION of all "non-zero mod p" sets.

This is like the Menger sponge:
- Each iteration removes a "middle" portion
- The remaining structure has fractal dimension
- Volume → 0, Surface → ∞

The primes are the "dust" left after infinite dimensional sieving.
"""
import math

def sieve_primes(limit):
    if limit < 2:
        return []
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, int(limit**0.5) + 1):
        if sieve[p]:
            sieve[p*p:limit+1:p] = b"\x00" * ((limit - p*p) // p + 1)
    return [i for i, is_p in enumerate(sieve) if is_p]


def dimensional_view(n, primes):
    """
    Show n's coordinates in each prime dimension.

    n's coordinate in dimension p is: n mod p
    If coordinate = 0, n is "on the surface" (divisible by p)
    If coordinate ≠ 0, n is "off the surface" (survives this sieve)
    """
    coords = []
    for p in primes:
        if p > n:
            break
        coords.append(n % p)
    return coords


def survival_at_each_dimension(start, end, max_primes=10):
    """
    Show how many candidates survive as we add each prime dimension.
    """
    primes = sieve_primes(100)[:max_primes]

    print(f"Range [{start}, {end}]: {end - start + 1} integers")
    print("-" * 60)

    survivors = list(range(start, end + 1))

    for i, p in enumerate(primes):
        # Remove multiples of p
        survivors = [n for n in survivors if n % p != 0 or n == p]
        density = len(survivors) / (end - start + 1)
        theoretical = math.prod((1 - 1/q) for q in primes[:i+1])

        print(f"After mod {p:2d}: {len(survivors):4d} survive "
              f"({density:.3f}) | theoretical: {theoretical:.3f}")

    # Count actual primes
    actual_primes = [n for n in range(start, end + 1) if n > 1 and is_prime(n)]
    print(f"\nActual primes: {len(actual_primes)}")
    print(f"Survivors that are prime: {[n for n in survivors if n in actual_primes][:20]}...")


def is_prime(n):
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    for i in range(3, int(n**0.5) + 1, 2):
        if n % i == 0:
            return False
    return True


def phase_shift_visualization():
    """
    Show how the "phase" of primes shifts as we move through ranges.

    This illustrates the non-intuitive nature: primes don't "shift" linearly.
    """
    print("\n" + "=" * 70)
    print("PHASE SHIFT: How primes change across ranges")
    print("=" * 70)

    primes_in_range = []
    for start in [0, 10, 20, 30, 40, 50, 60, 70, 80, 90]:
        end = start + 10
        primes = [p for p in range(max(2, start), end) if is_prime(p)]
        primes_in_range.append((start, end, primes))

    print(f"\n{'Range':<12} {'Primes':<30} {'Count':<6} {'Density':<8}")
    print("-" * 60)

    for start, end, primes in primes_in_range:
        prime_str = str(primes)[:28]
        density = len(primes) / 10
        print(f"[{start:2d}, {end:2d})    {prime_str:<30} {len(primes):<6} {density:<8.2f}")

    print("\nNotice: The pattern doesn't repeat! Each range is unique.")


def coordinate_visualization():
    """
    Show the multi-dimensional coordinates of numbers.
    """
    print("\n" + "=" * 70)
    print("MULTI-DIMENSIONAL COORDINATES")
    print("Each number has coordinates (n mod 2, n mod 3, n mod 5, n mod 7, ...)")
    print("Primes have ALL non-zero coordinates (for primes < themselves)")
    print("=" * 70)

    primes = [2, 3, 5, 7, 11]

    print(f"\n{'n':>4} | ", end="")
    for p in primes:
        print(f"mod {p:<2}", end=" ")
    print("| Prime? | Note")
    print("-" * 60)

    for n in range(2, 35):
        coords = [n % p for p in primes if p < n]
        coord_str = " ".join(f"{c:>4}" for c in coords)
        # Pad to align
        while len(coords) < len(primes):
            coord_str += "    -"
            coords.append(-1)

        is_p = is_prime(n)

        # Check if all relevant coords are non-zero
        relevant_coords = [n % p for p in primes if p < n and p * p <= n]
        all_nonzero = all(c != 0 for c in relevant_coords) if relevant_coords else True

        # Find zeros
        zeros = [p for p in primes if p < n and n % p == 0]

        note = ""
        if is_p:
            note = "PRIME"
        elif zeros:
            note = f"÷ {zeros[0]}"

        # Color coding: zeros in coordinates indicate divisibility
        coord_display = []
        for i, p in enumerate(primes):
            if p >= n:
                coord_display.append("  - ")
            elif n % p == 0:
                coord_display.append(f" [0]")  # Highlight zeros
            else:
                coord_display.append(f"  {n % p} ")

        print(f"{n:4d} | {''.join(coord_display)} | {'  ✓' if is_p else '   '} | {note}")


def surface_tension_visualization():
    """
    Visualize the "surface" between prime and composite regions.
    """
    print("\n" + "=" * 70)
    print("SURFACE TENSION: The boundary between prime and composite")
    print("=" * 70)

    print("""
Think of it like a 2D slice through infinite-dimensional space:

    mod 2 →
  m  0 1 2 3 4 5 6 7 8 9 ...
  o  ┌─────────────────────
  d  0│ · · · · · · · · · ·   (multiples of both 2 and 3)
     1│ · ■ · ■ · ■ · ■ · ■   (odd multiples of 3)
  3  2│ · ■ · ■ · ■ · ■ · ■   (odd, not mult of 3)
  ↓  3│ · · · · · · · · · ·   (multiples of 3)
     4│ · ■ · ■ · ■ · ■ · ■
     5│ · ■ · ■ · ■ · ■ · ■

■ = candidate (survives mod 2 and mod 3)
· = removed (divisible by 2 or 3)

The "surface" is the boundary of the ■ region.
Adding mod 5 removes more ■, shrinking the region further.
""")

    # Actual grid
    print("\nActual sieve grid (mod 6 = mod 2 × mod 3):")
    print("Position mod 6:  0  1  2  3  4  5")
    print("                ─────────────────")
    print("Divisible by 2:  ✓  ·  ✓  ·  ✓  ·")
    print("Divisible by 3:  ✓  ·  ·  ✓  ·  ·")
    print("Survives both:   ·  ✓  ·  ·  ·  ✓")
    print("\nOnly positions 1 and 5 (mod 6) can be prime (except 2, 3)")
    print("This is the 'wheel' pattern with period 6")


def menger_analogy():
    """
    Show how the sieve is like Menger sponge iteration.
    """
    print("\n" + "=" * 70)
    print("MENGER SPONGE ANALOGY")
    print("=" * 70)

    print("""
Menger Sponge:
- Start: Solid cube (all integers)
- Iteration 1: Remove center + face centers (27 → 20 subcubes)
- Iteration 2: Same removal in each subcube
- Limit: Zero volume, infinite surface area, dimension log(20)/log(3) ≈ 2.73

Prime Sieve:
- Start: All integers [2, N]
- After mod 2: N/2 remain (remove evens)
- After mod 3: N/2 × 2/3 = N/3 remain
- After mod 5: N/3 × 4/5 = 4N/15 remain
- After mod p: multiply by (p-1)/p
- Limit: N/log(N) primes remain (Prime Number Theorem)

The "fractal dimension" of primes:
- Count in [1,N] ~ N/log(N)
- This is like dimension 1 - ε where ε → 0 slowly
""")

    # Show the product
    primes = sieve_primes(100)

    print("\nDensity after each prime sieve:")
    print(f"{'Primes used':<20} {'Product':<15} {'1/Product':<15}")
    print("-" * 50)

    product = 1.0
    for i in range(1, 15):
        ps = primes[:i]
        product *= (1 - 1/primes[i-1])
        inv = 1/product if product > 0 else float('inf')
        print(f"{str(ps):<20} {product:<15.6f} {inv:<15.2f}")

    print("\nMertens' theorem: Π(1-1/p) for p≤N ~ e^(-γ)/log(N)")
    print("where γ ≈ 0.5772 (Euler-Mascheroni constant)")


def main():
    print("=" * 70)
    print("DIMENSIONAL SIEVE VISUALIZATION")
    print("Understanding what each prime dimension does")
    print("=" * 70)

    # Show survival at each dimension
    print("\n1. SURVIVAL THROUGH DIMENSIONS")
    survival_at_each_dimension(1, 100, max_primes=8)

    # Show phase shifts
    phase_shift_visualization()

    # Show coordinates
    coordinate_visualization()

    # Surface tension
    surface_tension_visualization()

    # Menger analogy
    menger_analogy()

    print("\n" + "=" * 70)
    print("KEY INSIGHT")
    print("=" * 70)
    print("""
The primes are not "random" - they are the DETERMINISTIC result of
infinite-dimensional sieving. But predicting WHERE they land requires
knowing the "phase alignment" of ALL prime waves simultaneously.

The critical line σ = 1/2 is where:
- The "weight" p^{-1/2} of each prime
- Exactly balances the "measure" √p of its contribution
- p^{-1/2} × √p = 1 for ALL primes

This balance is the "surface tension" being zero - the boundary
between prime and composite regions is in equilibrium.

Away from σ = 1/2:
- σ < 1/2: Small primes dominate (inward tension)
- σ > 1/2: Large primes dominate (outward tension)
- The imbalance creates "stress" that breaks the symmetry
""")


if __name__ == "__main__":
    main()
