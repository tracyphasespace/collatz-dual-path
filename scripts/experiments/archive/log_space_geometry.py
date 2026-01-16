#!/usr/bin/env python3
"""
═══════════════════════════════════════════════════════════════════════════════
EVALUATION (2026-01-16):
  - Explores log-space geometry of primes
  - Memory: O(1)
  - VALUE: PEDAGOGICAL - explains why log appears everywhere
  - RECOMMENDATION: Archive - overlaps with outer_product_direction
═══════════════════════════════════════════════════════════════════════════════

Log Space Geometry - How log(n) Captures Each Prime Dimension

Key insight from the user: "log(n) captures each space"

The geometry:
- Each integer n lives at "position" log(n) in logarithmic space
- Primes are evenly spaced in log space (approximately, by PNT)
- The sieve operates MULTIPLICATIVELY, which becomes ADDITIVE in log space

Why log is the natural coordinate:
1. n = p1^a1 × p2^a2 × ... → log(n) = a1·log(p1) + a2·log(p2) + ...
   Multiplication becomes vector addition!

2. The "distance" between n and 2n is always log(2), regardless of n
   This is scale invariance.

3. Each prime p creates a LATTICE with spacing log(p)
   Integers are the intersection of all these lattices.

4. The critical line σ = 1/2 is where the "weight" p^{-σ} and
   "lattice spacing" log(p) are balanced: p^{-1/2} × √p = 1

This script visualizes the log-space structure.
"""
import math
import numpy as np

def sieve_primes(limit):
    if limit < 2:
        return []
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, int(limit**0.5) + 1):
        if sieve[p]:
            sieve[p*p:limit+1:p] = b"\x00" * ((limit - p*p) // p + 1)
    return [i for i, is_p in enumerate(sieve) if is_p]


def visualize_log_lattice():
    """
    Show how each prime creates a lattice in log space.
    """
    print("=" * 70)
    print("LOG SPACE LATTICE STRUCTURE")
    print("=" * 70)

    print("""
In logarithmic space, each prime p creates a periodic structure:
- Multiples of p occur at: log(p), log(2p), log(3p), ... = log(p) + log(k)
- Spacing between consecutive multiples: log((k+1)p) - log(kp) = log(1 + 1/k)
  → approaches 0 as k→∞ (multiples get denser in log space)

But the FUNDAMENTAL period is log(p).

A number n is divisible by p if log(n) ≡ 0 (mod log(p)) in some sense.
More precisely: n ≡ 0 (mod p) iff n hits the p-lattice.
""")

    primes = [2, 3, 5, 7]

    print("\nLattice positions (multiples of p) in log space:")
    print("-" * 60)

    max_log = 4.0  # Show up to e^4 ≈ 55
    scale = 60  # Characters width

    for p in primes:
        positions = []
        k = 1
        while math.log(k * p) <= max_log:
            positions.append(math.log(k * p))
            k += 1

        # Create visual representation
        line = [' '] * (scale + 1)
        for pos in positions:
            idx = int(pos / max_log * scale)
            if 0 <= idx <= scale:
                line[idx] = '|'

        print(f"p={p}: {''.join(line)}")
        print(f"     log(p)={math.log(p):.3f}, positions: {[f'{x:.2f}' for x in positions[:8]]}...")

    # Show integers
    print("\nAll integers in log space:")
    int_line = [' '] * (scale + 1)
    for n in range(1, 56):
        pos = math.log(n)
        if pos <= max_log:
            idx = int(pos / max_log * scale)
            if 0 <= idx <= scale:
                int_line[idx] = '*'
    print(f"n:  {''.join(int_line)}")

    # Show primes
    print("\nPrimes only in log space:")
    prime_line = [' '] * (scale + 1)
    for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53]:
        pos = math.log(p)
        if pos <= max_log:
            idx = int(pos / max_log * scale)
            if 0 <= idx <= scale:
                prime_line[idx] = 'P'
    print(f"P:  {''.join(prime_line)}")


def factorization_as_coordinates():
    """
    Show how factorization becomes coordinates in prime-log space.
    """
    print("\n" + "=" * 70)
    print("FACTORIZATION AS COORDINATES IN LOG SPACE")
    print("=" * 70)

    print("""
Every integer n has a unique factorization:
    n = 2^a × 3^b × 5^c × 7^d × ...

In log space, this becomes:
    log(n) = a·log(2) + b·log(3) + c·log(5) + d·log(7) + ...

This is a LINEAR COMBINATION of the basis vectors {log(2), log(3), log(5), ...}

The integers form a LATTICE in this infinite-dimensional space!
The primes are the BASIS VECTORS.
""")

    primes = [2, 3, 5, 7, 11]

    print(f"\n{'n':<6} {'Factorization':<25} {'Coords (a,b,c,d,e)':<25} {'log(n)':<10} {'Check':<10}")
    print("-" * 80)

    for n in [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 15, 18, 20, 24, 30, 36, 60]:
        # Get prime factorization
        coords = []
        temp = n
        for p in primes:
            count = 0
            while temp % p == 0:
                temp //= p
                count += 1
            coords.append(count)

        # Compute log(n) from coordinates
        log_n_computed = sum(c * math.log(p) for c, p in zip(coords, primes))
        log_n_actual = math.log(n) if n > 0 else 0

        # Format factorization
        factors = []
        for c, p in zip(coords, primes):
            if c > 0:
                factors.append(f"{p}^{c}" if c > 1 else str(p))
        fact_str = " × ".join(factors) if factors else "1"

        coord_str = str(tuple(coords))
        check = "✓" if abs(log_n_computed - log_n_actual) < 0.0001 else "✗"

        print(f"{n:<6} {fact_str:<25} {coord_str:<25} {log_n_actual:<10.4f} {check:<10}")


def von_mangoldt_geometry():
    """
    Show the geometric meaning of the von Mangoldt function.
    """
    print("\n" + "=" * 70)
    print("VON MANGOLDT FUNCTION: THE GEOMETRIC STIFFNESS")
    print("=" * 70)

    print("""
The von Mangoldt function:
    Λ(n) = log(p) if n = p^k for some prime p
           0      otherwise

Geometric interpretation:
- Each prime p contributes "stiffness" log(p) to the lattice
- Prime powers p^k all contribute the SAME stiffness log(p)
- This is because p^k creates a "resonance" at scale p

The Chebyshev function:
    ψ(x) = Σ_{n≤x} Λ(n) ≈ x

This says: "Total stiffness up to x equals x"
The primes collectively create a lattice with total measure proportional to x.
""")

    primes = sieve_primes(100)

    print(f"\n{'n':<6} {'Λ(n)':<10} {'Type':<20} {'Cumulative':<15}")
    print("-" * 55)

    cumulative = 0
    for n in range(1, 35):
        # Compute Λ(n)
        lambda_n = 0
        n_type = ""

        for p in primes:
            if p > n:
                break
            # Check if n is a power of p
            pk = p
            k = 1
            while pk <= n:
                if pk == n:
                    lambda_n = math.log(p)
                    n_type = f"p={p}, k={k}" if k == 1 else f"{p}^{k}"
                    break
                pk *= p
                k += 1
            if lambda_n > 0:
                break

        if lambda_n == 0 and n > 1:
            n_type = "composite"

        cumulative += lambda_n

        lambda_str = f"{lambda_n:.4f}" if lambda_n > 0 else "-"
        print(f"{n:<6} {lambda_str:<10} {n_type:<20} {cumulative:<15.4f}")


def resonance_at_zeros():
    """
    Show how zeros are resonances in log space.
    """
    print("\n" + "=" * 70)
    print("RESONANCE AT ZETA ZEROS: WAVE INTERFERENCE IN LOG SPACE")
    print("=" * 70)

    print("""
At the critical line s = 1/2 + it, each prime p contributes a wave:
    p^{-1/2} × e^{-it log(p)} = p^{-1/2} × (cos(t log p) - i sin(t log p))

A zeta ZERO occurs when all these waves destructively interfere:
    Σ_p p^{-1/2} × e^{-it log(p)} = 0

This is a RESONANCE condition in log space:
- Each prime p oscillates at "frequency" log(p) in the t-variable
- At a zero t = γ, the frequencies {γ log(2), γ log(3), γ log(5), ...}
  align such that the weighted sum vanishes

The log(p) terms are the "natural frequencies" of the prime lattice.
The zeros are the "eigenfrequencies" where resonance occurs.
""")

    ZETA_ZEROS = [14.134725, 21.022040, 25.010858, 30.424876, 32.935062]
    primes = sieve_primes(100)[:15]

    print("\nWave phases at first zero (γ₁ = 14.1347):")
    print("-" * 60)

    gamma = ZETA_ZEROS[0]
    print(f"{'p':<6} {'log(p)':<10} {'γ·log(p)':<12} {'phase/2π':<10} {'cos':<10} {'sin':<10}")

    total_cos = 0
    total_sin = 0
    for p in primes[:10]:
        log_p = math.log(p)
        angle = gamma * log_p
        phase = (angle / (2 * math.pi)) % 1
        cos_val = math.cos(angle)
        sin_val = math.sin(angle)
        weight = p ** (-0.5)

        total_cos += weight * cos_val
        total_sin += weight * sin_val

        print(f"{p:<6} {log_p:<10.4f} {angle:<12.4f} {phase:<10.4f} {cos_val:<10.4f} {sin_val:<10.4f}")

    print(f"\nWeighted sum (first 10 primes):")
    print(f"  Real part: {total_cos:.6f}")
    print(f"  Imag part: {total_sin:.6f}")
    print(f"  |sum|: {math.sqrt(total_cos**2 + total_sin**2):.6f}")


def the_key_insight():
    """
    Summarize the key geometric insight.
    """
    print("\n" + "=" * 70)
    print("THE KEY INSIGHT: log(n) AS THE NATURAL GEOMETRY")
    print("=" * 70)

    print("""
Why log(n) is the right coordinate system:

1. MULTIPLICATIVE → ADDITIVE
   n = p₁^a₁ × p₂^a₂ × ... becomes
   log(n) = a₁ log(p₁) + a₂ log(p₂) + ...

   Multiplication (the fundamental operation on integers)
   becomes addition (linear algebra!).

2. SCALE INVARIANCE
   The "structure" of primes is the same at all scales.
   In log space, this means translation invariance.

   Going from n to 2n is always the same "distance" log(2).

3. LATTICE STRUCTURE
   Multiples of p form a lattice with spacing ~log(p).
   Integers are the intersection of all these lattices.
   Primes are the points that ESCAPE all lattices.

4. STIFFNESS = log(p)
   The "energy cost" of including prime p is log(p).
   This comes from the derivative d/ds(p^{-s}) = -log(p) × p^{-s}.

   The von Mangoldt function Λ(n) = log(p) is GEOMETRIC.

5. BALANCE AT σ = 1/2
   At the critical line:
   - Weight of prime p: p^{-1/2}
   - Lattice contribution: √p (measure theory)
   - Product: p^{-1/2} × √p = 1 for ALL primes!

   This is the ONLY σ where all primes balance equally.

6. ZEROS AS RESONANCES
   At a zeta zero t = γ:
   - Each prime oscillates at frequency γ × log(p)
   - These frequencies are INCOMMENSURATE (log(p)/log(q) irrational)
   - Yet they conspire to cancel: Σ p^{-1/2} e^{-iγ log p} = 0

   The zeros are the "eigenfrequencies" of the prime lattice.

THE AXIOM GAP:
We need to prove that at a zero γ, the resonance condition implies
the existence of a non-trivial kernel vector for the operator K(s).

The geometric picture suggests:
- The resonance creates a "standing wave" pattern
- This pattern is the kernel vector
- The log(p) weights ensure it has the right structure
""")


def main():
    visualize_log_lattice()
    factorization_as_coordinates()
    von_mangoldt_geometry()
    resonance_at_zeros()
    the_key_insight()


if __name__ == "__main__":
    main()
