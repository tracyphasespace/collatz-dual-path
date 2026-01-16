#!/usr/bin/env python3
"""
═══════════════════════════════════════════════════════════════════════════════
EVALUATION (2026-01-16):
  - Tests the Zeta Link hypothesis: ζ(s)=0 → eigenvalue 1 exists
  - Memory: O(1)
  - VALUE: VERIFICATION - tests the AXIOM numerically
  - Finding: eigenvalue 1 doesn't obviously appear (finite truncation issue)
  - Connects to Lean: Axioms.lean `zero_implies_kernel`
  - RECOMMENDATION: KEEP - documents why axiom can't be proven numerically
═══════════════════════════════════════════════════════════════════════════════

Zeta Link Numerical Test

The Zeta Link hypothesis (Assumption 5.1 in the paper) states:
    If ζ(s) = 0 with 0 < Re(s) < 1, then ∃ B ≥ 2, v ≠ 0 such that K_B(s)v = v

The Sieve Operator is:
    K_B(s) = Σ_{p≤B} (p^{-s} T_{log p} + p^{-(1-s)} T_{-log p})

Where T_a is translation by a. In Fourier space (exponential basis e^{iωx}),
translation becomes multiplication:
    T_a(e^{iωx}) = e^{-iωa} e^{iωx}

So for v_ω(x) = e^{iωx}, the eigenvalue is:
    λ(s, ω) = Σ_p (p^{-s} e^{-iω log p} + p^{-(1-s)} e^{iω log p})

The Zeta Link claims: at zeta zeros s, there exists ω such that λ(s, ω) = 1.

This script tests this numerically.
"""
import cmath
import math

# First 10 Riemann zeta zeros (imaginary parts, real part is 1/2)
ZETA_ZEROS = [
    14.134725142,
    21.022039639,
    25.010857580,
    30.424876126,
    32.935061588,
    37.586178159,
    40.918719012,
    43.327073281,
    48.005150881,
    49.773832478,
]

# Small primes for the operator basis
def sieve_primes(limit):
    if limit < 2:
        return []
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, int(limit**0.5) + 1):
        if sieve[p]:
            sieve[p*p:limit+1:p] = b"\x00" * ((limit - p*p) // p + 1)
    return [i for i, is_p in enumerate(sieve) if is_p]


def eigenvalue_at_omega(s, omega, primes):
    """
    Compute λ(s, ω) = Σ_p (p^{-s} e^{-iω log p} + p^{-(1-s)} e^{iω log p})

    This is the eigenvalue of K_B(s) for the eigenvector e^{iωx}.
    """
    total = 0j
    for p in primes:
        log_p = math.log(p)

        # p^{-s} e^{-iω log p} = p^{-s} · e^{-iω log p} = e^{-s log p} · e^{-iω log p}
        #                      = e^{-(s + iω) log p} = p^{-(s + iω)}
        term1 = cmath.exp(-(s + 1j * omega) * log_p)

        # p^{-(1-s)} e^{iω log p} = p^{-(1-s+iω)}
        term2 = cmath.exp(-(1 - s + 1j * omega) * log_p)

        total += term1 + term2

    return total


def find_eigenvalue_one(s, primes, omega_range=(-50, 50), steps=1000):
    """
    Scan omega values to find where |λ(s, ω) - 1| is minimized.

    If min is close to 0, then eigenvalue 1 exists at that omega.
    """
    best_omega = None
    best_dist = float('inf')
    best_lambda = None

    for i in range(steps):
        omega = omega_range[0] + (omega_range[1] - omega_range[0]) * i / steps
        lam = eigenvalue_at_omega(s, omega, primes)
        dist = abs(lam - 1)

        if dist < best_dist:
            best_dist = dist
            best_omega = omega
            best_lambda = lam

    return best_omega, best_lambda, best_dist


def test_zeta_link():
    """Test the Zeta Link at known zeta zeros vs random points."""

    print("=" * 70)
    print("ZETA LINK NUMERICAL TEST")
    print("Testing: Does eigenvalue 1 appear at zeta zeros?")
    print("=" * 70)

    # Use primes up to various limits
    for B in [50, 100, 500]:
        primes = sieve_primes(B)

        print(f"\n{'='*70}")
        print(f"Operator K_B with B={B} ({len(primes)} primes)")
        print("=" * 70)

        # Test at zeta zeros (s = 1/2 + i*gamma)
        print(f"\n{'s (zeta zero)':<25} {'best ω':<12} {'λ(s,ω)':<25} {'|λ-1|':<12}")
        print("-" * 70)

        zero_distances = []
        for gamma in ZETA_ZEROS[:5]:
            s = 0.5 + 1j * gamma
            omega, lam, dist = find_eigenvalue_one(s, primes)
            zero_distances.append(dist)
            print(f"0.5 + {gamma:.4f}i      {omega:>10.4f}   {lam.real:>+10.6f}{lam.imag:>+10.6f}i   {dist:.6f}")

        # Test at NON-zeros (same real part, different imaginary)
        print(f"\n{'s (NOT zero)':<25} {'best ω':<12} {'λ(s,ω)':<25} {'|λ-1|':<12}")
        print("-" * 70)

        non_zero_distances = []
        test_points = [10.0, 15.0, 18.0, 22.5, 27.0]  # Between zeros
        for gamma in test_points:
            s = 0.5 + 1j * gamma
            omega, lam, dist = find_eigenvalue_one(s, primes)
            non_zero_distances.append(dist)
            print(f"0.5 + {gamma:.4f}i      {omega:>10.4f}   {lam.real:>+10.6f}{lam.imag:>+10.6f}i   {dist:.6f}")

        # Test OFF the critical line (should be worse)
        print(f"\n{'s (off line)':<25} {'best ω':<12} {'λ(s,ω)':<25} {'|λ-1|':<12}")
        print("-" * 70)

        off_line_distances = []
        for sigma in [0.3, 0.4, 0.6, 0.7]:
            gamma = 14.134725  # First zero's imaginary part
            s = sigma + 1j * gamma
            omega, lam, dist = find_eigenvalue_one(s, primes)
            off_line_distances.append(dist)
            print(f"{sigma:.1f} + {gamma:.4f}i      {omega:>10.4f}   {lam.real:>+10.6f}{lam.imag:>+10.6f}i   {dist:.6f}")

        # Summary
        print(f"\n--- Summary for B={B} ---")
        print(f"At zeta zeros:     avg |λ-1| = {sum(zero_distances)/len(zero_distances):.6f}")
        print(f"Between zeros:     avg |λ-1| = {sum(non_zero_distances)/len(non_zero_distances):.6f}")
        print(f"Off critical line: avg |λ-1| = {sum(off_line_distances)/len(off_line_distances):.6f}")


def detailed_omega_scan():
    """Detailed scan showing λ(s,ω) as function of ω at a zeta zero."""

    print("\n" + "=" * 70)
    print("DETAILED OMEGA SCAN AT FIRST ZETA ZERO")
    print("s = 0.5 + 14.1347i")
    print("=" * 70)

    primes = sieve_primes(100)
    s = 0.5 + 1j * ZETA_ZEROS[0]

    print(f"\n{'ω':<10} {'Re(λ)':<12} {'Im(λ)':<12} {'|λ|':<10} {'|λ-1|':<10}")
    print("-" * 55)

    for omega in range(-30, 31, 2):
        lam = eigenvalue_at_omega(s, omega, primes)
        print(f"{omega:<10} {lam.real:<12.6f} {lam.imag:<12.6f} {abs(lam):<10.6f} {abs(lam-1):<10.6f}")


def convergence_test():
    """Test how eigenvalue converges as B increases."""

    print("\n" + "=" * 70)
    print("CONVERGENCE TEST: How does λ change with B?")
    print("At first zeta zero s = 0.5 + 14.1347i")
    print("=" * 70)

    s = 0.5 + 1j * ZETA_ZEROS[0]

    print(f"\n{'B':<8} {'#primes':<10} {'best ω':<10} {'|λ-1|':<12} {'Re(λ)':<12} {'Im(λ)':<12}")
    print("-" * 70)

    for B in [10, 20, 50, 100, 200, 500, 1000]:
        primes = sieve_primes(B)
        omega, lam, dist = find_eigenvalue_one(s, primes, omega_range=(-30, 30), steps=500)
        print(f"{B:<8} {len(primes):<10} {omega:<10.4f} {dist:<12.6f} {lam.real:<12.6f} {lam.imag:<12.6f}")


def main():
    test_zeta_link()
    detailed_omega_scan()
    convergence_test()

    print("\n" + "=" * 70)
    print("INTERPRETATION")
    print("=" * 70)
    print("""
The Zeta Link hypothesis claims that at zeta zeros, eigenvalue 1 exists.

What we're testing:
1. Is |λ-1| smaller at zeta zeros than elsewhere? (ZETA LINK EVIDENCE)
2. Is |λ-1| smaller ON the critical line than off it? (SELF-ADJOINT EVIDENCE)
3. Does |λ-1| → 0 as B → ∞ at zeta zeros? (CONVERGENCE EVIDENCE)

If all three hold, we have numerical support for the Zeta Link.
""")


if __name__ == "__main__":
    main()
