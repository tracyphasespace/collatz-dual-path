#!/usr/bin/env python3
"""
═══════════════════════════════════════════════════════════════════════════════
EVALUATION (2026-01-16):
  - Tests Fredholm determinant connection: ζ(s) = det(I-K)^{-1}
  - Memory: O(1) for most tests
  - VALUE: VERIFICATION - confirms theoretical relationships hold numerically
  - Connects to Lean: Axioms.lean `zero_implies_kernel`
  - RECOMMENDATION: KEEP - useful for verifying Lean theorems
═══════════════════════════════════════════════════════════════════════════════

Fredholm Determinant Test - Connecting Zeta to Operator Spectrum

The key insight from the paper and Lean formalization:

    ζ(s) = det(I - K(s))^{-1}  (Euler product as Fredholm determinant)

This means:
    ζ(s) = 0  ⟺  det(I - K(s)) = ∞  ⟺  1 is eigenvalue of K(s)

The operator K(s) acts on prime-indexed space:
    K(s) = Σ_p K_p(s)

where each prime contributes:
    K_p(s) e_p = p^{-σ} [cos(t log p) e_p - sin(t log p) J_p(e_p)]

In our simplified model (diagonal in prime basis):
    K(s) = diag(p^{-s}) for primes p

The Fredholm determinant is:
    det(I - K) = Π_p (1 - p^{-s})

This equals 1/ζ(s) when σ > 1!

So:
    ζ(s) = 0  ⟺  det = 0  ⟺  some (1 - p^{-s}) = 0  ⟺  p^{-s} = 1

But p^{-s} = 1 means s = 0 (only solution), which is outside critical strip.

THE GAP: The naive Fredholm picture doesn't directly explain zeros in 0 < σ < 1.
The zeros come from ANALYTIC CONTINUATION of both ζ and det.

This script tests alternative formulations.
"""
import cmath
import math

ZETA_ZEROS = [
    14.134725142, 21.022039639, 25.010857580, 30.424876126, 32.935061588,
]

def sieve_primes(limit):
    if limit < 2:
        return []
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, int(limit**0.5) + 1):
        if sieve[p]:
            sieve[p*p:limit+1:p] = b"\x00" * ((limit - p*p) // p + 1)
    return [i for i, is_p in enumerate(sieve) if is_p]


def euler_product(s, primes):
    """
    Compute Euler product: Π_p (1 - p^{-s})^{-1}

    For σ > 1, this equals ζ(s).
    """
    product = 1.0 + 0j
    for p in primes:
        term = 1 - cmath.exp(-s * math.log(p))  # 1 - p^{-s}
        if abs(term) > 1e-15:
            product *= 1 / term
    return product


def fredholm_determinant(s, primes):
    """
    Compute Fredholm determinant: det(I - K) = Π_p (1 - p^{-s})

    This equals 1/ζ(s) for σ > 1.
    """
    det = 1.0 + 0j
    for p in primes:
        det *= 1 - cmath.exp(-s * math.log(p))
    return det


def rayleigh_form(sigma, t, primes):
    """
    Compute the Rayleigh-like quantity from the Lean formalization.

    The Lean code has: BivectorComponent = (σ - 1/2) × Q(v)

    At σ = 1/2, this is zero regardless of t.
    Away from 1/2, it's proportional to the "tension".

    We compute: Σ_p log(p) × p^{-σ} × sin(t log p)

    This is the "imaginary" part of -ζ'(s)/ζ(s).
    """
    total = 0.0
    for p in primes:
        log_p = math.log(p)
        amplitude = p ** (-sigma)
        phase = math.sin(t * log_p)
        total += log_p * amplitude * phase
    return total


def dirichlet_eta(s, N=1000):
    """
    Compute the Dirichlet eta function: η(s) = Σ (-1)^{n-1} n^{-s}

    This is related to ζ(s) by: η(s) = (1 - 2^{1-s}) ζ(s)

    The eta function converges for σ > 0, giving us access to the critical strip.
    """
    total = 0j
    for n in range(1, N + 1):
        sign = (-1) ** (n - 1)
        total += sign * cmath.exp(-s * math.log(n))
    return total


def zeta_from_eta(s, N=1000):
    """
    Compute ζ(s) from η(s) via: ζ(s) = η(s) / (1 - 2^{1-s})

    This works in the critical strip!
    """
    eta = dirichlet_eta(s, N)
    denominator = 1 - cmath.exp((1 - s) * math.log(2))
    if abs(denominator) < 1e-15:
        return complex(float('inf'), 0)
    return eta / denominator


def main():
    print("=" * 70)
    print("FREDHOLM DETERMINANT TEST")
    print("Connecting ζ(s) = det(I-K)^{-1} to operator spectrum")
    print("=" * 70)

    primes = sieve_primes(1000)

    # Test 1: Euler product vs zeta in convergent region
    print("\n1. EULER PRODUCT TEST (σ > 1)")
    print("-" * 50)

    for sigma in [1.5, 2.0, 3.0]:
        s = complex(sigma, 0)
        euler = euler_product(s, primes)
        zeta = zeta_from_eta(s, N=5000)
        print(f"σ={sigma}: Euler={euler.real:.6f}, ζ={zeta.real:.6f}, diff={abs(euler-zeta):.6f}")

    # Test 2: Fredholm determinant at various points
    print("\n2. FREDHOLM DETERMINANT det(I-K) = 1/ζ")
    print("-" * 50)

    for sigma in [1.5, 2.0]:
        s = complex(sigma, 0)
        det = fredholm_determinant(s, primes)
        zeta = zeta_from_eta(s, N=5000)
        product = det * zeta
        print(f"σ={sigma}: det={det.real:.6f}, ζ={zeta.real:.6f}, det×ζ={product.real:.6f} (should be 1)")

    # Test 3: Behavior at zeta zeros
    print("\n3. ZETA AT KNOWN ZEROS (critical line σ=1/2)")
    print("-" * 50)

    print(f"{'γ (zero)':<12} {'|ζ(1/2+iγ)|':<15} {'|det|':<15} {'Rayleigh form':<15}")
    for gamma in ZETA_ZEROS[:5]:
        s = complex(0.5, gamma)
        zeta = zeta_from_eta(s, N=10000)
        det = fredholm_determinant(s, primes[:100])  # Use fewer primes
        rayleigh = rayleigh_form(0.5, gamma, primes[:100])
        print(f"{gamma:<12.4f} {abs(zeta):<15.6f} {abs(det):<15.6f} {rayleigh:<15.6f}")

    # Test 4: Rayleigh form behavior
    print("\n4. RAYLEIGH FORM: (σ-1/2) × tension")
    print("-" * 50)
    print("At σ=1/2, should be ~0 regardless of t")
    print("Away from 1/2, should be non-zero")

    t = ZETA_ZEROS[0]  # Use first zero's imaginary part
    print(f"\nt = {t} (first zero)")
    print(f"{'σ':<8} {'Rayleigh':<15} {'σ-0.5':<10}")
    for sigma in [0.3, 0.4, 0.45, 0.5, 0.55, 0.6, 0.7]:
        rayleigh = rayleigh_form(sigma, t, primes[:100])
        print(f"{sigma:<8.2f} {rayleigh:<15.6f} {sigma-0.5:<10.2f}")

    # Test 5: The key insight - zeros force critical line
    print("\n5. WHY ZEROS FORCE σ = 1/2")
    print("-" * 50)
    print("""
The Lean proof structure:

1. AXIOM (zero_implies_kernel):
   ζ(s)=0 → ∃ v≠0: K(s)v = 0

2. PROVEN (Rayleigh):
   BivectorComponent(K,v) = (σ-1/2) × Q(v)

3. PROVEN (Positivity):
   Q(v) > 0 for v ≠ 0

4. PROVEN (Critical Line):
   K(s)v = 0 → BivectorComponent = 0 → σ-1/2 = 0 → σ = 1/2

THE GAP (the axiom): Why does ζ(s)=0 imply K has a kernel?

The Fredholm picture says: ζ = det(I-K)^{-1}
So ζ=0 means det=∞, meaning I-K singular, meaning K has eigenvalue 1.

But our K is: K = (σ-1/2) × Stiffness × J
This K is 0 when σ=1/2, so kernel exists trivially!

The deep question: How does ζ(s)=0 (analytic fact)
connect to K having kernel (operator fact)?
""")

    # Test 6: Look for structure at zeros
    print("\n6. STRUCTURE AT ZEROS: Phase alignment")
    print("-" * 50)

    print("At zeta zeros, the terms might show special phase alignment:")
    gamma = ZETA_ZEROS[0]
    s = complex(0.5, gamma)

    print(f"\nFirst zero: s = 0.5 + {gamma}i")
    print(f"{'prime p':<10} {'p^(-s)':<25} {'|p^(-s)|':<10} {'arg':<10}")

    for p in primes[:10]:
        term = cmath.exp(-s * math.log(p))
        print(f"{p:<10} {term.real:>+10.6f}{term.imag:>+10.6f}i {abs(term):<10.4f} {cmath.phase(term):<10.4f}")

    print(f"\nSum of first 100 terms (scalar/bivector):")
    scalar_sum = sum(p**(-0.5) * math.cos(gamma * math.log(p)) for p in primes[:100])
    bivector_sum = sum(p**(-0.5) * math.sin(gamma * math.log(p)) for p in primes[:100])
    print(f"  Scalar: {scalar_sum:.6f}")
    print(f"  Bivector: {bivector_sum:.6f}")


if __name__ == "__main__":
    main()
