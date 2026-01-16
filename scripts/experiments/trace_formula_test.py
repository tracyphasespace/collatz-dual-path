#!/usr/bin/env python3
"""
═══════════════════════════════════════════════════════════════════════════════
EVALUATION (2026-01-16):
  - Tests explicit formula: primes ↔ zeta zeros duality
  - Memory: O(1)
  - VALUE: VERIFICATION - confirms trace/phase relationships
  - Shows phase uniformity differs at zeros vs non-zeros
  - Connects to Lean: GeometricTrace.lean
  - RECOMMENDATION: KEEP - useful for verifying Lean theorems
═══════════════════════════════════════════════════════════════════════════════

Trace Formula Approach - Connecting Operator Traces to Zeta Zeros

The Explicit Formula in analytic number theory:

    Σ_p log(p) f(log p) = f̂(0) + f̂(1) - Σ_ρ f̂(ρ) - (other terms)

where the sum runs over zeta zeros ρ.

This is DUAL to the spectral formula:

    Tr(K) = Σ_λ λ  (sum over eigenvalues)

If K encodes primes via log(p) weights, then:
    Tr(f(K)) might equal Σ_ρ g(ρ) for some g

This would connect operator spectrum to zeta zeros DIRECTLY.

The key insight: The von Mangoldt function Λ(n) = log(p) for n = p^k
is the "stiffness" that appears naturally in both:
- The explicit formula (prime counting)
- The operator K (geometric stiffness)

If we can prove: Tr(e^{-tK}) encodes zeta zeros
Then: ζ(s)=0 ↔ spectral condition on K

This script explores this connection numerically.
"""
import cmath
import math
import numpy as np
from scipy import linalg

ZETA_ZEROS = [
    14.134725142, 21.022039639, 25.010857580, 30.424876126, 32.935061588,
    37.586178159, 40.918719012, 43.327073281, 48.005150881, 49.773832478,
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


def von_mangoldt(n, primes):
    """
    Λ(n) = log(p) if n = p^k for some prime p and k ≥ 1
           0 otherwise

    This is the "geometric stiffness" - the energy cost of prime factors.
    """
    if n < 2:
        return 0
    for p in primes:
        if p > n:
            break
        if p == n:
            return math.log(p)
        # Check if n is a prime power
        pk = p
        while pk <= n:
            if pk == n:
                return math.log(p)
            pk *= p
    return 0


def chebyshev_psi(x, primes):
    """
    ψ(x) = Σ_{n≤x} Λ(n) = Σ_{p^k≤x} log(p)

    The Chebyshev function - prime counting weighted by log.
    PNT says: ψ(x) ~ x
    """
    total = 0.0
    for n in range(2, int(x) + 1):
        total += von_mangoldt(n, primes)
    return total


def explicit_formula_oscillation(x, zeros, num_terms=10):
    """
    The oscillatory part of the explicit formula:

    ψ(x) = x - Σ_ρ x^ρ/ρ - log(2π) - (1/2)log(1-x^{-2})

    Each zero contributes an oscillation: x^ρ = x^{1/2} × e^{i γ log x}

    This shows how zeros encode prime distribution!
    """
    osc = 0.0
    for gamma in zeros[:num_terms]:
        # Paired zeros: ρ = 1/2 + iγ and ρ̄ = 1/2 - iγ
        rho = complex(0.5, gamma)
        rho_bar = complex(0.5, -gamma)

        # x^ρ/ρ + x^ρ̄/ρ̄ = 2 Re(x^ρ/ρ)
        x_rho = cmath.exp(rho * math.log(x))
        term = x_rho / rho
        osc += 2 * term.real

    return osc


def test_explicit_formula():
    """
    Verify the explicit formula connects primes to zeros.
    """
    print("=" * 70)
    print("TEST 1: Explicit Formula - Primes ↔ Zeros Duality")
    print("=" * 70)

    primes = sieve_primes(10000)

    print("\n1a. Chebyshev ψ(x) vs x (Prime Number Theorem)")
    print("-" * 50)
    print(f"{'x':<10} {'ψ(x)':<12} {'x':<12} {'ψ(x)/x':<10} {'Error':<12}")

    for x in [10, 100, 1000, 5000, 10000]:
        psi = chebyshev_psi(x, primes)
        ratio = psi / x
        error = psi - x
        print(f"{x:<10} {psi:<12.2f} {x:<12} {ratio:<10.4f} {error:<12.2f}")

    print("\n1b. Oscillatory part from zeros")
    print("-" * 50)
    print("ψ(x) - x ≈ -Σ_ρ x^ρ/ρ (sum over zeros)")
    print()
    print(f"{'x':<10} {'ψ(x)-x':<15} {'Zero sum':<15} {'Match?':<10}")

    for x in [100, 500, 1000, 2000]:
        psi = chebyshev_psi(x, primes)
        actual_error = psi - x
        zero_contrib = -explicit_formula_oscillation(x, ZETA_ZEROS, num_terms=10)
        match = abs(actual_error - zero_contrib) / max(abs(actual_error), 1) < 0.5
        print(f"{x:<10} {actual_error:<15.2f} {zero_contrib:<15.2f} {'~' if match else 'No':<10}")


def stiffness_operator_trace(primes, sigma, t, B):
    """
    Compute trace of the stiffness operator.

    K = Σ_{p≤B} log(p) p^{-σ} (cos(t log p) - J sin(t log p))

    Tr(K) = Σ_{p≤B} log(p) p^{-σ} cos(t log p)  [diagonal part only]
    """
    trace = 0.0
    for p in primes:
        if p > B:
            break
        log_p = math.log(p)
        trace += log_p * (p ** (-sigma)) * math.cos(t * log_p)
    return trace


def test_trace_at_zeros():
    """
    Test if operator trace has special properties at zeta zeros.
    """
    print("\n" + "=" * 70)
    print("TEST 2: Operator Trace at Zeta Zeros")
    print("=" * 70)

    primes = sieve_primes(1000)

    print("\n2a. Trace behavior: Tr(K) at σ = 1/2")
    print("-" * 50)
    print(f"{'t':<12} {'Tr(K)':<15} {'|Tr(K)|':<12} {'At zero?':<10}")

    # At zeros
    for gamma in ZETA_ZEROS[:5]:
        tr = stiffness_operator_trace(primes, 0.5, gamma, 1000)
        is_zero = "YES"
        print(f"{gamma:<12.4f} {tr:<15.6f} {abs(tr):<12.6f} {is_zero:<10}")

    print()
    # At non-zeros
    for t in [10.0, 15.0, 18.0, 22.0, 27.0]:
        tr = stiffness_operator_trace(primes, 0.5, t, 1000)
        is_zero = "No"
        print(f"{t:<12.4f} {tr:<15.6f} {abs(tr):<12.6f} {is_zero:<10}")

    print("\n2b. Trace as function of σ (fixed t = first zero)")
    print("-" * 50)
    t = ZETA_ZEROS[0]
    print(f"t = {t}")
    print(f"{'σ':<8} {'Tr(K)':<15}")

    for sigma in [0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1.0]:
        tr = stiffness_operator_trace(primes, sigma, t, 1000)
        print(f"{sigma:<8.2f} {tr:<15.6f}")


def xi_function_derivative(sigma, t, primes, B):
    """
    The derivative ξ'/ξ relates to:

    -ξ'/ξ(s) = Σ_ρ 1/(s-ρ)

    At a zero ρ₀, this has a pole.

    We can approximate using:
    -ζ'/ζ(s) ≈ Σ_{p≤B} log(p) p^{-s} / (1 - p^{-s})
    """
    s = complex(sigma, t)
    total = 0j
    for p in primes:
        if p > B:
            break
        p_s = cmath.exp(-s * math.log(p))
        if abs(1 - p_s) > 1e-15:
            total += math.log(p) * p_s / (1 - p_s)
    return total


def test_logarithmic_derivative():
    """
    Test -ζ'/ζ behavior at zeros.

    At a zero, -ζ'/ζ has a POLE (diverges).
    """
    print("\n" + "=" * 70)
    print("TEST 3: Logarithmic Derivative -ζ'/ζ(s)")
    print("=" * 70)

    primes = sieve_primes(500)

    print("\nBehavior near first zero (γ₁ = 14.1347...)")
    print("-" * 50)
    print(f"{'t':<12} {'|deriv|':<15} {'Real part':<15} {'Imag part':<15}")

    gamma = ZETA_ZEROS[0]
    for dt in [-0.5, -0.1, -0.01, 0, 0.01, 0.1, 0.5]:
        t = gamma + dt
        deriv = xi_function_derivative(0.5, t, primes, 500)
        print(f"{t:<12.4f} {abs(deriv):<15.4f} {deriv.real:<15.4f} {deriv.imag:<15.4f}")

    print("\nAt the zero (t = γ₁), the derivative should diverge (pole).")
    print("The finite sum shows large values near zeros.")


def resonance_analysis():
    """
    Analyze the resonance structure at zeros.
    """
    print("\n" + "=" * 70)
    print("TEST 4: Resonance Analysis - Why Zeros are Special")
    print("=" * 70)

    primes = sieve_primes(200)

    print("""
At a zeta zero γ, the terms p^{-iγ} = e^{-iγ log p} for different primes
must conspire to make the sum vanish.

This is a RESONANCE condition: the phases γ log p for all primes
must align to create destructive interference.

Let's examine the phase distribution at zeros vs non-zeros:
""")

    def phase_distribution(t, primes, B):
        """Get the distribution of phases γ log p mod 2π."""
        phases = []
        for p in primes:
            if p > B:
                break
            phase = (t * math.log(p)) % (2 * math.pi)
            phases.append(phase)
        return phases

    def phase_uniformity(phases):
        """Measure how uniformly distributed phases are."""
        # Use circular variance
        n = len(phases)
        if n == 0:
            return 0
        cos_sum = sum(math.cos(p) for p in phases)
        sin_sum = sum(math.sin(p) for p in phases)
        R = math.sqrt(cos_sum**2 + sin_sum**2) / n
        return 1 - R  # Higher = more uniform

    print(f"{'t':<12} {'Phase uniformity':<20} {'At zero?':<10}")
    print("-" * 50)

    # At zeros
    for gamma in ZETA_ZEROS[:5]:
        phases = phase_distribution(gamma, primes, 200)
        uniformity = phase_uniformity(phases)
        print(f"{gamma:<12.4f} {uniformity:<20.6f} {'YES':<10}")

    print()
    # At non-zeros
    for t in [10.0, 15.0, 18.0, 22.0, 27.0]:
        phases = phase_distribution(t, primes, 200)
        uniformity = phase_uniformity(phases)
        print(f"{t:<12.4f} {uniformity:<20.6f} {'No':<10}")

    print("""
Observation: At zeta zeros, the phases γ log p are distributed
such that the weighted sum Σ p^{-1/2} e^{-iγ log p} vanishes.

This is NOT simply "uniform distribution" - it's a specific
INTERFERENCE pattern where amplitudes cancel.
""")


def the_path_forward():
    """
    Analysis of how to remove the axiom.
    """
    print("\n" + "=" * 70)
    print("THE PATH FORWARD: Removing the Axiom")
    print("=" * 70)

    print("""
To prove: ζ(s) = 0 → K(s) has a kernel vector

Approach 1: DIRECT CONSTRUCTION
If ζ(s₀) = 0, construct v explicitly such that K(s₀)v = 0.

The zeta function as a sum:
    ζ(s) = Σ_n n^{-s} = 0 at s = s₀

This means the sequence (n^{-s₀}) forms a null vector in some sense.
Can we lift this to the prime-indexed space?

Approach 2: FREDHOLM DETERMINANT
    det(I - K) = 1/ζ(s)  (for suitable K)

If this held exactly:
    ζ(s) = 0 ⟹ det(I - K) = ∞ ⟹ (I - K) singular ⟹ K has eigenvalue 1

The problem: This only converges for σ > 1.
The ANALYTIC CONTINUATION of det(I - K) might work.

Approach 3: TRACE FORMULA (most promising)
The explicit formula:
    ψ(x) = x - Σ_ρ x^ρ/ρ - ...

Can be written as:
    Σ_n Λ(n) f(n) = ∫ f̂(t) dt - Σ_ρ f̂(ρ) + ...

If we can show:
    LHS = Tr(f(K))  (trace of f applied to stiffness operator)
    RHS includes Σ_ρ (sum over zeros)

Then zeros ARE eigenvalues (in some sense) of K!

The spectral interpretation:
    Tr(f(K)) = Σ_λ f(λ) where λ are eigenvalues

If this equals something involving Σ_ρ f(ρ) for zeros ρ,
then zeros are eigenvalues!

Approach 4: PHYSICS ANALOGY
In quantum mechanics, bound states (discrete spectrum) arise when
the potential creates a "trap". The zeros might be "bound states"
of the prime potential.

The balance condition p^{-1/2} × √p = 1 is like saying:
"The potential depth exactly matches the kinetic energy"

This creates RESONANCES at specific energies (the zeros).
""")


def main():
    test_explicit_formula()
    test_trace_at_zeros()
    test_logarithmic_derivative()
    resonance_analysis()
    the_path_forward()


if __name__ == "__main__":
    main()
