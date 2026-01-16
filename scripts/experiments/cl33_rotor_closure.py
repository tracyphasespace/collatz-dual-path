"""
Cl(3,3) Rotor Closure Test

Tests whether weighted rotor sums converge at σ = 1/2 but diverge elsewhere.

Key hypothesis: Large primes "close" onto the critical line because:
- At σ = 1/2: rotors are unitary, contributions decay and stabilize
- At σ ≠ 1/2: rotors have scaling, causing growth or collapse

Usage:
    pip install clifford numpy sympy matplotlib
    python cl33_rotor_closure.py
"""

import numpy as np
from sympy import primerange, log as sym_log
import matplotlib.pyplot as plt

try:
    from clifford import Cl
    HAS_CLIFFORD = True
except ImportError:
    HAS_CLIFFORD = False
    print("Warning: clifford package not installed. Using simplified 2x2 model.")


# ============================================================
# SIMPLIFIED 2x2 MODEL (fallback if clifford not available)
# ============================================================

def rotor_2x2(p, t):
    """Simple 2x2 rotation matrix for prime p at parameter t."""
    theta = t * np.log(p)
    return np.array([
        [np.cos(theta), -np.sin(theta)],
        [np.sin(theta), np.cos(theta)]
    ])


def weighted_rotor_sum_2x2(maxP, sigma, t):
    """Weighted sum of 2x2 rotors."""
    primes = list(primerange(2, maxP + 1))
    total = np.zeros((2, 2))

    for p in primes:
        weight = np.log(p) * (p ** (-sigma))
        R = rotor_2x2(p, t)
        total += float(weight) * R

    return total


def closure_norm_2x2(maxP, sigma, t):
    """Frobenius norm of weighted rotor sum."""
    R = weighted_rotor_sum_2x2(maxP, sigma, t)
    return np.sqrt(np.sum(R**2))


# ============================================================
# Cl(3,3) MODEL (requires clifford package)
# ============================================================

if HAS_CLIFFORD:
    # Setup Cl(3,3) with signature (+,+,+,-,-,-)
    layout, blades = Cl(3, 3, firstIdx=1)
    e = blades

    def bivector_for_prime(p):
        """Assign a bivector plane to each prime (cyclic pattern)."""
        i = (p % 3) + 1
        j = (p % 3) + 4
        return e[i] ^ e[j]

    def rotor_cl33(p, t):
        """Clifford rotor: exp(B * theta) = cos(theta) + B*sin(theta)."""
        theta = t * np.log(p)
        B = bivector_for_prime(p)
        return np.cos(theta) + B * np.sin(theta)

    def weighted_rotor_sum_cl33(maxP, sigma, t):
        """Weighted sum of Cl(3,3) rotors."""
        primes = list(primerange(2, maxP + 1))
        total = layout.MultiVector()

        for p in primes:
            weight = float(sym_log(p)) * (p ** (-sigma))
            R = rotor_cl33(p, t)
            total += weight * R

        return total

    def closure_norm_cl33(maxP, sigma, t):
        """Scalar norm of Cl(3,3) rotor sum."""
        R = weighted_rotor_sum_cl33(maxP, sigma, t)
        # Inner product gives scalar
        inner = R | R
        scalar_part = inner[()]  # Extract scalar component
        return np.sqrt(abs(scalar_part))


# ============================================================
# MAIN TESTS
# ============================================================

def test_sigma_sweep(maxP=1000, t=14.1347):
    """Test closure norm at different sigma values."""
    print(f"\n=== SIGMA SWEEP (maxP={maxP}, t={t}) ===")

    sigmas = [0.3, 0.4, 0.5, 0.6, 0.7]

    if HAS_CLIFFORD:
        print("Using Cl(3,3) model")
        closure_fn = closure_norm_cl33
    else:
        print("Using 2x2 model")
        closure_fn = closure_norm_2x2

    results = []
    for sigma in sigmas:
        norm = closure_fn(maxP, sigma, t)
        results.append((sigma, norm))
        print(f"  σ = {sigma}: norm = {norm:.6f}")

    return results


def test_prime_convergence(sigma=0.5, t=14.1347):
    """Test how norm changes as maxP increases."""
    print(f"\n=== PRIME CONVERGENCE (σ={sigma}, t={t}) ===")

    maxPs = [50, 100, 200, 500, 1000, 2000, 5000]

    if HAS_CLIFFORD:
        closure_fn = closure_norm_cl33
    else:
        closure_fn = closure_norm_2x2

    results = []
    for maxP in maxPs:
        norm = closure_fn(maxP, sigma, t)
        results.append((maxP, norm))
        print(f"  maxP = {maxP}: norm = {norm:.6f}")

    return results


def test_zero_comparison(maxP=1000, sigma=0.5):
    """Compare closure norm at zeta zeros vs non-zeros."""
    print(f"\n=== ZERO COMPARISON (maxP={maxP}, σ={sigma}) ===")

    zeros = [14.1347, 21.0220, 25.0109, 30.4249, 32.9351]
    non_zeros = [10.0, 15.0, 20.0, 26.0, 35.0]

    if HAS_CLIFFORD:
        closure_fn = closure_norm_cl33
    else:
        closure_fn = closure_norm_2x2

    print("At zeta zeros:")
    for t in zeros:
        norm = closure_fn(maxP, sigma, t)
        print(f"  t = {t}: norm = {norm:.6f}")

    print("At non-zeros:")
    for t in non_zeros:
        norm = closure_fn(maxP, sigma, t)
        print(f"  t = {t}: norm = {norm:.6f}")


def plot_sigma_comparison(maxP=1000, t=14.1347):
    """Plot closure norm vs sigma."""
    sigmas = np.linspace(0.2, 0.8, 50)

    if HAS_CLIFFORD:
        closure_fn = closure_norm_cl33
    else:
        closure_fn = closure_norm_2x2

    norms = [closure_fn(maxP, s, t) for s in sigmas]

    plt.figure(figsize=(10, 6))
    plt.plot(sigmas, norms, 'b-', linewidth=2)
    plt.axvline(x=0.5, color='r', linestyle='--', label='σ = 1/2')
    plt.xlabel('σ')
    plt.ylabel('Closure Norm ||K(t)||')
    plt.title(f'Rotor Closure Norm vs σ (maxP={maxP}, t={t})')
    plt.legend()
    plt.grid(True)
    plt.savefig('closure_vs_sigma.png', dpi=150)
    plt.show()


def plot_convergence_comparison(t=14.1347):
    """Plot convergence at different sigma values."""
    maxPs = [50, 100, 200, 500, 1000, 2000]
    sigmas = [0.4, 0.5, 0.6]

    if HAS_CLIFFORD:
        closure_fn = closure_norm_cl33
    else:
        closure_fn = closure_norm_2x2

    plt.figure(figsize=(10, 6))

    for sigma in sigmas:
        norms = [closure_fn(maxP, sigma, t) for maxP in maxPs]
        plt.plot(maxPs, norms, 'o-', label=f'σ = {sigma}')

    plt.xlabel('maxP (number of primes)')
    plt.ylabel('Closure Norm ||K(t)||')
    plt.title(f'Convergence of Rotor Sum (t={t})')
    plt.legend()
    plt.grid(True)
    plt.xscale('log')
    plt.savefig('convergence_by_sigma.png', dpi=150)
    plt.show()


# ============================================================
# RUN TESTS
# ============================================================

if __name__ == "__main__":
    print("=" * 60)
    print("Cl(3,3) ROTOR CLOSURE TEST")
    print("=" * 60)

    # Test 1: Sigma sweep
    test_sigma_sweep(maxP=500, t=14.1347)

    # Test 2: Prime convergence
    test_prime_convergence(sigma=0.5, t=14.1347)

    # Test 3: Zero comparison
    test_zero_comparison(maxP=500, sigma=0.5)

    print("\n" + "=" * 60)
    print("Tests complete. Run plot_* functions for visualization.")
    print("=" * 60)
