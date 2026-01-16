"""
Cl(3,3) Rotor Closure Test using Kingdon

Tests whether weighted rotor sums converge at σ = 1/2 but diverge elsewhere.
"""

import numpy as np
from sympy import primerange
from kingdon import Algebra

# Setup Cl(3,3): 3 positive, 3 negative dimensions
alg = Algebra(p=3, q=3)

# Get basis vectors e1, e2, e3 (positive), e4, e5, e6 (negative)
e1, e2, e3, e4, e5, e6 = [alg.vector(name=f"e{i}") for i in range(1, 7)]

# Actually, let's use the frame directly
frame = alg.frame
print(f"Algebra: Cl(3,3)")
print(f"Dimension: {len(alg)}")
print(f"Frame: {frame}")

# Create bivectors for primes (cyclic assignment to different planes)
# IMPORTANT: Use same-signature bivectors that square to -1 for circular rotors
# Mixed-signature bivectors (e1^e4, etc.) square to +1 and give hyperbolic rotors!
bivector_planes = [
    frame[0] ^ frame[1],  # e1^e2, B^2 = -1 (positive-positive)
    frame[0] ^ frame[2],  # e1^e3, B^2 = -1
    frame[1] ^ frame[2],  # e2^e3, B^2 = -1
    frame[3] ^ frame[4],  # e4^e5, B^2 = -1 (negative-negative)
    frame[3] ^ frame[5],  # e4^e6, B^2 = -1
    frame[4] ^ frame[5],  # e5^e6, B^2 = -1
]

def bivector_for_prime(p):
    """Assign a bivector plane to each prime (cyclic through 6 planes)."""
    return bivector_planes[p % 6]

# Test bivector
B2 = bivector_for_prime(2)
print(f"\nBivector for prime 2: {B2}")
print(f"B2 squared: {B2 * B2}")

# Rotor: exp(B * theta) = cos(theta) + B * sin(theta)
def rotor(p, t):
    """Clifford rotor for prime p at parameter t."""
    theta = t * np.log(p)
    B = bivector_for_prime(p)
    return float(np.cos(theta)) + B * float(np.sin(theta))

# Test rotor
R2 = rotor(2, 1.0)
print(f"\nRotor for prime 2 at t=1: {R2}")

# Weighted rotor sum
def weighted_rotor_sum(maxP, sigma, t):
    """Compute weighted sum of rotors."""
    primes = list(primerange(2, maxP + 1))

    # Start with scalar 0 (kingdon requires values= keyword)
    total = alg.scalar(values=[0.0])

    for p in primes:
        weight = np.log(p) * (p ** (-sigma))
        R = rotor(p, t)
        total = total + weight * R

    return total

# Closure norm (magnitude of multivector)
def closure_norm(maxP, sigma, t):
    """Compute norm of weighted rotor sum."""
    K = weighted_rotor_sum(maxP, sigma, t)
    # Use the reverse to compute |K|^2 = K * ~K (scalar part)
    K_rev = ~K  # reverse
    product = K * K_rev
    # Extract scalar part using kingdon's values() method
    scalar_part = product.values()[0] if product.values() else 0.0
    return np.sqrt(abs(scalar_part))

# ============================================================
# TESTS
# ============================================================

print("\n" + "="*60)
print("SIGMA SWEEP (maxP=500, t=14.1347)")
print("="*60)

for sigma in [0.3, 0.4, 0.5, 0.6, 0.7]:
    try:
        norm = closure_norm(500, sigma, 14.1347)
        print(f"σ = {sigma}: norm = {norm:.6f}")
    except Exception as e:
        print(f"σ = {sigma}: ERROR - {e}")

print("\n" + "="*60)
print("PRIME CONVERGENCE (σ=0.5, t=14.1347)")
print("="*60)

for maxP in [50, 100, 200, 500, 1000]:
    try:
        norm = closure_norm(maxP, 0.5, 14.1347)
        print(f"maxP = {maxP}: norm = {norm:.6f}")
    except Exception as e:
        print(f"maxP = {maxP}: ERROR - {e}")

print("\n" + "="*60)
print("ZERO COMPARISON (maxP=500, σ=0.5)")
print("="*60)

print("At zeta zeros:")
for t in [14.1347, 21.022, 25.0109, 30.4249, 32.9351]:
    try:
        norm = closure_norm(500, 0.5, t)
        print(f"  t = {t}: norm = {norm:.6f}")
    except Exception as e:
        print(f"  t = {t}: ERROR - {e}")

print("\nAt non-zeros:")
for t in [10.0, 15.0, 20.0, 26.0, 35.0]:
    try:
        norm = closure_norm(500, 0.5, t)
        print(f"  t = {t}: norm = {norm:.6f}")
    except Exception as e:
        print(f"  t = {t}: ERROR - {e}")

print("\n" + "="*60)
print("Tests complete.")
print("="*60)
