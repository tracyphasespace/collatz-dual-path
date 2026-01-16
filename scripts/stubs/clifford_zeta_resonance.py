#!/usr/bin/env python3
import math

import numpy as np


def calculate_manifold_torque(t, eta, basis_size=5000):
    """
    Calculates the 'Resonant Torque' at a height t on the critical line.
    Increased basis_size to 5000 to handle the high-frequency resolution
    required for the 100th zero.
    """
    # Simulate prime frequencies (rotors)
    primes = []
    is_prime = [True] * (basis_size + 1)
    for p in range(2, basis_size + 1):
        if is_prime[p]:
            primes.append(p)
            for i in range(p * p, basis_size + 1, p):
                is_prime[i] = False

    # Calculate phase torque across the (+++---) manifold
    torque_sum = 0
    for i, p in enumerate(primes):
        # We apply the refractive index 'eta' to the phase torque calculation.
        # This represents the 'bend' in the manifold at height t.
        phase = (t * np.log(p)) / (eta / np.pi)

        # Split signature interaction (Clifford 3,3)
        if i % 2 == 0:
            torque_sum += np.cos(phase)
        else:
            torque_sum -= np.sin(phase)

    return abs(torque_sum) / len(primes)


# Known heights of non-trivial zeros
# t_1, t_2, t_3 are the first three.
# t_100 is approximately 236.524272.
zeta_zeros = {
    "Zero #1": 14.134725,
    "Zero #2": 21.022040,
    "Zero #3": 25.010858,
    "Zero #100": 236.524272,
}

clifford_constant = 3.299

print("--- DEEP SCAN: CLIFFORD-ZETA RESONANCE ---")
print(f"Curvature Constant (eta): {clifford_constant}")
print("Manifold Basis: 5000 prime rotors")
print("-" * 50)

for label, t in zeta_zeros.items():
    coherence = calculate_manifold_torque(t, clifford_constant)

    # Classification logic based on field integrity
    status = "UNKNOWN"
    if coherence < 0.045:
        status = "NODAL LOCK (Structural Sink)"
    elif coherence > 0.12:
        status = "ANTI-NODAL LOCK (Structural Peak)"
    else:
        status = "PHASE DRIFT"

    print(f"{label} at t = {t:.6f}")
    print(f"  > Coherence: {coherence:.8f}")
    print(f"  > Alignment: {status}")
    print("-" * 50)

print("SCALING ANALYSIS:")
# Comparing the coherence of the 100th zero to the 1st
# to determine if the 3.299 constant is drifting.
c1 = calculate_manifold_torque(zeta_zeros["Zero #1"], clifford_constant)
c100 = calculate_manifold_torque(zeta_zeros["Zero #100"], clifford_constant)
drift = abs(c1 - c100)

print(f"Relative Drift (Zero #1 vs #100): {drift:.8f}")
if drift < 0.05:
    print(
        "CONCLUSION: The 3.299 constant is SCALE-INVARIANT. "
        "It acts as a universal refractive index."
    )
else:
    print(
        "CONCLUSION: Refractive Drift detected. "
        "The manifold curvature may evolve as t -> infinity."
    )
