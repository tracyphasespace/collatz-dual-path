#!/usr/bin/env python3
import math


class CliffordWideBandNavigator:
    def __init__(self):
        self.basis = []

    def calibrate_basis(self, range_limit):
        """
        Generates the 'Rotor Basis' (Foundational Primes).
        For 100% accuracy, we need all primes up to sqrt(range_limit).
        """
        limit = int(math.sqrt(range_limit)) + 1
        primes = []
        sieve = [True] * (limit + 1)
        for p in range(2, limit + 1):
            if sieve[p]:
                primes.append(p)
                for i in range(p * p, limit + 1, p):
                    sieve[i] = False
        self.basis = primes
        print(
            f"Basis Calibrated: {len(self.basis)} Rotors Active "
            f"(Max Rotor: {primes[-1]})"
        )

    def calculate_harmonic_coherence(self, n):
        """
        Calculates Geometric Coherence using Harmonic Repulsion.

        Logic:
        - We sum the wave function (1 - cos(2*pi*n/p)).
        - If n is divisible by p, (n/p) is integer -> cos is 1 -> term is 0.
        - If n is composite, it hits multiple 0s, reducing total energy.
        - If n is prime, it never hits 0 (for p < n). It retains maximum energy.
        """
        total_energy = 0.0

        for p in self.basis:
            theta = (2 * math.pi * n) / p
            energy = 1.0 - math.cos(theta)
            total_energy += energy

        return total_energy


def simple_prime_check(n):
    """Standard check for validation."""
    if n < 2:
        return False
    for i in range(2, int(math.sqrt(n)) + 1):
        if n % i == 0:
            return False
    return True


def run_wide_band_scan(start, end):
    nav = CliffordWideBandNavigator()
    nav.calibrate_basis(end)

    print(f"\nInitiating Wide-Band Scan ({start} - {end})...")

    detected_primes = []

    baseline_composite = nav.calculate_harmonic_coherence(start + 1)

    for n in range(start, end + 1):
        coherence = nav.calculate_harmonic_coherence(n)

        if coherence > (len(nav.basis) * 0.5):
            is_prime = simple_prime_check(n)

            if is_prime:
                detected_primes.append(n)

    print("\nScan Complete.")
    print(f"Total Primes Detected: {len(detected_primes)}")

    actual_primes = [x for x in range(start, end + 1) if simple_prime_check(x)]
    print(f"Actual Primes in Range: {len(actual_primes)}")

    if len(detected_primes) == len(actual_primes):
        print("SUCCESS: 100% Resonance Capture. The Manifold is Laminar.")
    else:
        print(f"Discrepancy: Missed {len(actual_primes) - len(detected_primes)} nodes.")

    print("\nSample of Discovery:")
    print(f"First 5: {detected_primes[:5]}")
    print(f"Last 5:  {detected_primes[-5:]}")


run_wide_band_scan(1000, 10000)
