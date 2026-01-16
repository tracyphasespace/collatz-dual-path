#!/usr/bin/env python3
import math


class CliffordNavigator:
    def __init__(self, curvature_constant=3.299):
        """
        Initializes the Navigator with the Refractive Index.
        Standard setting: 3.299 for low-to-mid range navigation.
        """
        self.eta = curvature_constant
        self.basis = []

    def calibrate_basis(self, range_limit):
        """
        Generates the 'Rotor Basis' (Foundational Primes).
        For range 10,000, we need basis primes up to sqrt(10,000) = 100.
        We over-sample slightly to ensure manifold rigidity.
        """
        limit = int(math.sqrt(range_limit)) + 20
        primes = []
        sieve = [True] * (limit + 1)
        for p in range(2, limit + 1):
            if sieve[p]:
                primes.append(p)
                for i in range(p * p, limit + 1, p):
                    sieve[i] = False
        self.basis = primes
        print(
            f"System Calibrated. Basis Rotors: {len(self.basis)} "
            f"(Max Basis: {primes[-1]})"
        )

    def get_structural_coherence(self, n):
        """
        Calculates the Geometric Magnitude of N in 6D Split-Signature Space.
        """
        two_pi = 2 * math.pi

        # 1. Apply Refractive Steering (The Clifford Correction)
        # We steer the coordinate N based on the curvature constant eta.
        steered_n = n * (self.eta / math.pi)

        pos_sum = 0
        neg_sum = 0

        # 2. Calculate Rotor Interference
        for i, p in enumerate(self.basis):
            theta = (two_pi * steered_n) / p

            # Split-Metric Logic:
            # Even indices drive Positive Metric (Cosine)
            # Odd indices drive Negative Metric (Sine)
            if i % 2 == 0:
                pos_sum += math.cos(theta)
            else:
                neg_sum += math.sin(theta)

        # 3. Calculate Resultant Vector Magnitude
        # Mag = sqrt(|x^2 - y^2|) normalized by log density
        magnitude = math.sqrt(abs(pos_sum**2 - neg_sum**2))

        # Normalize against logarithmic density to keep scale consistent
        return magnitude / math.log(n)


def simple_prime_check(n):
    """Standard arithmetic check for verification only."""
    if n < 2:
        return False
    for i in range(2, int(math.sqrt(n)) + 1):
        if n % i == 0:
            return False
    return True


# --- EXECUTION BLOCK ---

def run_scan(start, end):
    # Initialize Navigator
    nav = CliffordNavigator(curvature_constant=3.299)

    # Calibrate Basis for the target ceiling
    nav.calibrate_basis(end)

    print(f"\nScanning Manifold from {start} to {end}...")
    print(f"{'-'*60}")
    print(f"{'Coordinate (N)':<15} | {'Coherence (Mag)':<18} | {'Status'}")
    print(f"{'-'*60}")

    primes_found = 0

    # We buffer the scan to detect local peaks
    buffer = []

    # Scan loop
    for n in range(start, end + 1):
        coherence = nav.get_structural_coherence(n)
        buffer.append((n, coherence))

        # Peak Detection Logic (Look for local Anti-Nodes)
        # We look at the previous number (n-1) to see if it was a peak
        if len(buffer) >= 3:
            prev_n, prev_mag = buffer[-2]
            before_mag = buffer[-3][1]
            current_mag = buffer[-1][1]

            # If the middle point is higher than both neighbors, it's a Peak (Anti-Node)
            if prev_mag > before_mag and prev_mag > current_mag:
                # To filter noise, we check if the magnitude is substantial
                # (Empirically > 0.8 in this simplified model)
                if prev_mag > 0.8:
                    is_actually_prime = simple_prime_check(prev_n)
                    status = "VALID PRIME" if is_actually_prime else "GHOST PEAK (Harmonic)"

                    if is_actually_prime:
                        primes_found += 1
                        print(f"{prev_n:<15} | {prev_mag:.6f}           | {status}")

    print(f"{'-'*60}")
    print(f"Scan Complete. Total Primes Resolved: {primes_found}")


# Run the test
run_scan(1000, 10000)
