#!/usr/bin/env python3
"""
═══════════════════════════════════════════════════════════════════════════════
EVALUATION (2026-01-16):
  - Visualizes phase angles and tension in prime space
  - Verifies balance condition: p^{-1/2} × √p = 1
  - Memory: O(1)
  - VALUE: PEDAGOGICAL - explains phase interpretation of primes
  - RECOMMENDATION: Archive - overlaps with outer_product_direction.py
═══════════════════════════════════════════════════════════════════════════════

Tension and Direction in Prime Space

The deep question: What does adding a prime dimension DO geometrically?

Key insight: It's not just "removal" - it's a PHASE ROTATION.

Each number n has a "phase" relative to prime p: θ_p(n) = 2π(n mod p)/p
- When θ = 0: n is divisible by p (resonance, removed)
- When θ ≠ 0: n survives this filter (out of phase)

Primes are numbers that are OUT OF PHASE with ALL smaller primes.
They're the "incommensurable" points - maximally avoiding all resonances.

The TENSION is the "pull" toward resonance.
The SURFACE is where tension balances (critical line).
"""
import math

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


def phase_angle(n, p):
    """
    The phase of n relative to prime p.
    θ = 2π(n mod p)/p

    θ = 0 means resonance (divisible)
    θ = π means maximally out of phase
    """
    return 2 * math.pi * (n % p) / p


def phase_vector(n, primes):
    """
    n's position as a vector of phases.
    Each coordinate is the phase relative to that prime.
    """
    return [phase_angle(n, p) for p in primes if p < n]


def total_phase_energy(n, primes):
    """
    The "energy" of n's position in phase space.

    High energy = far from all resonances = more "prime-like"
    Low energy = close to some resonance = composite

    E(n) = Σ (1 - cos(θ_p))

    This is exactly the resonance formula from our experiments!
    - cos(θ) = 1 when θ = 0 (divisible) → E contribution = 0
    - cos(θ) = -1 when θ = π (maximally out of phase) → E contribution = 2
    """
    energy = 0
    for p in primes:
        if p >= n:
            break
        if p * p > n:  # Only check up to sqrt(n)
            break
        theta = phase_angle(n, p)
        energy += 1 - math.cos(theta)
    return energy


def direction_vector(n, primes):
    """
    The "direction" that n is pulled by each prime.

    Each prime p exerts a "force" toward n being divisible by p.
    The force direction is toward the nearest multiple of p.

    This is like gravity in multiple dimensions.
    """
    forces = []
    for p in primes:
        if p >= n:
            break
        remainder = n % p
        # Distance to nearest multiple
        dist_down = remainder
        dist_up = p - remainder

        if dist_down <= dist_up:
            force = -dist_down  # Pull down toward previous multiple
        else:
            force = dist_up    # Pull up toward next multiple

        forces.append((p, force))
    return forces


def tension_magnitude(n, primes):
    """
    Total tension = sum of absolute forces.

    Primes have tension that's "balanced" in a special way.
    Composites have at least one zero-force (they're AT a multiple).
    """
    forces = direction_vector(n, primes)
    return sum(abs(f) for _, f in forces)


def analyze_tension():
    """
    Show how tension relates to primality.
    """
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23]

    print("=" * 80)
    print("TENSION AND DIRECTION ANALYSIS")
    print("=" * 80)

    print("\n1. PHASE ANGLES (θ_p = 2π(n mod p)/p)")
    print("-" * 60)
    print(f"{'n':>4} | ", end="")
    for p in primes[:5]:
        print(f"θ_{p:<2}   ", end="")
    print("| Prime? | Phase Energy")
    print("-" * 70)

    for n in range(2, 35):
        phases = []
        for p in primes[:5]:
            if p < n:
                theta = phase_angle(n, p)
                # Show as fraction of 2π
                frac = theta / (2 * math.pi)
                phases.append(f"{frac:5.2f}")
            else:
                phases.append("    -")

        energy = total_phase_energy(n, primes)
        is_p = "✓" if is_prime(n) else " "

        print(f"{n:4d} | {' '.join(phases)} |   {is_p}    | {energy:.3f}")


def analyze_direction():
    """
    Show the direction/force vector for each number.
    """
    primes = [2, 3, 5, 7]

    print("\n2. DIRECTION VECTORS (force toward nearest multiple)")
    print("-" * 60)
    print("Positive = pulled toward next multiple")
    print("Negative = pulled toward previous multiple")
    print("Zero = AT a multiple (resonance)")
    print()

    print(f"{'n':>4} | ", end="")
    for p in primes:
        print(f"F_{p:<2}  ", end="")
    print("| Prime? | Interpretation")
    print("-" * 70)

    for n in range(2, 25):
        forces = direction_vector(n, primes)
        force_strs = []

        for p in primes:
            if p < n:
                f = next((f for pr, f in forces if pr == p), 0)
                if f == 0:
                    force_strs.append(" [0] ")  # AT resonance
                else:
                    force_strs.append(f"{f:+4d} ")
            else:
                force_strs.append("   - ")

        is_p = "✓" if is_prime(n) else " "

        # Find which prime catches it (if any)
        zero_primes = [p for p in primes if p < n and n % p == 0]
        if zero_primes:
            interp = f"Caught by {zero_primes[0]}"
        elif is_prime(n):
            interp = "ESCAPES ALL"
        else:
            interp = ""

        print(f"{n:4d} | {''.join(force_strs)} |   {is_p}    | {interp}")


def surface_tension_balance():
    """
    The critical line interpretation: where tension balances.
    """
    print("\n3. SURFACE TENSION BALANCE")
    print("-" * 60)
    print("""
The σ = 1/2 condition:

For each prime p, there are two competing effects:
- p^{-σ}: The "weight" of the prime (how much it contributes)
- √p: The "scale" at which the prime operates

At σ = 1/2: p^{-1/2} × √p = 1 for ALL primes.

This is like a BALANCE CONDITION:
- Inward tension (small primes, large weight) = Outward tension (large primes, spread measure)
- At balance, the "surface" of the prime distribution is stable.

Below σ = 1/2:
- Small primes have weight > 1 (p^{-σ} > p^{-1/2} for small p)
- The distribution is pulled "inward" (more primes bunched up)

Above σ = 1/2:
- Large primes have more weight relative to their measure
- The distribution spreads "outward"

The critical line is the PHASE BOUNDARY between these regimes.
""")

    # Demonstrate the balance
    print("Verification: p^{-1/2} × √p = 1")
    print(f"{'p':>4} | {'p^{-1/2}':<12} | {'√p':<12} | {'product':<12}")
    print("-" * 50)

    for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 97, 997]:
        weight = p ** (-0.5)
        scale = math.sqrt(p)
        product = weight * scale
        print(f"{p:4d} | {weight:<12.6f} | {scale:<12.6f} | {product:<12.6f}")


def the_deep_insight():
    """
    The geometric meaning of it all.
    """
    print("\n" + "=" * 80)
    print("THE DEEP INSIGHT: What Each Dimension Does")
    print("=" * 80)
    print("""
When you add a prime p to the sieve:

1. PHASE SPACE EXPANDS
   - The space goes from dimension n to dimension n+1
   - Each point n splits into p different "phases" (n mod p = 0, 1, ..., p-1)
   - Only 1/p of the phases are "resonant" (divisible)

2. ROTATION, NOT JUST REMOVAL
   - The survivors are ROTATED in this higher-dimensional space
   - Their "angle" relative to p is now fixed
   - This angle becomes part of their identity

3. TENSION ACCUMULATES
   - Each prime adds a new "direction" of tension
   - The tension pulls numbers toward being divisible
   - Primes are numbers that RESIST all tensions simultaneously

4. THE CRITICAL LINE
   - At σ = 1/2, the tensions from all primes BALANCE
   - Small primes (strong, local) balance large primes (weak, global)
   - This balance is why zeros cluster on σ = 1/2

THE QUESTION YOU'RE ASKING:
"What happens when you add a trillion?"

Adding a large number N:
- Doesn't change the STRUCTURE (same mod relationships)
- SHIFTS the phase window we're viewing
- The primes we see are determined by their phases relative to ALL primes ≤ √N
- These phases don't "shift linearly" - they precess at different rates

The primes at N are determined by a HIGH-DIMENSIONAL phase alignment.
No simple formula captures this because the alignment is inherently
transcendental (involves log of each prime).

This is why the Riemann zeros encode the distribution:
- Each zero γ corresponds to a "frequency" in log-space
- The phases sin(γ log p) for each prime create the interference pattern
- The primes emerge where ALL these waves constructively interfere
""")


def main():
    analyze_tension()
    analyze_direction()
    surface_tension_balance()
    the_deep_insight()


if __name__ == "__main__":
    main()
