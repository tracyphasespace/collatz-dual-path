# Weighted Rotor Closure Approach

**Date:** 2026-01-16
**Status:** NEW DIRECTION - Addresses limitations of previous tests

---

## The Key Insight

Previous tests failed because:

1. **Too few primes** - Only using p ≤ 50, missing the "tail closure" behavior
2. **No decay weighting** - Equal magnitude rotors don't converge
3. **Wrong observables** - Raw norms don't capture phase interference

The fix: **Weighted rotor sums with proper decay**

---

## The Weighted Rotor Sum

Define:
```
K_P(t) = Σ_{p≤P} Λ(p) · p^{-σ} · exp(B_p · t·log p)
```

Where:
- Λ(p) = log(p) (von Mangoldt weight)
- p^{-σ} provides decay for large primes
- B_p ∈ Cl(3,3) are prime-indexed bivectors
- exp(B·θ) = cos(θ) + B·sin(θ)

---

## Expected Behavior

| σ | Behavior as P → ∞ |
|---|-------------------|
| σ < 1/2 | Sum grows (rotors expand) |
| σ = 1/2 | Sum stabilizes (unitary, balanced) |
| σ > 1/2 | Sum collapses (rotors contract) |

**Only at σ = 1/2 does the infinite tail "close" properly.**

---

## Why This Should Work

### At σ = 1/2:
- Each rotor has unit scaling: p^{-1/2} · √p = 1 in L² sense
- Large primes contribute small, fast-rotating terms
- Oscillations average out → bounded sum
- "Closure" = geometric stabilization

### At σ ≠ 1/2:
- Scaling factor p^{-(σ-1/2)} ≠ 1
- σ < 1/2: factors > 1, sum grows
- σ > 1/2: factors < 1, sum shrinks
- No stable limit → instability

---

## The Closure Observable

Define closure norm:
```
||K_P(t)|| = scalar norm of the Cl(3,3) multivector
```

Track this as P increases:
- If it stabilizes → closure achieved
- If it grows/shrinks unboundedly → no closure

---

## Implementation

### Python (with clifford package):
```python
from clifford import Cl
from sympy import primerange

layout, blades = Cl(3, 3, firstIdx=1)
e = blades

def bivector_for_prime(p):
    i = (p % 3) + 1
    j = (p % 3) + 4
    return e[i] ^ e[j]

def weighted_rotor_sum(maxP, sigma, t):
    total = layout.MultiVector()
    for p in primerange(2, maxP + 1):
        weight = np.log(p) * (p ** (-sigma))
        theta = t * np.log(p)
        B = bivector_for_prime(p)
        R = np.cos(theta) + B * np.sin(theta)
        total += weight * R
    return total
```

### Test Protocol:
1. Fix t (e.g., first zeta zero 14.1347)
2. Sweep σ from 0.3 to 0.7
3. For each σ, increase maxP from 100 to 10000
4. Plot ||K_P(t)|| vs P for each σ

---

## Connection to Previous Results

### What still holds:
- Unitarity at σ = 1/2 (proven)
- Prime irreducibility essential (confirmed)
- Eigenvalue magnitudes = 1 at σ = 1/2 (proven)

### What this adds:
- Proper infinite product treatment
- Decay structure that enforces convergence
- Physical interpretation: "closure" = geometric stability

---

## Predictions

If this approach works, we should see:

1. **At σ = 0.5**: ||K_P(t)|| converges to finite value as P → ∞
2. **At σ ≠ 0.5**: ||K_P(t)|| diverges (grows or collapses)
3. **Near zeta zeros**: Special structure in the converged value

This would demonstrate that **the critical line emerges from geometric closure
of the prime rotor field** - not imposed, but derived.

---

## Files

- `scripts/experiments/cl33_rotor_closure.py` - Python implementation
- Can run locally with large prime sets (p ≤ 10000+)

---

*New approach documented 2026-01-16*
