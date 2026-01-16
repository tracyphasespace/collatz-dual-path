# Weighted Rotor Closure Test Results

**Date:** 2026-01-16
**Status:** HYPOTHESIS NOT CONFIRMED

---

## Test Setup

Used Kingdon library for proper Cl(3,3) Clifford algebra:

```python
from kingdon import Algebra
alg = Algebra(p=3, q=3)  # Signature (+,+,+,-,-,-)
```

### Critical Fix: Bivector Planes

Original approach used mixed-signature bivectors (e1^e4, e2^e5, e3^e6).
These square to **+1**, giving hyperbolic rotors (cosh/sinh), not circular rotors!

Fixed to use same-signature bivectors that square to **-1**:
- e1^e2, e1^e3, e2^e3 (positive-positive)
- e4^e5, e4^e6, e5^e6 (negative-negative)

### Kingdon Verification

All operations verified correct:
- Basis vectors: e1²=e2²=e3²=+1, e4²=e5²=e6²=-1
- Bivectors: B² = -1 for same-signature planes
- Rotors: R·~R = 1 (unitary)
- Products: R(θ₁)·R(θ₂) = R(θ₁+θ₂)
- Norms: Correctly computed via scalar part of K·~K

---

## Results

### Sigma Sweep (maxP=500, t=14.1347)

| σ | Norm |
|---|------|
| 0.3 | 12.54 |
| 0.4 | 8.67 |
| 0.5 | 6.19 |
| 0.6 | 4.57 |
| 0.7 | 3.46 |

**Observation:** Norm decreases monotonically with σ. No special behavior at σ=0.5.

---

### Prime Convergence (σ=0.5, t=14.1347)

| maxP | Norm |
|------|------|
| 100 | 3.96 |
| 200 | 5.25 |
| 500 | 6.19 |
| 1000 | 7.64 |
| 2000 | 6.37 |
| 5000 | 4.72 |

**Observation:** Norm oscillates, not converging. Growth rate similar across all σ values.

---

### Zero vs Non-Zero Comparison (σ=0.5)

| maxP | At Zeros (mean) | At Non-zeros (mean) |
|------|-----------------|---------------------|
| 500 | 6.19 | 2.25 |
| 1000 | 6.13 | 2.56 |
| 2000 | 6.96 | 2.84 |

**Unexpected Result:** Norms at zeta zeros are **HIGHER** than at non-zeros!

This is the opposite of what "closure" would predict.

---

### T-scan Local Minima (σ=0.5, maxP=1000)

Local minima found at:
- t = 12.50, 13.50, 19.00, 22.50, 29.00, 31.50, ...

**Zeta zeros:** 14.1347, 21.0220, 25.0109, 30.4249, 32.9351

**Observation:** Local minima do NOT coincide with zeta zeros.

---

## Analysis

### Why the Hypothesis Failed

1. **No Convergence at σ=0.5**
   - The weighted sum oscillates for all σ values
   - Growth rates are similar (~1.2x from 100 to 5000 primes)
   - σ=0.5 shows no special stabilization

2. **Zeros Have Higher Norms**
   - If "closure" meant small norm, zeros should have smaller norms
   - Instead, zeros have ~2-3x higher norms than non-zeros
   - This suggests the weighted sum is actually larger at zeros

3. **The Weighting Doesn't Capture Zero Locations**
   - p^{-σ} decay doesn't encode where zeros are
   - Zeros arise from infinite interference in ζ(s), not from finite rotor sums

---

## Theoretical Reflection

The weighted rotor approach captures some aspects:
- σ=0.5 is still the unitarity locus (individual rotors unitary)
- Primes contribute with natural log-weighting

But the sum K_P(t) = Σ Λ(p)·p^{-σ}·R_p(t):
- Is NOT the Euler product (which is a product, not sum)
- Does NOT have zeros at the same locations as ζ(s)
- Oscillates rather than converging/diverging

---

## What This Tells Us

The weighted rotor sum is a **different object** from the zeta function.

While both involve primes and oscillations, the zero locations are encoded in:
- ζ(s) = Π_p (1-p^{-s})^{-1} (infinite product)
- Not in Σ log(p)·p^{-σ}·R_p(t) (weighted sum)

The connection between rotors and RH must go through the **product** structure,
not through weighted sums.

---

## Possible Next Steps

1. **Test rotor products** instead of sums: Π_p R_p(t)
2. **Use renormalized infinite products** with proper limiting procedure
3. **Test spectral interference functional** S(t) = Σ_{i<j} sin(t·log(p_i/p_j))
4. **Try higher-dimensional Cl(n,n)** with non-commuting bivector planes

---

*Test completed 2026-01-16*
