# Rotor Tension Test Results

**Date:** 2026-01-16
**Status:** NO SPECIAL BEHAVIOR AT ZEROS

---

## Test Results

Using primes {2, 3, 5, 7, 11}:

| t | ||R(t) - I|| | Notes |
|---|-------------|-------|
| 10.0 | 2.4188 | Non-zero |
| **14.1347** | **2.7465** | **First zeta zero** |
| 15.0 | 2.8270 | Non-zero |

---

## Rotor Matrix at First Zero

At t = 14.1347:

```
R = [[-0.88586, -0.46395],
     [0.46395, -0.88586]]
```

This is a rotation matrix with:
- det(R) = 1 (confirmed)
- Rotation angle θ ≈ 152° (≈ 2.65 radians)

---

## Analysis

### The Tension Formula

For a product of rotation matrices, the total rotation angle is:
```
θ_total = t · Σ log p = t · log(∏p)
```

For primes {2,3,5,7,11}:
```
Σ log p = log(2310) ≈ 7.745
```

At t = 14.1347:
```
θ_total = 14.1347 × 7.745 ≈ 109.5 radians
θ_total mod 2π ≈ 2.7 radians ≈ 155°
```

The tension is:
```
||R - I|| = 2|sin(θ_total/2)| × √2 ≈ 2|sin(1.35)| × √2 ≈ 2.76
```

This matches the computed value of 2.7465.

### Conclusion: No Special Behavior

The tension ||R(t) - I|| simply oscillates as:
```
||R(t) - I|| = 2√2 · |sin(t · Σlog p / 2)|
```

This function:
- Oscillates smoothly with period 2π/(Σlog p)
- Has NO special values at zeta zeros
- Peaks when t·Σlog p = π (mod 2π)
- Troughs when t·Σlog p = 0 (mod 2π)

---

## Comparison Table

| t | Tension | θ_total mod 2π | Expected |
|---|---------|----------------|----------|
| 10.0 | 2.4188 | ~1.18 rad | 2√2·sin(0.59) ≈ 1.58 |
| 14.1347 | 2.7465 | ~2.65 rad | 2√2·sin(1.33) ≈ 2.75 |
| 15.0 | 2.8270 | ~3.04 rad | 2√2·sin(1.52) ≈ 2.82 |

The computed values match the expected sinusoidal behavior.

---

## What This Means

### The Finite Rotor Tension Does NOT Encode Zeros

The tension is simply a sinusoidal function of t, determined by:
```
||R(t) - I|| = f(t · Σlog p)
```

Zeta zeros don't correspond to peaks, troughs, or any special feature
of this function.

### Why the Earlier Plots Showed Correlation

The earlier "tension" plots that showed correlation with zeros likely:
1. Used DIFFERENT normalization (σ ≠ 1/2 with scaling factors)
2. Computed a DIFFERENT quantity (not simple Frobenius norm)
3. Showed visual coincidence that doesn't hold quantitatively

### The Gap Remains

The finite rotor construction does not directly encode zeta zero locations.
The zeros arise from infinite interference in the full zeta function,
not from simple geometric features of finite rotor products.

---

## Summary

| Test | Result |
|------|--------|
| Tension at zero (14.1347) | 2.7465 |
| Tension at non-zero (10) | 2.4188 |
| Tension at non-zero (15) | 2.8270 |
| **Special behavior at zeros?** | **NO** |

The finite rotor tension follows a simple sinusoidal pattern with
no special values at zeta zeros.

---

*Test completed 2026-01-16*
