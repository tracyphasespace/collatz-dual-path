# Fredholm Determinant Test Results

**Date:** 2026-01-16
**Status:** HYPOTHESIS NOT CONFIRMED - Deeper structure needed

---

## Executive Summary

The naive Fredholm identity `det(I - R) = 1/ζ(s)` does **NOT** hold for finite
prime rotor constructions. The eigenvalues of R do **NOT** approach 1 at zeta
zeros as maxP increases.

This does NOT invalidate the rotor unitarity results, but indicates that the
connection to Fredholm theory requires a more sophisticated operator construction.

---

## Test 1: det(I-R) vs 1/ζ(s)

At t₀ = 14.1347 (first zeta zero), σ = 1/2, maxP = 50:

| Quantity | Value |
|----------|-------|
| det(I - R) | 0.76835 |
| |det(I - R)| | 0.76835 |
| 1/ζ_B(s) | 9.49 - 2.22i |
| |1/ζ_B| | 9.7486 |
| **Ratio** | 0.0767 + 0.0179i |

### Result: ❌ NO MATCH

- Magnitudes differ by factor of ~12
- Phase angles unrelated
- det(I-R) remains finite while 1/ζ should diverge at zeros

---

## Test 2: Eigenvalues at Zeta Zeros

Using primes ≤ 50, σ = 1/2:

| t | Eigenvalues of R(t) | min|λ - 1| |
|---|---------------------|------------|
| 14.1347 | 0.616 ± 0.788i | 0.877 |
| 21.0220 | 0.964 ± 0.266i | 0.269 |
| 25.0109 | 0.957 ± 0.289i | 0.292 |
| 30.4249 | -0.539 ± 0.842i | 1.75 |
| 32.9351 | -0.281 ± 0.960i | 1.60 |

### Result: ❌ EIGENVALUES NOT EQUAL TO 1

- All eigenvalues are on unit circle (confirming unitarity at σ = 1/2)
- But NO eigenvalue equals 1 at any tested zero
- Closest approach: ~0.27 at t = 21.0220

---

## Test 3: Convergence with Increasing maxP

Does min|λ - 1| → 0 as maxP → ∞?

| t | maxP=50 | maxP=100 | maxP=200 | maxP=300 |
|---|---------|----------|----------|----------|
| 14.1347 | 0.877 | 1.799 | 1.144 | 1.163 |
| 21.0220 | 0.269 | 0.821 | 0.693 | 0.864 |
| 25.0109 | 0.292 | 1.580 | 1.907 | 1.508 |

### Result: ❌ NO CONVERGENCE

- Distance sometimes INCREASES with more primes
- No clear trend toward eigenvalue 1
- Finite rotor construction does NOT approximate Fredholm picture

---

## Analysis: Why the Mismatch?

### 1. Dimension Mismatch

- ζ(s) is an infinite product over ALL primes
- Rotor R(t) is a 2×2 matrix using FINITE primes
- det(I - R) is a 2×2 determinant, not a Fredholm determinant

### 2. Operator Space Mismatch

The Fredholm identity applies to:
```
det(I - K) where K : H → H is trace-class on infinite-dim Hilbert space
```

Our rotor is:
```
R : ℝ² → ℝ² (finite-dimensional)
```

### 3. What Would Be Needed

To properly test Fredholm connection, we'd need:
- Infinite-dimensional Hilbert space H (e.g., L²(0,∞))
- Operator K(s) acting on H with Tr(K^n) related to prime sums
- Proper trace-class conditions

---

## What Remains Valid

Despite the Fredholm test failure, these results STILL HOLD:

| Result | Status |
|--------|--------|
| σ = 1/2 is only unitary line | ✅ PROVEN |
| Eigenvalue magnitudes = 1 only at σ = 1/2 | ✅ PROVEN |
| Prime irreducibility essential | ✅ CONFIRMED |
| Phase velocity extrema at zeros | ✅ CONFIRMED |
| Tension spikes at zeros | ✅ CONFIRMED |

The rotor formulation captures GEOMETRIC structure that correlates with zeros,
even if the direct Fredholm identity doesn't hold for finite constructions.

---

## Revised Understanding

### What the Rotor DOES Show

1. **Critical line uniqueness:** σ = 1/2 is geometrically special (unitarity)
2. **Prime necessity:** Only primes create zeta-correlated structure
3. **Phase dynamics:** Sharp features at zero locations

### What the Rotor Does NOT Show (Yet)

1. **Direct zero characterization:** Eigenvalue = 1 at zeros
2. **Fredholm identity:** det(I-R) = 1/ζ(s)
3. **Convergence:** Finite → infinite limit recovering zeros

---

## Possible Paths Forward

### Path A: Infinite-Dimensional Rotor

Construct operator on L²(0,∞) with kernel:
```
K(x,y) = Σ_p f_p(x) g_p(y) where f_p, g_p encode prime rotations
```

### Path B: Different Normalization/Scaling

The det(I-R) and 1/ζ differ by factor ~12. Perhaps:
```
det(I - α·R) = 1/ζ(s) for some α(s)
```

### Path C: Trace Formula Approach

Instead of determinant identity, try:
```
Tr(R^n) ~ Σ_p (log p)^n · p^{-ns}
```

Connect via log det = -Σ Tr(K^n)/n

### Path D: Accept Geometric Characterization

The rotor may characterize the LINE (σ = 1/2) without directly
characterizing POINTS (zeros) on that line. This is still valuable
but different from what we hoped.

---

## Conclusion

The Fredholm determinant hypothesis `det(I-R) = 1/ζ(s)` is **NOT CONFIRMED**
for finite prime rotor constructions.

This indicates that:
1. The naive 2×2 rotor is insufficient for the Fredholm connection
2. A proper infinite-dimensional formulation is needed
3. OR the rotor approach characterizes the LINE but not the POINTS

The unitarity theorem (σ = 1/2 uniqueness) and prime irreducibility results
remain valid and significant.

---

## Updated Proof Status

```
LEVEL 1: ARITHMETIC - ✅ Established
LEVEL 2: GEOMETRIC (frequency independence) - ✅ Confirmed
LEVEL 3: UNITARITY - ✅ Proven
LEVEL 4: FREDHOLM CONNECTION - ❌ NOT CONFIRMED (needs deeper structure)
LEVEL 5: FUNCTIONAL EQUATION - ✅ Established
LEVEL 6: RH - ⏳ Blocked by Level 4
```

---

*Fredholm test completed 2026-01-16. Negative result documented honestly.*
