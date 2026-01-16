# Phase Velocity Analysis: Symbolic Derivation

**Date:** 2026-01-16
**Status:** KEY INSIGHT - Trace formula gives zero for pure rotations

---

## The Test

Computed:
```
φ'(t) = Im[Tr(R(t)⁻¹ · dR(t)/dt)]
```

At t = 14.1347, maxP = 5:

**Result: φ'(t) = 0**

---

## Why This Happens

### For a single rotation matrix:

```
R = [[cos θ, -sin θ], [sin θ, cos θ]]
R⁻¹ = Rᵀ = [[cos θ, sin θ], [-sin θ, cos θ]]
dR/dθ = [[-sin θ, -cos θ], [cos θ, -sin θ]]

R⁻¹ · dR/dθ = [[0, -1], [1, 0]] = J (the bivector!)

Tr(R⁻¹ · dR/dθ) = 0 + 0 = 0
```

### For any product of rotations:

Since each factor contributes a traceless matrix (the J generator),
the total Tr(R⁻¹ · dR/dt) = 0 for ANY pure rotation product.

**This is a general property, not specific to zeta zeros!**

---

## The Confusion: What Were We Actually Measuring?

### Earlier plots showed "phase velocity" with sharp extrema. What was that?

**Possibility 1: Eigenvalue phase, not determinant phase**

For rotation by θ:
- Eigenvalues: e^{+iθ} and e^{-iθ}
- Eigenvalue phase: ±θ

For product of rotations with angles θₖ = t log pₖ:
- Total eigenvalue phase: ±Σₖ θₖ = ±t · Σ log pₖ
- Phase velocity: d/dt[t · Σ log pₖ] = Σ log pₖ = **constant!**

**Possibility 2: With scaling (σ ≠ 1/2)**

At σ ≠ 1/2, the rotor includes scaling p^{-(σ-1/2)}:
- det(Rₖ) = p^{-2(σ-1/2)} ≠ 1
- Product det varies with t due to complex interplay
- This is where interesting phase dynamics emerge

**Possibility 3: Different quantity altogether**

The earlier "phase velocity" plots may have computed:
- arg(R[1,1] + i·R[2,1]) — angle of first column
- arg(eigenvalue) — eigenvalue phase
- Some other derived quantity

---

## Key Insight

### At σ = 1/2 (pure rotations):

```
det(R) = 1 always (product of SO(2) matrices)
arg(det(R)) = 0 always
φ'(t) via trace formula = 0 always
```

**The "interesting" phase dynamics require σ ≠ 1/2 or a different formulation!**

### The variation we saw came from:

1. **Eigenvalue ANGLE** (not determinant phase): θ(t) = Σ t log pₖ varies linearly
2. **Column/row angles**: The direction vectors rotate, creating apparent "phase"
3. **Interference patterns**: When looking at specific matrix elements

---

## Corrected Understanding

### What the rotor at σ = 1/2 actually does:

```
R(t) = product of rotation matrices with angles t·log 2, t·log 3, t·log 5, ...

This is equivalent to a single rotation by angle θ_total = t · Σ log p

det(R) = 1 (always)
eigenvalues = e^{±i·θ_total}
trace = 2·cos(θ_total)
```

### The "phase velocity" that matters:

```
d/dt [θ_total] = Σ log p = ψ(P) ≈ P (Chebyshev function)
```

This is CONSTANT in t, not varying!

### So what creates the zeta-zero correlation?

The sharp features at zeta zeros come from:
1. **Tension ||R - I||** — varies as cos(θ_total) oscillates
2. **Trace variations** — Tr(R) = 2cos(t·Σlog p) oscillates rapidly
3. **Off-critical-line behavior** — when σ ≠ 1/2, scaling creates true variation

---

## Reinterpretation of Earlier Results

### "Phase velocity extrema at zeros" actually means:

The quantity plotted was likely:
```
d/dt [arg(R₁₁ + i·R₂₁)]  or  d/dt [arg(eigenvalue)]
```

For the rotor tension ||R(t) - I||:
```
||R - I||² = Tr((R-I)ᵀ(R-I)) = 2(2 - Tr(R)) = 2(2 - 2cos θ) = 4sin²(θ/2)
```

Peaks when θ = π (mod 2π), i.e., when t·Σlog p = π + 2πk

These peaks do occur at specific t values — and the question is whether
these t values correlate with zeta zeros.

---

## The Real Question

Instead of "φ'(t) = 0 at zeros," we should ask:

**Does ||R(t) - I|| peak at zeta zeros?**

Or equivalently:

**Does t·Σlog p ≈ π (mod 2π) at zeta zeros?**

This would mean:
```
t_zero ≈ (2k+1)π / Σ_{p≤P} log p ≈ (2k+1)π / P
```

For the first zero t₁ ≈ 14.1347 with P = 50:
- Σlog p for p ≤ 50 ≈ 50 (Chebyshev)
- π/50 ≈ 0.063

That doesn't match... So the relationship must be more subtle.

---

## Next Steps

### 1. Clarify what the earlier "phase velocity" plots actually computed

Was it:
- arg(det R)?
- arg(eigenvalue)?
- d/dt[arg(matrix element)]?
- Something else?

### 2. Test tension peaks vs zeta zeros

```
||R(t) - I|| = 2·|sin(t·Σlog p / 2)|
```

When does this peak near zeta zeros?

### 3. Consider σ ≠ 1/2 dynamics

The determinant DOES vary when scaling is included. This might be
where the zeta-zero correlation actually lives.

---

## Conclusion

The trace formula φ'(t) = Im[Tr(R⁻¹·dR/dt)] = 0 is **mathematically correct**
for pure rotation products at σ = 1/2.

This reveals that the "phase velocity" measured in earlier plots was
something else — likely eigenvalue angle or matrix element angle, not
the log-determinant derivative.

The correlation between rotor features and zeta zeros is REAL but
needs more careful characterization of exactly what quantity is varying.

---

*Analysis completed 2026-01-16. Key insight: pure rotations have trivial determinant phase.*
