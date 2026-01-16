# Response to Wolfram - Execute P0 Tasks

---

## Your Observation is Correct

You identified the core problem:

```
Claimed:  Im⟨v,Kv⟩ = (σ - 1/2) Σ Λ(n)|v_n|²
Derived:  Im⟨v,Kv⟩ = -Σ Λ(n)|v_n|² n^{-σ} sin(t log n)

These are NOT equal in general.
```

**This is the critical issue we need to quantify.**

---

## Execute These Tasks (in order)

### Task 1: Rayleigh Identity Test
```mathematica
(* Run this first *)
result1 = TestRayleighBatch[1000, 1000];
Print["Mean Error: ", result1["MeanError"]];
Print["Max Error: ", result1["MaxError"]];
Print["StdDev: ", result1["StdError"]];
```

**Expected:** Large errors (confirming the identity fails for arbitrary v)

---

### Task 10a: Off-Critical Kernel Search
```mathematica
(* Search for near-zero eigenvalues at σ ≠ 1/2 *)
offCritical = SearchOffCriticalKernel[{0.1, 0.9}, {10, 50}, 500, 30];
Print["Found ", Length[offCritical], " suspicious points off critical line"];
If[Length[offCritical] > 0, Print[offCritical[[1;;Min[5, Length[offCritical]]]]]]
```

**Expected:** Many points (because K is diagonal and always has kernel)

---

### Task 10b: Critical Line Correlation
```mathematica
(* Does min eigenvalue correlate with |ζ(s)|? *)
criticalData = SearchCriticalLineKernel[{10, 50}, 500, 100];
(* Plot min eigenvalue vs |ζ(1/2+it)| *)
ListPlot[{criticalData[[All, {1, 2}]], criticalData[[All, {1, 3}]]},
  PlotLegends -> {"Min|λ|", "|ζ(s)|"}]
```

**Expected:** No correlation (because diagonal K has constant kernel structure)

---

### Task 4: Eigenvalues at Zeta Zeros
```mathematica
ZetaZeros = {14.1347, 21.0220, 25.0109, 30.4249, 32.9351};
Do[
  result = AnalyzeAtZero[γ, 500];
  Print["γ = ", γ, ", Min|λ| = ", result["minEigenvalue"]],
  {γ, ZetaZeros}
]
```

**Expected:** Min eigenvalue is always 0 (because Λ(1) = 0, etc.)

---

## Key Question After Results

Once you have results, answer:

1. **Does Rayleigh Identity hold?** (Task 1 error magnitude)
2. **Is kernel existence special?** (Task 10 - or does K always have kernel?)
3. **Do zeta zeros matter?** (Task 4 - or is eigenvalue structure constant?)

If all three fail (as we expect), we confirm:
- **The diagonal operator formulation doesn't work**
- **The paper's claims need a different operator definition**
- **Investigate the ROTOR formulation instead (Part 9 of the request)**

---

## REMINDER: K(s) is Diagonal

The operator K(s) = diag(Λ(n)·n^{-s}) has:
- Λ(1) = 0 → kernel direction e₁
- Λ(6) = 0 → kernel direction e₆
- etc.

**K(s) ALWAYS has non-trivial kernel regardless of s.**

This structural issue may invalidate all tests on the diagonal operator. But run them anyway to confirm, then move to rotor formulation.

---

**Please proceed and report numerical results.**
