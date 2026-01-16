# Simplified Code for Wolfram Cloud

The previous code had syntax issues. Here are simplified, single-expression versions.

---

## TASK 1: Rayleigh Identity Test (Simplified)

**Execute this single block:**

```mathematica
Module[{VonMangoldt, K, LHS, RHS, errors, n = 100, trials = 50},
  VonMangoldt[m_] := If[m < 2, 0, If[PrimePowerQ[m], Log[FactorInteger[m][[1,1]]], 0]];
  K[s_, max_] := DiagonalMatrix[Table[VonMangoldt[j] * j^(-s), {j, 1, max}]];
  errors = Table[Module[{v, sig, t, lhs, rhs},
    v = RandomComplex[{-1-I, 1+I}, n];
    sig = RandomReal[{0.1, 0.9}];
    t = RandomReal[{1, 50}];
    lhs = Im[Conjugate[v] . K[sig + I*t, n] . v];
    rhs = (sig - 0.5) * Total[Table[VonMangoldt[j] * Abs[v[[j]]]^2, {j, 1, n}]];
    Abs[lhs - rhs]], {trials}];
  {Mean[errors], Max[errors], StandardDeviation[errors]}
]
```

**Expected output:** `{mean, max, stddev}` - if mean >> 0, identity fails.

---

## TASK 4: Eigenvalues at First Zeta Zero (Simplified)

**Execute this single block:**

```mathematica
Module[{VonMangoldt, K, gamma = 14.1347, n = 200, eigs},
  VonMangoldt[m_] := If[m < 2, 0, If[PrimePowerQ[m], Log[FactorInteger[m][[1,1]]], 0]];
  K = DiagonalMatrix[Table[VonMangoldt[j] * j^(-(1/2 + I*gamma)), {j, 1, n}]];
  eigs = Eigenvalues[K];
  {Min[Abs[eigs]], Sort[Abs[eigs]][[1;;5]], Abs[Zeta[1/2 + I*gamma]]}
]
```

**Expected output:** `{minEig, first5, zetaMag}` - minEig should be 0 (from Λ(1)=0).

---

## TASK 6: Balance Condition (Simplest Test)

**Execute this single line:**

```mathematica
Table[{p, p^(-1/2) * Sqrt[p]}, {p, {2, 3, 5, 7, 11, 13, 17, 19, 23, 29}}]
```

**Expected output:** All second elements = 1.0 exactly.

---

## TASK: Verify Diagonal Structure Issue

**Execute this to confirm K always has kernel:**

```mathematica
Module[{VonMangoldt, diag, n = 50},
  VonMangoldt[m_] := If[m < 2, 0, If[PrimePowerQ[m], Log[FactorInteger[m][[1,1]]], 0]];
  diag = Table[VonMangoldt[j], {j, 1, n}];
  {Count[diag, 0], Positions[diag, 0][[1;;10]]}
]
```

**Expected output:** Many zeros at positions 1, 6, 10, 12, 14, 15, ... (non-prime-powers).

---

## Execution Order

1. **Start with Task 6** (balance condition) - simplest, one line
2. **Then Task: Diagonal Structure** - confirms the kernel issue
3. **Then Task 4** (eigenvalues at zero) - medium complexity
4. **Finally Task 1** (Rayleigh test) - most complex

If any fail, report the error message.

---

## Alternative: Start with Simplest Possible Test

If still having issues, try just this:

```mathematica
Table[p^(-1/2) * Sqrt[p], {p, Prime[Range[10]]}]
```

This should return `{1, 1, 1, 1, 1, 1, 1, 1, 1, 1}`.

If this works, we know Wolfram Cloud is functional and can proceed with larger tests.
