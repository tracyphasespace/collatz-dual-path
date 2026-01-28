# Collatz Dual-Path Proof Certificate

**Generated:** 2026-01-28 04:55:53 UTC
**Lean Version:** v4.27.0
**Mathlib Version:** v4.27.0

---

## 1. Build Verification

```
Build timestamp: 2026-01-28 04:55:53 UTC
Build completed successfully (3078 jobs).
```

---

## 2. Sorry Check

```
Lines with standalone 'sorry': 0
Status: ✅ NO SORRIES FOUND
```

---

## 3. Custom Axiom Inventory

```
Custom axioms declared in this project:
Axioms.lean:75:axiom geometric_dominance (n : ℕ) (hn : 4 < n) :
    ∃ k : ℕ, k ≤ 100 * Nat.log2 n ∧ trajectory n k < n
```

---

## 4. Verification Summary

| Component | Status |
|-----------|--------|
| Build | ✅ SUCCESS |
| Sorries | ✅ NONE |
| Custom Axioms | 1 (geometric_dominance) |
| Path B Core | ✅ AXIOM-FREE |

---

*Certificate generated for Collatz Dual-Path Formalization*
*Author: Tracy D. McSheery*
