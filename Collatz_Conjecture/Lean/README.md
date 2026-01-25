# Collatz Conjecture: Lean 4 Formalization

## Overview

This directory contains a Lean 4 formalization of the geometric proof framework for the Collatz Conjecture.

## File Structure

- `Collatz.lean` - Main formalization with definitions and theorems

## Proof Status

### Fully Proven (no sorry)

| Theorem | Description |
|---------|-------------|
| `decomposition` | Every n = 2^k × m where m is odd |
| `fundamental_asymmetry` | 3/2 < 2 |
| `log_asymmetry` | log(3/2) < log(2) |
| `expansion_less_than_contraction` | log(3) - log(2) < log(2) |
| `T_E_contracts` | One T + one E contracts (for n > 2) |
| `T_parity` | Parity of T(n) depends on n mod 4 |
| `T_produces_even` | n ≡ 1 (mod 4) ⟹ T(n) even |
| `T_produces_odd` | n ≡ 3 (mod 4) ⟹ T(n) odd |
| `no_odd_fixed_point` | T(n) ≠ n for odd n > 1 |
| `powers_coprime` | 3^k ≠ 2^m for positive k, m |
| `no_multiplicative_cycle` | 3^k / 2^m ≠ 1 |
| `trivial_cycle` | 1 → 4 → 2 → 1 verified |

### Requires Further Work (sorry)

| Theorem | Gap |
|---------|-----|
| `consecutive_T_bounded` | Detailed 2-adic valuation analysis |
| `E_decreases_potential` | Integer division casting to reals |
| `T_bounded_increase` | Edge case at n = 1 |
| `multiplicative_has_fixed_points` | Constructive cycle witness |
| `criticalRatio_bound` | Numerical logarithm bounds |
| `collatz_conjecture` | Main theorem (combines all pieces) |

## Key Definitions

```lean
-- The two operators
def E (n : ℕ) : ℕ := n / 2                    -- Contraction by 2
def T (n : ℕ) : ℕ := (3 * n + 1) / 2          -- Expansion by ~3/2

-- The potential function
def potential (n : ℕ) : ℝ := Real.log n

-- Structure
def height (n : ℕ) : ℕ := n.factorization 2   -- 2-adic valuation
def oddCore (n : ℕ) : ℕ := n / 2^(height n)   -- Odd part
```

## The Core Argument

1. **Asymmetry**: `fundamental_asymmetry` proves 3/2 < 2
2. **No Cycles**: `powers_coprime` shows 3^k ≠ 2^m, ruling out multiplicative cycles
3. **No Fixed Points**: `no_odd_fixed_point` shows T(n) ≠ n
4. **Contraction Dominates**: `T_E_contracts` shows one E beats one T

The remaining gap is formalizing why these properties together force convergence.

## Building

This file is designed to be compatible with Lean 4.27.0 and Mathlib v4.27.0-rc1.

```bash
# From the main Lean directory
lake build Collatz
```

## Connection to RH Framework

This proof mirrors the Riemann Hypothesis geometric approach:

| RH | Collatz |
|----|---------|
| Cl(3,3) rotors | Operators T, E |
| σ = 1/2 attractor | n = 1 attractor |
| Energy convexity | Log potential convexity |
| Functional equation symmetry | Asymmetry 3/2 < 2 |
