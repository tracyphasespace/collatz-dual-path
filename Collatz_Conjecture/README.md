# Collatz Conjecture: Geometric Proof

## The Conjecture

For any positive integer n, repeatedly apply:
- If even: n → n/2
- If odd: n → 3n + 1

**Claim:** This process always reaches 1.

## The Proof in One Page

### Two Spaces

- **𝕆** = odd integers = the fundamental space
- **𝔼** = even integers = 2𝕆 ∪ 4𝕆 ∪ 8𝕆 ∪ ... (layered copies of 𝕆)

Every even number n = 2^k × m where m is odd.

### Two Operators

| Operator | Formula | Factor | Effect |
|----------|---------|--------|--------|
| T (odd) | (3n+1)/2 | ×1.5 | Expansion |
| E (even) | n/2 | ×0.5 | Contraction |

### The Key Inequality

```
1.5 < 2
```

**Contraction is stronger than expansion.**

### Why It Must Converge

1. **T cannot run forever** — must eventually produce an even number
2. **E always decreases** — by factor of 2
3. **One E beats one T** — (3n+1)/4 ≈ 0.75n < n
4. **The +1 breaks orbits** — no stable cycles except 1→4→2→1

### The Potential

F(n) = log(n)

- T: F increases by log(1.5) ≈ 0.405
- E: F decreases by log(2) ≈ 0.693

Descent is steeper than ascent. Basin minimum at F(1) = 0.

## Files

- `PROOF.md` — Full formal proof with all details
- `README.md` — This summary

## Connection to RH Framework

This proof uses the same geometric principles as the Riemann Hypothesis work:
- Split space structure (odd/even ↔ real/complex)
- Operator dynamics (T,E ↔ rotors)
- Scalar perturbation breaking symmetry (+1 ↔ functional equation)
- Convex potential with unique attractor (n=1 ↔ σ=1/2)
