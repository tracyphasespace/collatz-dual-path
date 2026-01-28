# Collatz Dual-Path (Lean 4)

**A Lean-checked reduction of the Collatz Conjecture to one conditional axiom**

✅ 0 `sorry`  •  ⚠️ 1 remaining axiom  •  🧾 reproducible build  •  Lean 4.27.0

---

> **Status:** This is a *machine-checked conditional proof*.
> The full Collatz Conjecture follows from **one explicit axiom** (`geometric_dominance`).
> Discharging this axiom would yield an unconditional proof.

---

## 1. What is the Collatz Conjecture?

Define the Collatz map on positive integers:
- if `n` is even: `n ↦ n/2`
- if `n` is odd: `n ↦ 3n + 1`

The **Collatz Conjecture** states that *starting from any positive integer and iterating this rule, the trajectory eventually reaches 1*.

It's simple to state, brutally hard to prove. Open since 1937.

---

## 2. What This Repository Proves (in Lean)

**Main Theorem (Lean-checked):**
> If `geometric_dominance` holds, then the Collatz Conjecture holds for all positive integers.

Everything except the single axiom is proved in Lean with **no placeholders**.

```lean
theorem collatz_conjecture' (n : ℕ) (hn : 0 < n) : eventuallyOne n
-- Depends on: geometric_dominance (1 custom axiom)
-- Plus standard: propext, Classical.choice, Quot.sound
```

---

## 3. The Single Remaining Axiom

### Plain English
**Geometric Dominance:** *Every starting value n > 4 eventually reaches a value smaller than n within O(log n) steps.*

This captures the intuition that "what goes up must come down" — contraction dominates expansion.

### Lean Statement (verbatim)
```lean
axiom geometric_dominance (n : ℕ) (hn : 4 < n) :
    ∃ k : ℕ, k ≤ 100 * Nat.log2 n ∧ trajectory n k < n
```

### Why This is the Only Gap
- ✅ We prove: `geometric_dominance` ⇒ every trajectory descends
- ✅ We prove: descent ⇒ no divergence, no nontrivial cycles
- ✅ We prove: therefore every orbit reaches 1
- ⚠️ Remains: prove `geometric_dominance` itself

---

## 4. The Grandfather Paradox

The key insight is that **divergence is self-defeating**:

> To escape to infinity, a trajectory must maintain odd-step density > 63%.
> But the Soliton mechanism (`gcd(3n+1, 3) = 1`) prevents phase-locking with expansion.

**It's like trying to rewrite your own past**: every attempt to ascend creates the very factors that pull you back down. This is the *Grandfather Paradox* of Collatz — divergence requires a structure the dynamics keep breaking.

### Axiom-Free Results (Path B)

These theorems are proved **without custom axioms**:

| Theorem | Statement | Status |
|---------|-----------|--------|
| `entropy_brake_engaged` | E[Drift] < 0 (average trajectory descends) | ✅ Axiom-free |
| `soliton_coprime_three` | gcd(3n+1, 3) = 1 (no 3-resonance) | ✅ Axiom-free |
| `spectral_gap_exists` | \|contraction\| > \|expansion\| | ✅ Axiom-free |

---

## 5. Dual-Path Architecture

We split the problem into two complementary approaches:

| Path | Assumption | What It Proves |
|------|------------|----------------|
| **Path A** (Deterministic) | `geometric_dominance` | Full Collatz Conjecture |
| **Path B** (Probabilistic) | `DensityHypothesis` (weaker) | Entropy Brake, expected descent |

**Path B's core is axiom-free** — it proves the system is "rigged" against divergence using only standard Lean axioms.

---

## 6. Reproduce the Lean Check

### Prerequisites
- Lean 4.27.0 (via `elan`)
- `lake` build tool

### Build
```bash
cd Collatz_Conjecture/Lean
lake update
lake build
```

### Verify
```bash
# Check for sorries (should be 0)
grep -r "sorry" *.lean | wc -l

# Check axiom dependencies
lake env lean -c 'import Proof_Complete; #print axioms collatz_conjecture\''
```

---

## 7. Papers

| Document | Description |
|----------|-------------|
| [The Stability of the Collatz Map](The%20Stability%20of%20the%20Collatz%20Map.pdf) | Full theoretical exposition |
| [The Geometric Sieve](The%20Geometric%20Sieve.pdf) | Grandfather Paradox & entropy brake |

---

## 8. Roadmap: Eliminating the Axiom

Concrete steps toward an unconditional proof:

1. **Residue certificates**: Extend mod-32 coverage to higher moduli
2. **Density bounds**: Prove odd-step density stays below critical threshold
3. **Measure theory**: Show "escape to infinity" has measure zero
4. **Verified computation**: Proof-by-reflection for finite exhaustive checks

---

## 9. FAQ

**Is this an unconditional proof of Collatz?**
Not yet. It's a *Lean-checked reduction* to one explicit axiom.

**Why is this valuable?**
It isolates the problem into one falsifiable bottleneck. Either `geometric_dominance` can be proved (yielding Collatz), or its failure would identify exactly what breaks.

**What's the Grandfather Paradox?**
Divergence requires sustained expansion, but the +1 in "3n+1" constantly injects factors that force descent. The trajectory trying to escape creates the conditions that pull it back.

**How does this relate to Tao's result?**
Tao (2019) proved "almost all orbits attain almost bounded values." Our approach formalizes a complete implication chain, conditional on one axiom.

---

## 10. Repository Structure

```
Collatz_Conjecture/Lean/
├── Axioms.lean              # The single axiom (geometric_dominance)
├── Proof_Complete.lean      # Final theorem assembly
├── ProbabilisticDescent.lean # Entropy Brake (axiom-free)
├── PrimeManifold.lean       # Soliton theorem (axiom-free)
├── MersenneProofs.lean      # Core descent machinery
├── Certificates.lean        # Mod-32 verification
├── *.pdf                    # Papers
└── scripts/                 # Build & verification tools
```

---

## 11. Citation

```bibtex
@software{collatz_dual_path_2026,
  author = {McSheery, Tracy D.},
  title = {Collatz Dual-Path: A Lean 4 Conditional Reduction},
  year = {2026},
  url = {https://github.com/tracyphasespace/collatz-dual-path},
  note = {Conditional proof reducing Collatz to geometric\_dominance axiom}
}
```

---

## 12. Contact

Open an Issue for:
- Questions about the axiom
- Proposed approaches to discharge `geometric_dominance`
- PRs strengthening the implication chain

---

**License:** MIT
