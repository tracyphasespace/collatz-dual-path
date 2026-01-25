# Collatz Proof Requirements

> **You need a deterministic, checkable descent mechanism that applies to every starting value, not "almost all," and not "in expectation."**

## 1) What would constitute a proof here

### A. Make the paper's main theorem explicitly *conditional* on certificates

**Theorem (Certificate ⇒ Collatz).**
Fix m. Suppose for every residue class r mod 2^m there exists a *decision-tree certificate* C_r such that for every n > 1 with n ≡ r (mod 2^m), following the tree's parity branches yields an iterate T^k(n) < n. Then every orbit reaches 1.

This is a clean well-foundedness argument: repeatedly apply "drop below start" to get a strictly decreasing sequence of positive integers, hence termination.

### B. Then, to make it unconditional, you must actually **produce** those certificates (or prove they exist)

There are only two ways forward:

1. **Computational proof**: generate a finite certificate object (a tree/DAG), and provide an independent verifier (Lean or a tiny checker) that validates the inequalities and coverage. This is the "Four Color Theorem" style.

2. **Pure existence proof**: prove that such certificates must exist for some finite m without enumerating them. That would be essentially a traditional proof of Collatz and is currently the hard, unknown part.

Given the "formal verification pipeline" framing, (1) is the credible path.

---

## 2) Critical technical upgrades needed in the paper

### A. Define certificates as **trees**, not single parity words

The parity of intermediate values is not fixed by the initial residue, so a single word w_r often won't be valid for all n ≡ r (mod 2^m). You must split on k (equivalently refining modulus to 2^{m+1}).

Formalize the object as:

* Node label: congruence constraint n ≡ r (mod 2^m) plus an accumulated affine form n ↦ (3^a n + b)/2^L
* Edge: refine the congruence (increase m) to determine the next parity uniquely.
* Leaf: a verified inequality implying (3^a n + b)/2^L < n for all n in the leaf class.

### B. Make the leaf-check fully rigorous: reduce it to checking the **minimal** n in the class

If 2^L > 3^a, then the function f(n) := (2^L - 3^a)n - b is increasing in n. Therefore it suffices to check the smallest n > 1 in the residue class:

```
n_min(r, m) = r       if r > 1
            = r + 2^m if r ∈ {0, 1}
```

(treating n = 1 as base-case separately).

Then the leaf criterion becomes: b < (2^L - 3^a) · n_min(r, m)

### C. Fix the literature linkage about "m ≈ 60 suffices"

Simons–de Weger is about **nontrivial cycles** (bounds on "m-cycles"), not about residue-class descent certificates. That sentence is not supported by that reference.

For *computational verification ranges*, cite:
* Oliveira e Silva's verification up to 20·2^58 ≈ 5.76×10^18
* Barina's 2025 result pushing verification to 2^71

Neither implies a finite-modulus certificate exists; they are still value-range checks.

### D. Reconcile the "μ_eff = 3/4" discussion with your chosen map

The 3/4 effective multiplier is naturally associated to the **odd-to-odd Syracuse map** U(n) := (3n+1)/2^{v_2(3n+1)}, not to a single-step T. Add a paragraph clarifying this.

Also keep the valuation argument clearly marked as **heuristic**; rigorous results like Tao's explicitly stop at "almost all," not "all."

---

## 3) The realistic strengthening path: produce a certificate artifact + independent checker

### Step 1 — Change the paper's logic spine

1. **Define** certificates as trees over residue refinements.
2. **Prove** (in the paper) that "complete certificate coverage ⇒ UDL ⇒ Collatz."
3. Treat "Carry Soliton / valuation" as **search guidance** (why certificates should exist and why the search should terminate quickly), not as a theorem.

### Step 2 — Generate certificates computationally (symbolic, not enumerating 2^m residues)

Build certificates **top-down**:
* Start with coarse class r mod 2^m
* Symbolically iterate the affine transform
* If parity ambiguity occurs, split to r mod 2^{m+1}
* Memoize identical subproblems (this produces a DAG, not a tree)
* Stop when you reach a leaf inequality that guarantees descent

### Step 3 — Produce a small, auditable "proof object"

The proof object should be a file containing nodes like:
* modulus exponent m
* residue r
* affine parameters (a, b, L)
* children residues if split
* leaf inequality check against n_min(r, m)

Then:
* A **Lean verifier** proves each leaf inequality and that the tree covers all residues.
* The "UDL ⇒ Collatz" part is a short pure proof (no computation).

---

## 4) What *not* to claim (yet)

* Do not claim "mixing in the 2-adic metric" as a proved mechanism. It is motivation; the conjecture's difficulty is precisely that exceptional non-mixing behavior is not ruled out by simple heuristics.

* Do not cite cycle-bound papers as evidence that a finite-modulus descent certificate exists. Cycle bounds are a different axis of control.

---

## 5) Minimal edits for "proof-grade conditional"

1. Add a formal definition: **Descent Certificate Tree**
2. Replace "Lemma (UDL)" with:
   * "**Definition (UDL)**"
   * "**Theorem: Certificate coverage ⇒ UDL**"
   * "**Theorem: UDL ⇒ Collatz**"
3. Move soliton/valuation section into "Heuristic search motivation"
4. Correct computational-verification citations

---

## The decisive deliverable

> **A certificate generator that outputs a finite DAG of residue refinements, plus a separate checker (Lean or otherwise) that verifies the DAG implies UDL.**

## References

1. [Simons & de Weger - Theoretical and computational bounds for m-cycles](https://research.tue.nl/en/publications/theoretical-and-computational-bounds-for-m-cycles-of-the-3n1-prob/)
2. [Oliveira e Silva - 3x+1 verification results](https://sweet.ua.pt/tos/3x_plus_1.html)
3. [Barina 2025 - Improved verification limit](https://link.springer.com/article/10.1007/s11227-025-07337-0)
4. [Tao 2019 - Almost all orbits attain almost bounded values](https://arxiv.org/abs/1909.03562)
