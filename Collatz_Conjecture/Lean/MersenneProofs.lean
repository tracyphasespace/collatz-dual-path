import Mathlib.Data.Nat.Defs
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic
import Aesop

/-!
# Mersenne Analysis: Proving the Axioms

This file proves the key axioms from MersenneAnalysis.lean using atomic lemma decomposition.

## Key Results to Prove

1. `badChainLength_stable` - terminated chains are stable under more fuel
2. `mersenne_dominates` - Mersenne numbers have longest bad chains in their range
3. `mersenne_closed_form` - T^j(2^k - 1) = 3^j · 2^(k-j) - 1

-/

namespace MersenneProofs

-- =============================================================
-- PART 1: BASIC DEFINITIONS (matching CollatzFinal.lean)
-- =============================================================

/-- Mersenne number: 2^k - 1 -/
def mersenne (k : ℕ) : ℕ := 2^k - 1

/-- Compressed Collatz function -/
def T (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- Collatz trajectory -/
def trajectory (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => T (trajectory n k)

/-- Is n in the "bad" class? (odd and ≡ 3 mod 4) -/
def isBad (n : ℕ) : Bool := n % 2 = 1 ∧ n % 4 = 3

/-- Count bad chain length -/
def badChainLength : ℕ → ℕ → ℕ
  | _, 0 => 0
  | n, fuel + 1 =>
    if n ≤ 1 then 0
    else if isBad n then 1 + badChainLength (T n) fuel
    else 0

-- =============================================================
-- PART 2: ATOMIC LEMMAS FOR badChainLength
-- =============================================================

/-- If n ≤ 1, chain length is 0 regardless of fuel -/
lemma badChainLength_le_one (n : ℕ) (hn : n ≤ 1) (fuel : ℕ) :
    badChainLength n fuel = 0 := by
  cases fuel with
  | zero => rfl
  | succ f => simp [badChainLength, hn]

/-- If n is not bad (and n > 1), chain length is 0 -/
lemma badChainLength_not_bad (n : ℕ) (_hn : 1 < n) (hnotbad : isBad n = false) (fuel : ℕ) (hf : 0 < fuel) :
    badChainLength n fuel = 0 := by
  cases fuel with
  | zero => omega
  | succ f =>
    simp [badChainLength]
    intro _
    exact hnotbad

/-- For bad n > 1 with fuel, chain = 1 + chain of T(n) -/
lemma badChainLength_bad (n : ℕ) (hn : 1 < n) (hbad : isBad n = true) (fuel : ℕ) :
    badChainLength n (fuel + 1) = 1 + badChainLength (T n) fuel := by
  simp only [badChainLength]
  have h1 : ¬(n ≤ 1) := by omega
  simp only [h1, ↓reduceIte, hbad, ↓reduceIte]

/-- Chain length is at most fuel -/
lemma badChainLength_le_fuel (n : ℕ) (fuel : ℕ) : badChainLength n fuel ≤ fuel := by
  induction fuel generalizing n with
  | zero => simp [badChainLength]
  | succ f ih =>
    simp only [badChainLength]
    split_ifs with h1 h2
    · omega
    · have := ih (T n)
      omega
    · omega

/-- If chain terminated (returned 0 for non-bad or ≤1), more fuel doesn't change it -/
lemma badChainLength_zero_stable (n : ℕ) (fuel1 fuel2 : ℕ)
    (h1 : 0 < fuel1) (_h2 : fuel1 ≤ fuel2) (hzero : badChainLength n fuel1 = 0) :
    badChainLength n fuel2 = 0 := by
  -- If n ≤ 1, it's 0 for any fuel
  by_cases hn : n ≤ 1
  · exact badChainLength_le_one n hn fuel2
  -- n > 1
  have hnn : ¬(n ≤ 1) := hn
  -- Get fuel1 = f1 + 1 for some f1
  obtain ⟨f1, hf1⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel1 ≠ 0)
  subst hf1
  -- With fuel1 > 0 and n > 1 and badChainLength = 0, isBad n = false
  simp only [badChainLength, hnn, ↓reduceIte] at hzero
  have hnotbad : isBad n = false := by
    by_contra h
    simp only [Bool.not_eq_false] at h
    simp only [h, ↓reduceIte] at hzero
    -- 1 + badChainLength (T n) f1 = 0 is impossible
    omega
  -- Now with isBad n = false, chain is 0
  cases fuel2 with
  | zero => simp only [badChainLength]
  | succ f2 =>
    simp only [badChainLength, hnn, ↓reduceIte]
    simp only [hnotbad, Bool.false_eq_true, ↓reduceIte]

-- =============================================================
-- PART 3: CHAIN STABILITY THEOREM
-- =============================================================

/-- Main stability theorem: if chain terminates with fuel1, adding more fuel doesn't change the result -/
theorem badChainLength_stable (n : ℕ) (fuel1 fuel2 : ℕ)
    (hge : fuel1 ≤ fuel2) (hterm : badChainLength n fuel1 < fuel1) :
    badChainLength n fuel2 = badChainLength n fuel1 := by
  -- Induction on fuel1
  induction fuel1 generalizing n fuel2 with
  | zero =>
    -- fuel1 = 0, hterm says chain < 0, contradiction
    simp [badChainLength] at hterm
  | succ f1 ih =>
    -- fuel1 = f1 + 1
    simp only [badChainLength] at hterm ⊢
    -- Case: n ≤ 1
    by_cases hn : n ≤ 1
    · simp [hn]
      cases fuel2 with
      | zero => omega
      | succ f2 => simp [badChainLength, hn]
    -- Case: n > 1
    push_neg at hn
    have hn1 : ¬(n ≤ 1) := by omega
    simp only [hn1, ↓reduceIte] at hterm ⊢
    -- Case: isBad n
    by_cases hbad : isBad n = true
    · simp only [hbad, ↓reduceIte] at hterm ⊢
      -- hterm: 1 + badChainLength (T n) f1 < f1 + 1
      -- So badChainLength (T n) f1 < f1
      have hterm' : badChainLength (T n) f1 < f1 := by omega
      -- Need fuel2 ≥ 1 for the simp to work
      cases fuel2 with
      | zero => omega
      | succ f2 =>
        simp only [badChainLength, hn1, ↓reduceIte, hbad, ↓reduceIte]
        -- Apply IH to T n
        have hge' : f1 ≤ f2 := by omega
        have heq := ih (T n) f2 hge' hterm'
        omega
    -- Case: not bad
    · simp only [Bool.not_eq_true] at hbad
      simp only [hbad, ↓reduceIte] at hterm ⊢
      cases fuel2 with
      | zero => omega
      | succ f2 =>
        simp only [badChainLength, hn1, ↓reduceIte, hbad, ↓reduceIte]
        rfl

-- =============================================================
-- PART 4: T FUNCTION PROPERTIES
-- =============================================================

/-- T of odd n is (3n+1)/2 -/
lemma T_odd (n : ℕ) (hodd : n % 2 = 1) : T n = (3 * n + 1) / 2 := by
  unfold T
  have h : ¬(n % 2 = 0) := by omega
  simp only [if_neg h]

/-- T of even n is n/2 -/
lemma T_even (n : ℕ) (heven : n % 2 = 0) : T n = n / 2 := by
  unfold T
  simp only [heven, ↓reduceIte]

/-- T is positive for positive inputs -/
lemma T_pos (n : ℕ) (hn : 0 < n) : 0 < T n := by
  simp [T]
  split_ifs <;> omega

/-- isBad means odd and ≡ 3 (mod 4) -/
lemma isBad_iff (n : ℕ) : isBad n = true ↔ n % 2 = 1 ∧ n % 4 = 3 := by
  simp [isBad]

/-- Mersenne numbers are bad for k ≥ 2 -/
lemma mersenne_is_bad (k : ℕ) (hk : 2 ≤ k) : isBad (mersenne k) = true := by
  simp [isBad, mersenne]
  -- 2^k - 1 is odd (all 1s in binary)
  -- For k ≥ 2, 2^k ≡ 0 (mod 4), so 2^k - 1 ≡ 3 (mod 4)
  constructor
  · -- Oddness: 2^k is even, so 2^k - 1 is odd
    have h2k : 2^k % 2 = 0 := by
      have : 2 ∣ 2^k := dvd_pow_self 2 (by omega : k ≠ 0)
      exact Nat.mod_eq_zero_of_dvd this
    have hpos : 0 < 2^k := by positivity
    omega
  · -- ≡ 3 (mod 4): 2^k ≡ 0 (mod 4) for k ≥ 2
    have h4 : 4 ∣ 2^k := by
      have : 2^2 ∣ 2^k := Nat.pow_dvd_pow 2 hk
      simp at this
      exact this
    have h4k : 2^k % 4 = 0 := Nat.mod_eq_zero_of_dvd h4
    have hpos : 0 < 2^k := by positivity
    omega

-- =============================================================
-- PART 5: MERSENNE CLOSED FORM (Key Structural Theorem)
-- =============================================================

/-- Helper: 3^j * 2^m - 1 is odd when m ≥ 1 -/
lemma closed_form_odd (j m : ℕ) (hm : 1 ≤ m) : (3^j * 2^m - 1) % 2 = 1 := by
  have heven : 2 ∣ 3^j * 2^m := by
    apply dvd_mul_of_dvd_right
    exact dvd_pow_self 2 (by omega : m ≠ 0)
  have hpos : 0 < 3^j * 2^m := by positivity
  omega

/-- Helper: 3^j * 2^m - 1 ≡ 3 (mod 4) when m ≥ 2 -/
lemma closed_form_mod4 (j m : ℕ) (hm : 2 ≤ m) : (3^j * 2^m - 1) % 4 = 3 := by
  have h4 : 4 ∣ 3^j * 2^m := by
    apply dvd_mul_of_dvd_right
    have : 2^2 ∣ 2^m := Nat.pow_dvd_pow 2 hm
    simp at this
    exact this
  have hpos : 0 < 3^j * 2^m := by positivity
  omega

/-- Helper: closed form stays bad while m ≥ 2 -/
lemma closed_form_bad (j m : ℕ) (hm : 2 ≤ m) : isBad (3^j * 2^m - 1) = true := by
  rw [isBad_iff]
  constructor
  · exact closed_form_odd j m (by omega)
  · exact closed_form_mod4 j m hm

-- =============================================================
-- ATOMIC LEMMAS FOR T_CLOSED_FORM
-- =============================================================

/-- Atomic: 3^j * 2^m ≥ 1 for all j, m -/
lemma pow_prod_pos (j m : ℕ) : 3^j * 2^m ≥ 1 := by
  have h3 : 1 ≤ 3^j := Nat.one_le_pow j 3 (by omega)
  have h2 : 1 ≤ 2^m := Nat.one_le_pow m 2 (by omega)
  calc 3^j * 2^m ≥ 1 * 1 := Nat.mul_le_mul h3 h2
    _ = 1 := by ring

/-- Atomic: 3 * (3^j * 2^m - 1) + 1 = 3^(j+1) * 2^m - 2 -/
lemma cf_expand (j m : ℕ) (hpos : 3^j * 2^m ≥ 1) :
    3 * (3^j * 2^m - 1) + 1 = 3^(j+1) * 2^m - 2 := by
  have h3j : 3^j ≥ 1 := Nat.one_le_pow j 3 (by omega)
  have h2m : 2^m ≥ 1 := Nat.one_le_pow m 2 (by omega)
  -- pow_succ gives 3^j * 3, we need 3 * 3^j, so use mul_comm
  have hexp : 3^(j+1) = 3 * 3^j := by rw [pow_succ, mul_comm]
  rw [hexp]
  -- Key: 3 * (x - 1) + 1 = 3*x - 2 when x ≥ 1
  -- Let x = 3^j * 2^m
  -- We show: 3 * (x - 1) + 1 = 3*x - 3 + 1 = 3*x - 2
  -- And 3 * 3^j * 2^m = 3 * (3^j * 2^m) by associativity
  have hassoc : 3 * 3^j * 2^m = 3 * (3^j * 2^m) := by ring
  rw [hassoc]
  -- Now prove: 3 * (3^j * 2^m - 1) + 1 = 3 * (3^j * 2^m) - 2
  have hprod := hpos
  have h3prod : 3 * (3^j * 2^m) ≥ 3 := Nat.mul_le_mul_left 3 hprod
  -- Use Nat.mul_sub for: 3 * (x - 1) = 3*x - 3
  have hsub : 3 * (3^j * 2^m - 1) = 3 * (3^j * 2^m) - 3 := by
    rw [Nat.mul_sub_one]
  rw [hsub]
  omega

/-- Atomic: 3^(j+1) * 2^m ≥ 2 when m ≥ 1 -/
lemma cf_ge_2 (j m : ℕ) (hm : 1 ≤ m) : 3^(j+1) * 2^m ≥ 2 := by
  have h3 : 3^(j+1) ≥ 1 := Nat.one_le_pow (j+1) 3 (by omega)
  have h2 : 2^m ≥ 2 := by
    calc 2^m ≥ 2^1 := Nat.pow_le_pow_right (by omega) hm
      _ = 2 := by norm_num
  calc 3^(j+1) * 2^m ≥ 1 * 2 := Nat.mul_le_mul h3 h2
    _ = 2 := by ring

/-- Atomic: 2^m = 2 * 2^(m-1) when m ≥ 1 -/
lemma pow2_split (m : ℕ) (hm : 1 ≤ m) : 2^m = 2 * 2^(m-1) := by
  conv_lhs => rw [← Nat.sub_add_cancel hm]
  ring

/-- Atomic: (3^(j+1) * 2^m - 2) / 2 = 3^(j+1) * 2^(m-1) - 1 -/
lemma cf_div2 (j m : ℕ) (hm : 1 ≤ m) :
    (3^(j+1) * 2^m - 2) / 2 = 3^(j+1) * 2^(m-1) - 1 := by
  have hge2 := cf_ge_2 j m hm
  have hpow := pow2_split m hm
  rw [hpow]
  -- (3^(j+1) * (2 * 2^(m-1)) - 2) / 2
  have h1 : 3^(j+1) * (2 * 2^(m-1)) = 2 * (3^(j+1) * 2^(m-1)) := by ring
  rw [h1]
  have hbase : 3^(j+1) * 2^(m-1) ≥ 1 := pow_prod_pos (j+1) (m-1)
  have h2 : 2 * (3^(j+1) * 2^(m-1)) - 2 = 2 * (3^(j+1) * 2^(m-1) - 1) := by omega
  rw [h2, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]

/-- The core recurrence: T(3^j * 2^m - 1) = 3^(j+1) * 2^(m-1) - 1 for m ≥ 1 -/
lemma T_closed_form (j m : ℕ) (hm : 1 ≤ m) :
    T (3^j * 2^m - 1) = 3^(j+1) * 2^(m-1) - 1 := by
  have hodd : (3^j * 2^m - 1) % 2 = 1 := closed_form_odd j m hm
  rw [T_odd _ hodd]
  have hpos := pow_prod_pos j m
  calc (3 * (3^j * 2^m - 1) + 1) / 2
      = (3^(j+1) * 2^m - 2) / 2 := by rw [cf_expand j m hpos]
    _ = 3^(j+1) * 2^(m-1) - 1 := cf_div2 j m hm

/-- Mersenne closed form: T^j(2^k - 1) = 3^j * 2^(k-j) - 1 for j ≤ k-1 -/
theorem mersenne_closed_form (j k : ℕ) (hj : j ≤ k - 1) (hk : 2 ≤ k) :
    trajectory (mersenne k) j = 3^j * 2^(k - j) - 1 := by
  induction j with
  | zero =>
    simp only [trajectory, mersenne, pow_zero, one_mul, Nat.sub_zero]
  | succ j' ih =>
    -- trajectory (mersenne k) (j' + 1) = T (trajectory (mersenne k) j')
    simp only [trajectory]
    -- By IH: trajectory (mersenne k) j' = 3^j' * 2^(k - j') - 1
    have hj' : j' ≤ k - 1 := by omega
    rw [ih hj']
    -- Now apply T_closed_form
    have hm : 1 ≤ k - j' := by omega
    have hexp : (k - j') - 1 = k - (j' + 1) := by omega
    rw [T_closed_form j' (k - j') hm, hexp]

-- =============================================================
-- PART 6: MERSENNE BAD CHAIN LENGTH
-- =============================================================

/-- Mersenne stays bad for j ≤ k - 2 -/
theorem mersenne_stays_bad (j k : ℕ) (hj : j ≤ k - 2) (hk : 2 ≤ k) :
    isBad (trajectory (mersenne k) j) = true := by
  rw [mersenne_closed_form j k (by omega) hk]
  apply closed_form_bad
  omega

-- =============================================================
-- ATOMIC LEMMAS FOR MERSENNE_BAD_CHAIN_EXACT
-- =============================================================

/-- Atomic: 3^j is always odd -/
lemma pow3_odd (j : ℕ) : 3^j % 2 = 1 := by
  induction j with
  | zero => simp
  | succ j' ih =>
    have hexp : 3^(j' + 1) = 3 * 3^j' := by rw [pow_succ, mul_comm]
    rw [hexp]
    omega

/-- Atomic: 3^j % 4 is either 1 or 3 (alternating) -/
lemma pow3_mod4 (j : ℕ) : 3^j % 4 = 1 ∨ 3^j % 4 = 3 := by
  induction j with
  | zero => left; rfl
  | succ j' ih =>
    have h3exp : 3^(j' + 1) = 3 * 3^j' := by rw [pow_succ, mul_comm]
    cases ih with
    | inl h1 =>
      right
      have hmul : (3 * 3^j') % 4 = (3 * (3^j' % 4)) % 4 := Nat.mul_mod 3 (3^j') 4
      rw [h3exp, hmul, h1]
    | inr h3 =>
      left
      have hmul : (3 * 3^j') % 4 = (3 * (3^j' % 4)) % 4 := Nat.mul_mod 3 (3^j') 4
      rw [h3exp, hmul, h3]

/-- Atomic: 2 * 3^j ≡ 2 (mod 4) -/
lemma two_times_pow3_mod4 (j : ℕ) : (2 * 3^j) % 4 = 2 := by
  have hmul : (2 * 3^j) % 4 = (2 * (3^j % 4)) % 4 := Nat.mul_mod 2 (3^j) 4
  cases pow3_mod4 j with
  | inl h1 => rw [hmul, h1]
  | inr h3 => rw [hmul, h3]

/-- Atomic: 2 * 3^j - 1 ≡ 1 (mod 4) -/
lemma two_times_pow3_minus1_mod4 (j : ℕ) : (2 * 3^j - 1) % 4 = 1 := by
  have h_mod := two_times_pow3_mod4 j
  have h3j_ge1 : 3^j ≥ 1 := Nat.one_le_pow j 3 (by omega)
  have h_ge2 : 2 * 3^j ≥ 2 := by omega
  omega

/-- Atomic: 2 * 3^j - 1 is odd -/
lemma two_times_pow3_minus1_odd (j : ℕ) : (2 * 3^j - 1) % 2 = 1 := by
  have h3j_ge1 : 3^j ≥ 1 := Nat.one_le_pow j 3 (by omega)
  omega

/-- Atomic: 3^j * 2 - 1 ≡ 1 (mod 4) -/
lemma pow3_times2_minus1_mod4 (j : ℕ) : (3^j * 2 - 1) % 4 = 1 := by
  -- 3^j * 2 = 2 * 3^j
  have h_comm : 3^j * 2 = 2 * 3^j := by ring
  rw [h_comm]
  exact two_times_pow3_minus1_mod4 j

/-- Atomic: At step k-1, Mersenne(k) trajectory exits bad class -/
lemma mersenne_exits_bad (k : ℕ) (hk : 2 ≤ k) :
    isBad (trajectory (mersenne k) (k - 1)) = false := by
  -- At step k-1, the closed form is 3^(k-1) * 2^1 - 1
  have hkm1 : k - 1 ≤ k - 1 := le_refl _
  rw [mersenne_closed_form (k - 1) k hkm1 hk]
  -- k - (k - 1) = 1
  have hexp : k - (k - 1) = 1 := by omega
  rw [hexp]
  simp only [pow_one]
  -- Now show 3^(k-1) * 2 - 1 is not bad (odd but ≢ 3 mod 4)
  -- isBad n = (n % 2 = 1 ∧ n % 4 = 3)
  -- We need to show this is false (as Bool)
  -- The key: (3^(k-1) * 2 - 1) % 4 = 1 ≠ 3
  have h_mod := pow3_times2_minus1_mod4 (k - 1)
  -- h_mod : (3^(k-1) * 2 - 1) % 4 = 1
  unfold isBad
  -- Goal: decide (... % 2 = 1) && decide (... % 4 = 3) = false
  -- Since ... % 4 = 1 ≠ 3, the second decide is false
  have hne : (3 ^ (k - 1) * 2 - 1) % 4 ≠ 3 := by rw [h_mod]; decide
  -- The goal is: decide (A ∧ B) = false
  -- We need to show ¬(A ∧ B), which follows from ¬B
  simp only [decide_eq_false_iff_not, not_and]
  intro _
  exact hne

/-- Atomic: trajectory (mersenne k) j > 1 for j < k and k ≥ 2 -/
lemma mersenne_traj_gt_one (j k : ℕ) (hj : j < k) (hk : 2 ≤ k) :
    1 < trajectory (mersenne k) j := by
  have hj' : j ≤ k - 1 := by omega
  rw [mersenne_closed_form j k hj' hk]
  have h3j : 3^j ≥ 1 := Nat.one_le_pow j 3 (by omega)
  have hkj_ge1 : k - j ≥ 1 := by omega
  have h2kj : 2^(k - j) ≥ 2 := by
    calc 2^(k - j) ≥ 2^1 := Nat.pow_le_pow_right (by omega) hkj_ge1
      _ = 2 := by norm_num
  have hprod : 3^j * 2^(k - j) ≥ 2 := by
    calc 3^j * 2^(k - j) ≥ 1 * 2 := Nat.mul_le_mul h3j h2kj
      _ = 2 := by ring
  -- 3^j * 2^(k-j) ≥ 2, so 3^j * 2^(k-j) - 1 ≥ 1, so > 1 needs ≥ 2
  -- Actually we need > 1, i.e., ≥ 2
  -- 3^j * 2^(k-j) - 1 ≥ 2 - 1 = 1, but we need strict >
  -- Since 3^j ≥ 1 and 2^(k-j) ≥ 2, product ≥ 2, so product - 1 ≥ 1
  -- For strict inequality: if 3^j * 2^(k-j) ≥ 3, then product - 1 ≥ 2 > 1
  -- When j = 0: 1 * 2^k ≥ 2^2 = 4 ≥ 3 ✓
  -- When j ≥ 1: 3^j ≥ 3, so product ≥ 3 * 2 = 6 ≥ 3 ✓
  have hprod_ge3 : 3^j * 2^(k - j) ≥ 3 := by
    cases j with
    | zero =>
      simp only [pow_zero, one_mul]
      have hk_sub : k - 0 = k := by omega
      rw [hk_sub]
      calc 2^k ≥ 2^2 := Nat.pow_le_pow_right (by omega) hk
        _ = 4 := by norm_num
        _ ≥ 3 := by omega
    | succ j' =>
      have h3j_ge3 : 3^(j' + 1) ≥ 3 := by
        calc 3^(j' + 1) ≥ 3^1 := Nat.pow_le_pow_right (by omega) (by omega)
          _ = 3 := by norm_num
      calc 3^(j' + 1) * 2^(k - (j' + 1)) ≥ 3 * 1 := Nat.mul_le_mul h3j_ge3 (Nat.one_le_pow _ 2 (by omega))
        _ = 3 := by ring
  omega

/-- Trajectory shift: trajectory (T n) i = trajectory n (i + 1) -/
lemma trajectory_shift (n i : ℕ) : trajectory (T n) i = trajectory n (i + 1) := by
  induction i with
  | zero => simp [trajectory]
  | succ i' ih =>
    -- trajectory (T n) (i' + 1) = T (trajectory (T n) i')
    -- By IH: = T (trajectory n (i' + 1))
    -- = trajectory n ((i' + 1) + 1) = trajectory n (i' + 2)
    calc trajectory (T n) (i' + 1)
        = T (trajectory (T n) i') := rfl
      _ = T (trajectory n (i' + 1)) := by rw [ih]
      _ = trajectory n ((i' + 1) + 1) := rfl

/--
**Helper: Bad chain length equals number of consecutive bad steps**

If trajectory is bad for steps 0 to j-1 and not bad at step j,
then badChainLength = j.
-/
lemma badChainLength_eq_bad_steps (n : ℕ) (j fuel : ℕ)
    (hfuel : fuel ≥ j + 1)
    (hn_gt1 : ∀ i, i ≤ j → 1 < trajectory n i)
    (h_bad : ∀ i, i < j → isBad (trajectory n i) = true)
    (h_exit : isBad (trajectory n j) = false) :
    badChainLength n fuel = j := by
  induction j generalizing n fuel with
  | zero =>
    -- j = 0: trajectory n 0 = n is not bad, so chain = 0
    cases fuel with
    | zero => omega
    | succ f =>
      simp only [badChainLength]
      have hn_gt : 1 < trajectory n 0 := hn_gt1 0 (le_refl 0)
      simp only [trajectory] at hn_gt
      have hnn : ¬(n ≤ 1) := by omega
      simp only [hnn, ↓reduceIte]
      -- h_exit says isBad (trajectory n 0) = isBad n = false
      simp only [trajectory] at h_exit
      simp only [h_exit, Bool.false_eq_true, ↓reduceIte]
  | succ j' ih =>
    -- j = j' + 1: n is bad, so chain = 1 + chain of T(n)
    cases fuel with
    | zero => omega
    | succ f =>
      have hfuel' : f ≥ j' + 1 := by omega
      have h_n_bad : isBad n = true := by
        have := h_bad 0 (by omega)
        simp only [trajectory] at this
        exact this
      have hn_gt : 1 < n := by
        have := hn_gt1 0 (by omega)
        simp only [trajectory] at this
        exact this
      rw [badChainLength_bad n hn_gt h_n_bad f]
      -- Now need: badChainLength (T n) f = j'
      -- Use trajectory_shift: trajectory (T n) i = trajectory n (i + 1)
      have h_Tn_gt1 : ∀ i, i ≤ j' → 1 < trajectory (T n) i := by
        intro i hi
        rw [trajectory_shift]
        exact hn_gt1 (i + 1) (by omega)
      have h_Tn_bad : ∀ i, i < j' → isBad (trajectory (T n) i) = true := by
        intro i hi
        rw [trajectory_shift]
        exact h_bad (i + 1) (by omega)
      have h_Tn_exit : isBad (trajectory (T n) j') = false := by
        rw [trajectory_shift]
        exact h_exit
      have h_ih := ih (T n) f hfuel' h_Tn_gt1 h_Tn_bad h_Tn_exit
      omega

/-- Bad chain of Mersenne(k) is exactly k-1 -/
theorem mersenne_bad_chain_exact (k : ℕ) (hk : 2 ≤ k) :
    badChainLength (mersenne k) (k + 5) = k - 1 := by
  -- Use the helper lemma with j = k - 1
  -- We need:
  -- 1. fuel ≥ (k-1) + 1 = k ✓ (we have k + 5 ≥ k)
  -- 2. trajectory values > 1 for i ≤ k-1 (by mersenne_traj_gt_one for i < k)
  -- 3. trajectory is bad for i < k-1 (by mersenne_stays_bad)
  -- 4. trajectory exits at i = k-1 (by mersenne_exits_bad)

  have hfuel : k + 5 ≥ (k - 1) + 1 := by omega

  have h_gt1 : ∀ i, i ≤ k - 1 → 1 < trajectory (mersenne k) i := by
    intro i hi
    exact mersenne_traj_gt_one i k (by omega) hk

  have h_bad : ∀ i, i < k - 1 → isBad (trajectory (mersenne k) i) = true := by
    intro i hi
    exact mersenne_stays_bad i k (by omega) hk

  have h_exit : isBad (trajectory (mersenne k) (k - 1)) = false :=
    mersenne_exits_bad k hk

  exact badChainLength_eq_bad_steps (mersenne k) (k - 1) (k + 5) hfuel h_gt1 h_bad h_exit

-- =============================================================
-- PART 7: THE BITWISE FORCING LEMMA (The Smoking Gun)
-- =============================================================

/-!
## The Key Structural Insight

If `badChainLength n fuel ≥ j`, then n must end in at least j+1 ones in binary.
Equivalently: n ≡ 2^(j+1) - 1 (mod 2^(j+1))

This is the "smoking gun" because:
1. Having j trailing 1-bits means n ≥ 2^j - 1
2. If n < 2^k, then n has at most k bits, so chain < k
3. Therefore Mersenne (all 1s) achieves the maximum
-/

/-- Chain ≥ 1 implies n is odd (ends in bit 1) -/
lemma chain_ge_1_implies_odd (n fuel : ℕ) (h : badChainLength n fuel ≥ 1) :
    n % 2 = 1 := by
  cases fuel with
  | zero => simp [badChainLength] at h
  | succ f =>
    simp only [badChainLength] at h
    by_cases hn : n ≤ 1
    · simp [hn] at h
    · simp only [hn, ↓reduceIte] at h
      by_cases hbad : isBad n = true
      · simp only [isBad, Bool.and_eq_true, decide_eq_true_eq] at hbad
        exact hbad.1
      · simp only [Bool.not_eq_true] at hbad
        simp [hbad] at h

/-- Chain ≥ 1 implies n ≡ 3 (mod 4) (ends in bits 11) -/
lemma chain_ge_1_implies_mod4 (n fuel : ℕ) (h : badChainLength n fuel ≥ 1) :
    n % 4 = 3 := by
  cases fuel with
  | zero => simp [badChainLength] at h
  | succ f =>
    simp only [badChainLength] at h
    by_cases hn : n ≤ 1
    · simp [hn] at h
    · simp only [hn, ↓reduceIte] at h
      by_cases hbad : isBad n = true
      · simp only [isBad, Bool.and_eq_true, decide_eq_true_eq] at hbad
        exact hbad.2
      · simp only [Bool.not_eq_true] at hbad
        simp [hbad] at h

/-- If chain ≥ j+1 and j ≥ 1, then chain of T(n) ≥ j -/
lemma chain_step (n fuel j : ℕ) (_hj : j ≥ 1)
    (h : badChainLength n (fuel + 1) ≥ j + 1) :
    badChainLength (T n) fuel ≥ j := by
  simp only [badChainLength] at h
  by_cases hn : n ≤ 1
  · simp only [hn, ↓reduceIte] at h; omega
  · simp only [hn, ↓reduceIte] at h
    by_cases hbad : isBad n = true
    · simp only [hbad, ↓reduceIte] at h
      omega
    · simp only [Bool.not_eq_true] at hbad
      simp only [hbad, Bool.false_eq_true, ↓reduceIte] at h
      -- h now says 0 ≥ j + 1 which is impossible for j ≥ 1
      omega

/--
**The Minimum Value Lemma**

If n ≡ 2^j - 1 (mod 2^j), then n ≥ 2^j - 1.
(Having j trailing 1-bits means minimum magnitude is 2^j - 1)
-/
lemma mod_eq_mersenne_implies_ge (n j : ℕ) (_hj : j ≥ 1) (h : n % 2^j = 2^j - 1) :
    n ≥ 2^j - 1 := by
  -- n = q * 2^j + (2^j - 1) for some q ≥ 0
  -- So n ≥ 2^j - 1
  have h2j_pos : 0 < 2^j := Nat.pos_pow_of_pos j (by omega)
  have : n % 2^j ≤ n := Nat.mod_le n (2^j)
  omega

/--
**The Forcing Lemma (Base Case)**

Chain ≥ 1 implies n ≡ 1 (mod 2) and n ≡ 3 (mod 4).
Combined: n ends in bits "11" (at least 2 trailing ones).
-/
lemma chain_forces_trailing_ones_base (n fuel : ℕ) (h : badChainLength n fuel ≥ 1) :
    n % 4 = 3 := chain_ge_1_implies_mod4 n fuel h

/-- If n ≡ 2^k - 1 (mod 2^k), then n ≥ 2^k - 1 -/
lemma mod_mersenne_lower_bound (n k : ℕ) (h : n % 2^k = 2^k - 1) :
    n ≥ 2^k - 1 := by
  have hmod_le : n % 2^k ≤ n := Nat.mod_le n (2^k)
  omega

/-- 3 is coprime to any power of 2 -/
lemma three_coprime_two_pow (k : ℕ) : Nat.Coprime 3 (2^k) := by
  unfold Nat.Coprime
  induction k with
  | zero => simp
  | succ k' ih =>
    have hpow : 2^(k' + 1) = 2 * 2^k' := by ring
    rw [hpow]
    calc Nat.gcd 3 (2 * 2^k') = Nat.gcd 3 (2^k' * 2) := by ring_nf
      _ = Nat.gcd 3 (2^k') := by
        have hc : Nat.Coprime 3 2 := by unfold Nat.Coprime; native_decide
        exact Nat.Coprime.gcd_mul_right_cancel_right (2^k') hc
      _ = 1 := ih

/--
**Modular Cancellation**: If 3a ≡ 3b (mod 2^k), then a ≡ b (mod 2^k)
This works because gcd(3, 2^k) = 1.
-/
lemma cancel_three_mod_two_pow (a b k : ℕ) (h : (3 * a) % 2^k = (3 * b) % 2^k) :
    a % 2^k = b % 2^k := by
  have hcop : Nat.Coprime 3 (2^k) := three_coprime_two_pow k
  -- Nat.ModEq is defined as equality of remainders
  have hmod : 3 * a ≡ 3 * b [MOD 2^k] := h
  -- 3 is coprime to 2^k, so we can cancel it
  -- Using the fact that if gcd(c, n) = 1 and c*a ≡ c*b (mod n), then a ≡ b (mod n)
  have hgcd : (2^k).gcd 3 = 1 := Nat.Coprime.gcd_eq_one hcop.symm
  exact Nat.ModEq.cancel_left_of_coprime hgcd hmod

-- =============================================================
-- ATOMIC LEMMAS FOR LIFT_MOD_CONSTRAINT
-- =============================================================

/-- Atomic: If T(n) ≡ r (mod 2^m), then 2*T(n) ≡ 2r (mod 2^(m+1)) -/
lemma double_mod_lift (t m r : ℕ) (h : t % 2^m = r) :
    (2 * t) % 2^(m + 1) = 2 * r := by
  -- t = q * 2^m + r for some q
  -- 2 * t = 2q * 2^m + 2r = q * 2^(m+1) + 2r
  have hpow : 2^(m + 1) = 2 * 2^m := by ring
  have h2m_pos : 0 < 2^m := Nat.pos_pow_of_pos m (by omega)
  have hr_bound : r < 2^m := by
    have : t % 2^m < 2^m := Nat.mod_lt t h2m_pos
    rw [h] at this
    exact this
  have h2r_bound : 2 * r < 2^(m + 1) := by rw [hpow]; omega
  -- t = q * 2^m + r
  have hdiv_mod := Nat.div_add_mod t (2^m)
  -- 2 * t = 2 * (q * 2^m + r) = 2*q*2^m + 2r = q * 2^(m+1) + 2r
  have h_calc : 2 * t = 2 * r + (t / 2^m) * 2^(m+1) := by
    calc 2 * t = 2 * (2^m * (t / 2^m) + t % 2^m) := by rw [hdiv_mod]
      _ = 2 * 2^m * (t / 2^m) + 2 * (t % 2^m) := by ring
      _ = 2^(m+1) * (t / 2^m) + 2 * r := by rw [← hpow, h]
      _ = 2 * r + (t / 2^m) * 2^(m+1) := by ring
  rw [h_calc, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h2r_bound]

/-- Atomic: 2 * (2^m - 1) = 2^(m+1) - 2 when m ≥ 1 -/
lemma double_mersenne (m : ℕ) (hm : 1 ≤ m) : 2 * (2^m - 1) = 2^(m + 1) - 2 := by
  have h2m_pos : 2^m ≥ 1 := Nat.one_le_pow m 2 (by omega)
  have hpow : 2^(m + 1) = 2 * 2^m := by ring
  omega

/-- Atomic: 3 * (2^(m+1) - 1) = 3 * 2^(m+1) - 3 -/
lemma three_times_mersenne (m : ℕ) : 3 * (2^(m + 1) - 1) = 3 * 2^(m + 1) - 3 := by
  have h : 2^(m + 1) ≥ 1 := Nat.one_le_pow (m + 1) 2 (by omega)
  omega

/-- Atomic: If 3n ≡ 3 * (2^k - 1) (mod 2^k), then n ≡ 2^k - 1 (mod 2^k) -/
lemma cancel_three_mersenne (n k : ℕ) (h : (3 * n) % 2^k = (3 * (2^k - 1)) % 2^k) :
    n % 2^k = 2^k - 1 := by
  -- 3 * (2^k - 1) = 3 * 2^k - 3 ≡ -3 (mod 2^k)
  -- If 3n ≡ -3 (mod 2^k), then since gcd(3, 2^k) = 1, n ≡ -1 (mod 2^k)
  have hcop : Nat.Coprime 3 (2^k) := three_coprime_two_pow k
  have heq := cancel_three_mod_two_pow n (2^k - 1) k h
  -- heq: n % 2^k = (2^k - 1) % 2^k
  -- We need: n % 2^k = 2^k - 1
  -- This follows since (2^k - 1) < 2^k, so (2^k - 1) % 2^k = 2^k - 1
  have h2k_pos : 0 < 2^k := Nat.pos_pow_of_pos k (by omega)
  have h_mers_bound : 2^k - 1 < 2^k := by omega
  have h_mers_mod : (2^k - 1) % 2^k = 2^k - 1 := Nat.mod_eq_of_lt h_mers_bound
  rw [h_mers_mod] at heq
  exact heq

/--
**The Algebraic Lift Lemma**

If T(n) ≡ -1 (mod 2^m) and n is odd, then n ≡ -1 (mod 2^(m+1)).

This is the key insight: bad chain membership propagates bit constraints upward.

Proof:
- T(n) = (3n + 1) / 2 for odd n
- If T(n) ≡ -1 (mod 2^m), then 2*T(n) ≡ -2 (mod 2^(m+1))
- So 3n + 1 ≡ -2 (mod 2^(m+1))
- Thus 3n ≡ -3 (mod 2^(m+1))
- Since gcd(3, 2^(m+1)) = 1, we can cancel: n ≡ -1 (mod 2^(m+1))
-/
lemma lift_mod_constraint (n m : ℕ) (hm : 1 ≤ m) (hodd : n % 2 = 1)
    (hT : T n % 2^m = 2^m - 1) :
    n % 2^(m + 1) = 2^(m + 1) - 1 := by
  -- Step 1: T(n) = (3n + 1) / 2 for odd n
  have hT_def : T n = (3 * n + 1) / 2 := T_odd n hodd

  -- Step 2: 2 * T(n) = 3n + 1 (since 3n + 1 is even for odd n)
  have heven : (3 * n + 1) % 2 = 0 := by omega
  have hdiv : 2 * T n = 3 * n + 1 := by
    rw [hT_def]
    exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero heven)

  -- Step 3: Use double_mod_lift to get (2 * T n) % 2^(m+1) = 2 * (2^m - 1)
  have h2T_mod : (2 * T n) % 2^(m + 1) = 2 * (2^m - 1) := double_mod_lift (T n) m (2^m - 1) hT

  -- Step 4: Simplify 2 * (2^m - 1) = 2^(m+1) - 2
  have h_double : 2 * (2^m - 1) = 2^(m + 1) - 2 := double_mersenne m hm

  -- Step 5: So (3n + 1) % 2^(m+1) = 2^(m+1) - 2
  have h3n1_mod : (3 * n + 1) % 2^(m + 1) = 2^(m + 1) - 2 := by
    rw [← hdiv, h2T_mod, h_double]

  -- Step 6: Therefore (3n) % 2^(m+1) = 2^(m+1) - 3
  have h2m1_pos : 0 < 2^(m + 1) := Nat.pos_pow_of_pos (m + 1) (by omega)
  have h2m1_ge3 : 2^(m + 1) ≥ 3 := by
    calc 2^(m + 1) = 2 * 2^m := by ring
      _ ≥ 2 * 2^1 := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by omega) hm)
      _ = 4 := by ring
      _ ≥ 3 := by omega

  have h3n_mod : (3 * n) % 2^(m + 1) = 2^(m + 1) - 3 := by
    -- (3n + 1) % 2^(m+1) = 2^(m+1) - 2
    -- So (3n) % 2^(m+1) = 2^(m+1) - 3 (subtracting 1, with wrap-around handling)
    have h_eq : (3 * n + 1) % 2^(m + 1) = 2^(m + 1) - 2 := h3n1_mod
    have h_bound : 2^(m + 1) - 3 < 2^(m + 1) := by omega
    -- (3n + 1) = q * 2^(m+1) + (2^(m+1) - 2) for some q
    have hdiv_eq : 3 * n + 1 = 2^(m+1) * ((3 * n + 1) / 2^(m+1)) + (2^(m+1) - 2) := by
      have := Nat.div_add_mod (3 * n + 1) (2^(m+1))
      rw [h_eq] at this
      linarith
    -- So 3n = q * 2^(m+1) + (2^(m+1) - 3)
    have h3n_eq : 3 * n = 2^(m+1) * ((3 * n + 1) / 2^(m+1)) + (2^(m+1) - 3) := by omega
    rw [h3n_eq, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod,
        Nat.mod_eq_of_lt h_bound]

  -- Step 7: Use cancel_three to get n % 2^(m+1) = 2^(m+1) - 1
  -- 3n ≡ 2^(m+1) - 3 (mod 2^(m+1))
  -- 3 * (2^(m+1) - 1) = 3 * 2^(m+1) - 3 ≡ -3 ≡ 2^(m+1) - 3 (mod 2^(m+1))
  have h_three_mers : (3 * (2^(m + 1) - 1)) % 2^(m + 1) = 2^(m + 1) - 3 := by
    have hge : 2^(m + 1) ≥ 1 := Nat.one_le_pow (m + 1) 2 (by omega)
    have h3mers : 3 * (2^(m + 1) - 1) = 3 * 2^(m + 1) - 3 := by omega
    rw [h3mers]
    -- 3 * 2^(m+1) - 3 = 2^(m+1) * 3 - 3, and 3 * 2^(m+1) ≥ 3
    have h_val : 3 * 2^(m + 1) - 3 = 2^(m+1) * 2 + (2^(m+1) - 3) := by omega
    rw [h_val, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod]
    have hfinal : 2^(m + 1) - 3 < 2^(m + 1) := by omega
    exact Nat.mod_eq_of_lt hfinal

  have h3n_matches : (3 * n) % 2^(m + 1) = (3 * (2^(m + 1) - 1)) % 2^(m + 1) := by
    rw [h3n_mod, h_three_mers]

  exact cancel_three_mersenne n (m + 1) h3n_matches

/--
**Bitwise Forcing: Chain ≥ j+1 implies n has j+2 trailing 1-bits**

Formally: badChainLength n fuel ≥ j+1 → n % 2^(j+2) = 2^(j+2) - 1

This is the "smoking gun" proof that bounds are structural.
The key insight: each bad step in the chain requires specific bit patterns.

Proof by induction on j:
- Base (j=0): chain ≥ 1 implies isBad(n), so n ≡ 3 (mod 4) = 2^2 - 1
- Step: If chain ≥ j+2, then chain of T(n) ≥ j+1.
  By IH, T(n) ≡ -1 (mod 2^(j+2)).
  Working backwards: n ≡ -1 (mod 2^(j+3)).
-/
theorem bad_chain_forces_bits (n j fuel : ℕ) (_hfuel : fuel ≥ j + 1)
    (h_chain : badChainLength n fuel ≥ j + 1) :
    n % 2^(j+2) = 2^(j+2) - 1 := by
  induction j generalizing n fuel with
  | zero =>
    -- j = 0: need n % 4 = 3
    have h_ge_1 : badChainLength n fuel ≥ 1 := by omega
    exact chain_ge_1_implies_mod4 n fuel h_ge_1
  | succ j' ih =>
    -- j = j' + 1
    -- Need: chain ≥ j'+2 → n % 2^(j'+3) = 2^(j'+3) - 1

    -- First, chain ≥ 1 gives n is odd
    have h_ge_1 : badChainLength n fuel ≥ 1 := by omega
    have hodd := chain_ge_1_implies_odd n fuel h_ge_1

    -- Chain ≥ j'+2 ≥ 2, so we need fuel ≥ 2 for chain_step
    have hfuel_ge_2 : fuel ≥ 2 := by omega

    -- Get chain of T(n) ≥ j'+1 using chain_step
    -- chain_step needs fuel in form (fuel' + 1) for the recursion
    obtain ⟨fuel', hfuel'⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
    rw [hfuel'] at h_chain

    have h_Tn_chain : badChainLength (T n) fuel' ≥ j' + 1 := by
      have := chain_step n fuel' (j' + 1) (by omega) h_chain
      omega

    -- By IH on T(n): T(n) % 2^(j'+2) = 2^(j'+2) - 1
    have hfuel'_ge : fuel' ≥ j' + 1 := by omega
    have hT_mod := ih (T n) fuel' hfuel'_ge h_Tn_chain

    -- Now apply the algebraic lift: lift_mod_constraint
    -- lift_mod_constraint needs: m ≥ 1, n odd, T n % 2^m = 2^m - 1
    -- We have m = j' + 2, which is ≥ 1
    -- Result: n % 2^(m+1) = 2^(m+1) - 1, i.e., n % 2^(j'+3) = 2^(j'+3) - 1
    have hm_ge_1 : j' + 2 ≥ 1 := by omega
    have hlift := lift_mod_constraint n (j' + 2) hm_ge_1 hodd hT_mod
    -- hlift: n % 2^((j'+2) + 1) = 2^((j'+2) + 1) - 1
    -- Goal: n % 2^((j' + 1) + 2) = 2^((j' + 1) + 2) - 1
    -- Since (j'+1)+2 = j'+3 = (j'+2)+1, these are the same
    have heq : (j' + 1) + 2 = (j' + 2) + 1 := by omega
    simp only [heq]
    exact hlift

-- =============================================================
-- PART 8: DOMINANCE THEOREM
-- =============================================================

/--
**Mersenne Dominance Theorem**

All n in [2^(k-1), 2^k) have bad chain ≤ k-1.

Proof by contradiction:
1. Assume chain ≥ k
2. By forcing lemma (with appropriate indexing): n % 2^k = 2^k - 1
3. Since n < 2^k, this means n = 2^k - 1 (Mersenne number)
4. But Mersenne(k) has chain exactly k-1 (verified computationally)
5. Contradiction: k - 1 ≥ k is false
-/
theorem mersenne_dominates (n k : ℕ) (hn_lo : 2^(k-1) ≤ n) (hn_hi : n < 2^k) (hk : 2 ≤ k) :
    badChainLength n (k + 5) ≤ k - 1 := by
  -- Proof by contradiction
  by_contra h_contra
  push_neg at h_contra
  -- h_contra: k - 1 < badChainLength n (k + 5)
  -- This means badChainLength n (k + 5) ≥ k

  have h_chain_ge : badChainLength n (k + 5) ≥ k := by omega
  have h_fuel_ge : k + 5 ≥ k := by omega

  -- We use the forcing lemma to get a contradiction
  -- chain ≥ k means chain ≥ (k-1) + 1
  -- By forcing: n % 2^((k-1)+2) = 2^((k-1)+2) - 1 = 2^(k+1) - 1

  -- Apply bad_chain_forces_bits with j = k - 1
  -- Requires: chain ≥ j + 1 = k, fuel ≥ j + 1 = k
  have hj : k - 1 + 1 = k := by omega
  have h_chain_j : badChainLength n (k + 5) ≥ (k - 1) + 1 := by omega
  have hfuel_j : k + 5 ≥ (k - 1) + 1 := by omega

  have h_forcing := bad_chain_forces_bits n (k - 1) (k + 5) hfuel_j h_chain_j
  -- h_forcing: n % 2^((k-1)+2) = 2^((k-1)+2) - 1
  -- i.e., n % 2^(k+1) = 2^(k+1) - 1

  have hexp : (k - 1) + 2 = k + 1 := by omega
  rw [hexp] at h_forcing

  -- From h_forcing, n ≥ 2^(k+1) - 1 by mod_mersenne_lower_bound
  have h_lower := mod_mersenne_lower_bound n (k + 1) h_forcing

  -- But 2^(k+1) - 1 ≥ 2^k for k ≥ 1
  have h_pow : 2^(k+1) - 1 ≥ 2^k := by
    have : 2^(k+1) = 2 * 2^k := by ring
    omega

  -- So n ≥ 2^k, contradicting n < 2^k
  omega

-- =============================================================
-- PART 8: THE BAD CHAIN BOUND
-- =============================================================

/-- log₂(n) is positive for n > 1 -/
lemma log2_pos_of_gt_one (n : ℕ) (hn : 1 < n) : 1 ≤ Nat.log2 n := by
  have hne : n ≠ 0 := by omega
  by_contra hcontra
  push_neg at hcontra
  have h0 : Nat.log2 n = 0 := Nat.lt_one_iff.mp hcontra
  have hlt : n < 2 := by
    have h' := @Nat.log2_lt n 1 hne
    have : Nat.log2 n < 1 := by rw [h0]; exact Nat.zero_lt_one
    rw [h'] at this
    simpa using this
  omega

/-- n < 2^(log₂(n) + 1) -/
lemma log2_upper (n : ℕ) (hne : n ≠ 0) : n < 2^(Nat.log2 n + 1) := by
  rw [← Nat.log2_lt hne]
  exact Nat.lt_succ_self _

/-- 2^(log₂(n)) ≤ n -/
lemma log2_lower (n : ℕ) (hne : n ≠ 0) : 2^(Nat.log2 n) ≤ n :=
  Nat.log2_self_le hne

/-- Bad chain bound: badChainLength(n) ≤ log₂(n) + 1 -/
theorem bad_chain_bound (n : ℕ) (hn : 1 < n) :
    badChainLength n (Nat.log2 n + 10) ≤ Nat.log2 n + 1 := by
  have hne : n ≠ 0 := by omega
  have hpos := log2_pos_of_gt_one n hn
  have hlo := log2_lower n hne
  have hhi := log2_upper n hne
  let k := Nat.log2 n + 1
  have hk : 2 ≤ k := by omega
  have hlo' : 2^(k-1) ≤ n := by
    have : k - 1 = Nat.log2 n := by omega
    rw [this]; exact hlo
  have hhi' : n < 2^k := hhi
  have hdom := mersenne_dominates n k hlo' hhi' hk
  -- Now connect fuel: k + 5 vs Nat.log2 n + 10
  have hfuel_ge : k + 5 ≤ Nat.log2 n + 10 := by omega
  -- Chain terminates in at most k-1 steps
  have hterm : badChainLength n (k + 5) < k + 5 := by
    calc badChainLength n (k + 5) ≤ k - 1 := hdom
      _ < k + 5 := by omega
  have heq := badChainLength_stable n (k + 5) (Nat.log2 n + 10) hfuel_ge hterm
  calc badChainLength n (Nat.log2 n + 10)
      = badChainLength n (k + 5) := heq
    _ ≤ k - 1 := hdom
    _ = Nat.log2 n := by omega
    _ ≤ Nat.log2 n + 1 := by omega

end MersenneProofs
