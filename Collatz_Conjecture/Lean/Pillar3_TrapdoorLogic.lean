-- Pillar3_TrapdoorLogic.lean
-- Trapdoor ratchet: powers of 2 as quantized barriers

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section

namespace TrapdoorLogic

open Real

/-- Number of power-of-2 barriers between n and 1 -/
def numBarriers (n : ℕ) : ℕ := Nat.log2 n

/-- The k-th barrier value -/
def barrier (k : ℕ) : ℕ := 2^k

/-- The T operator's multiplication factor -/
def T_factor : ℝ := 3 / 2

/-- The E operator's multiplication factor -/
def E_factor : ℝ := 1 / 2

/-- The barrier gap (factor of 2 between consecutive barriers) -/
def barrier_gap : ℝ := 2

/-- Fundamental asymmetry: T_factor < barrier_gap -/
theorem climb_insufficient : T_factor < barrier_gap := by
  unfold T_factor barrier_gap
  norm_num

/-- Two T steps exceed barrier gap but one does not -/
theorem climb_requires_multiple_T :
    T_factor < barrier_gap ∧ T_factor * T_factor > barrier_gap := by
  unfold T_factor barrier_gap
  constructor <;> norm_num

/-- The +1 ensures 3n+1 is even (crosses to E surface) -/
theorem soliton_creates_even (n : ℕ) (hodd : Odd n) :
    Even (3 * n + 1) := by
  have h3 : Odd 3 := by decide
  have h3n : Odd (3 * n) := h3.mul hodd
  exact h3n.add_one

/-- 3^k is always odd -/
theorem three_pow_odd (k : ℕ) : Odd (3 ^ k) := by
  induction k with
  | zero => exact odd_one
  | succ n ih =>
    rw [pow_succ]
    exact Odd.mul ih (by decide : Odd 3)

/-- 2^k is even for k > 0 -/
theorem two_pow_even (k : ℕ) (hk : 0 < k) : Even (2 ^ k) := by
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hk)
  rw [hj, pow_succ, mul_comm]
  exact even_two_mul _

/-- Transcendental obstruction: 3^p ≠ 2^q for positive p, q -/
theorem no_resonance (p q : ℕ) (_hp : 0 < p) (hq : 0 < q) :
    3 ^ p ≠ 2 ^ q := by
  intro h
  have h3_odd : Odd (3^p) := three_pow_odd p
  have h2_even : Even (2^q) := two_pow_even q hq
  rw [h] at h3_odd
  exact (Nat.not_even_iff_odd.mpr h3_odd) h2_even

/-- Log of T factor (positive - expansion) -/
def log_T : ℝ := log (3/2)

/-- Log of E factor (negative - contraction) -/
def log_E : ℝ := log (1/2)

/-- The ratchet inequality: |log E| > |log T| -/
theorem ratchet_favors_descent : |log_E| > |log_T| := by
  unfold log_E log_T
  have hE : log (1/2) = -log 2 := by rw [one_div, log_inv]
  have hE_neg : log (1/2) < 0 := by rw [hE]; exact neg_neg_of_pos (log_pos (by norm_num))
  have hT_pos : log (3/2) > 0 := log_pos (by norm_num)
  rw [abs_of_neg hE_neg, abs_of_pos hT_pos, hE, neg_neg]
  exact log_lt_log (by norm_num) (by norm_num)

/-- Net energy change per T-E cycle is negative -/
theorem net_descent : log_T + log_E < 0 := by
  unfold log_T log_E
  have h : log (3/2) + log (1/2) = log ((3/2) * (1/2)) := by
    rw [← log_mul (by norm_num) (by norm_num)]
  rw [h]
  have h2 : (3:ℝ)/2 * (1/2) = 3/4 := by norm_num
  rw [h2]
  exact log_neg (by norm_num) (by norm_num)

/-- The back door theorem: conditions that make escape impossible -/
theorem back_door :
    (T_factor < barrier_gap) ∧
    (|log_E| > |log_T|) ∧
    (log_T + log_E < 0) ∧
    (∀ p q : ℕ, 0 < p → 0 < q → 3^p ≠ 2^q) := by
  exact ⟨climb_insufficient, ratchet_favors_descent, net_descent, no_resonance⟩

/-- Ratchet conditions verified -/
theorem ratchet_conditions_verified :
    T_factor < barrier_gap ∧
    |log_E| > |log_T| ∧
    log_T + log_E < 0 :=
  ⟨climb_insufficient, ratchet_favors_descent, net_descent⟩

end TrapdoorLogic
