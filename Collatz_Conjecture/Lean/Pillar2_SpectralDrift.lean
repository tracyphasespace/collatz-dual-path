-- Pillar2_SpectralDrift.lean
-- Spectral gap analysis: geometric drift is negative

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section

namespace SpectralDrift

open Real

/-- Net drift per T-E cycle: log(3/2) + log(1/2) = log(3/4) -/
def net_drift : ℝ := log (3/2) + log (1/2)

/-- Spectral gap: |log(1/2)| - |log(3/2)| -/
def spectral_gap : ℝ := log 2 - log (3/2)

/-- Log of expansion factor -/
def log_T : ℝ := log (3/2)

/-- Log of contraction factor -/
def log_E : ℝ := log (1/2)

/-- log(2) > 0 -/
lemma log2_pos : 0 < log 2 := log_pos (by norm_num : (1 : ℝ) < 2)

/-- log(3/2) > 0 -/
lemma log_three_half_pos : 0 < log (3/2) := log_pos (by norm_num : (1 : ℝ) < 3/2)

/-- log(3/2) < log(2) -/
lemma log_three_half_lt_log2 : log (3/2) < log 2 := by
  apply log_lt_log
  · norm_num
  · norm_num

/-- Spectral gap is positive: contraction dominates expansion -/
theorem spectral_gap_pos : spectral_gap > 0 := by
  unfold spectral_gap
  have h := log_three_half_lt_log2
  linarith

/-- Net drift is negative: system loses energy on average -/
theorem net_drift_neg : net_drift < 0 := by
  unfold net_drift
  have h : log (3/2) + log (1/2) = log ((3/2) * (1/2)) := by
    rw [← log_mul (by norm_num) (by norm_num)]
  rw [h]
  have h2 : (3:ℝ)/2 * (1/2) = 3/4 := by norm_num
  rw [h2]
  exact log_neg (by norm_num) (by norm_num)

/-- Ratchet asymmetry: |log_E| > |log_T| -/
theorem ratchet_favors_descent : |log_E| > |log_T| := by
  unfold log_E log_T
  have hE : log (1/2) = -log 2 := by rw [one_div, log_inv]
  have hE_neg : log (1/2) < 0 := by rw [hE]; exact neg_neg_of_pos log2_pos
  have hT_pos : log (3/2) > 0 := log_three_half_pos
  rw [abs_of_neg hE_neg, abs_of_pos hT_pos, hE, neg_neg]
  exact log_three_half_lt_log2

/-- Average drift under 50/50 parity: 0.5*log(3/2) + 0.5*log(1/2) ≈ -0.14 -/
def average_drift : ℝ := 0.5 * log (3/2) + 0.5 * log (1/2)

/-- Average drift is negative -/
theorem average_drift_neg : average_drift < 0 := by
  unfold average_drift
  have h : 0.5 * log (3/2) + 0.5 * log (1/2) = 0.5 * (log (3/2) + log (1/2)) := by ring
  rw [h]
  have hsum : log (3/2) + log (1/2) < 0 := net_drift_neg
  linarith

end SpectralDrift
