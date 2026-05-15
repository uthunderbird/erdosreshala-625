import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Erdos625.PartBProfileBridge
import Erdos625.CrossingPartB

/-!
# Crossing-Window Gap: kThresholdAlphaMinus2 vs kThresholdAlphaMinusOne

This file derives the `n^(1-ε)` lower bound on
`kThresholdAlphaMinus2 n - kThresholdAlphaMinusOne n` needed for the crossing-window
route, together with the softened-rate log-gap statement.
-/

namespace Problem625

open Real Filter

noncomputable section

/-- The gap `kThresholdAlphaMinus2 n - kThresholdAlphaMinusOne n` is eventually at least
`n / log n ^ 2`. Proved from `partB_crossing_lower_bound_alpha_minus_two_source`. -/
theorem kThresholdGapSource : KThresholdGapSource :=
  partB_crossing_lower_bound_alpha_minus_two_source

/-- For any `ε > 0`, eventually `n / log n ^ 2 ≥ n ^ (1 - ε)`. -/
lemma n_div_log_sq_ge_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      (n : ℝ) ^ (1 - ε) ≤ (n : ℝ) / Real.log n ^ 2 := by
  have hlittle : (fun x : ℝ => Real.log x ^ (2 : ℝ)) =o[atTop]
      (fun x : ℝ => x ^ ε) :=
    isLittleO_log_rpow_rpow_atTop 2 hε
  have hlim : Tendsto
      (fun x : ℝ => Real.log x ^ (2 : ℝ) / x ^ ε) atTop (nhds 0) :=
    hlittle.tendsto_div_nhds_zero
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨X, hX⟩ := hlim 1 (by norm_num)
  refine ⟨max ⌈X⌉₊ 3, fun n hn => ?_⟩
  have hn3 : 3 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn_ge_X : X ≤ (n : ℝ) := by
    have h1 : X ≤ (⌈X⌉₊ : ℝ) := Nat.le_ceil X
    have h2 : (⌈X⌉₊ : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (le_trans (Nat.le_max_left _ _) hn)
    linarith
  have hn_gt_one : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hlog_pos : 0 < Real.log n := Real.log_pos hn_gt_one
  have hxε_pos : 0 < (n : ℝ) ^ ε := Real.rpow_pos_of_pos hn_pos _
  have hX_bound := hX n hn_ge_X
  have hlog_rpow_eq : Real.log n ^ (2 : ℝ) = Real.log n ^ 2 := by
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  have hlog_sq_nn : 0 ≤ Real.log n ^ 2 := sq_nonneg _
  have hlog_sq_pos : 0 < Real.log n ^ 2 := by positivity
  have hquot_nn : 0 ≤ Real.log n ^ 2 / (n : ℝ) ^ ε := div_nonneg hlog_sq_nn hxε_pos.le
  have hX_lt : Real.log n ^ 2 / (n : ℝ) ^ ε < 1 := by
    have := hX_bound
    rw [Real.dist_eq, sub_zero, hlog_rpow_eq, abs_of_nonneg hquot_nn] at this
    exact this
  have hkey : Real.log n ^ 2 < (n : ℝ) ^ ε := (div_lt_one hxε_pos).mp hX_lt
  have hge : (n : ℝ) / (n : ℝ) ^ ε ≤ (n : ℝ) / Real.log n ^ 2 :=
    div_le_div_of_nonneg_left hn_pos.le hlog_sq_pos hkey.le
  have heq : (n : ℝ) / (n : ℝ) ^ ε = (n : ℝ) ^ (1 - ε) := by
    rw [sub_eq_add_neg, Real.rpow_add hn_pos, Real.rpow_one,
        Real.rpow_neg hn_pos.le, div_eq_mul_inv]
  linarith

/-- For any `ε > 0`, eventually `n ^ (1 - ε) ≤ kThresholdAlphaMinus2 n - kThresholdAlphaMinusOne n`. -/
lemma kThreshold_gap_alpha_minus_2 {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      (n : ℝ) ^ (1 - ε) ≤
        (kThresholdAlphaMinus2 n : ℝ) - (kThresholdAlphaMinusOne n : ℝ) := by
  obtain ⟨n₁, h₁⟩ := kThresholdGapSource
  obtain ⟨n₂, h₂⟩ := n_div_log_sq_ge_rpow hε
  refine ⟨max n₁ n₂, fun n hn => ?_⟩
  have hn1 : n₁ ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn2 : n₂ ≤ n := le_trans (Nat.le_max_right _ _) hn
  exact (h₂ n hn2).trans (h₁ n hn1)

/-- Softened-rate gap: eventually `Real.log n ≤ kThresholdAlphaMinus2 n − kThresholdAlphaMinusOne n`. -/
def KThresholdLogGapSource : Prop :=
  ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
    Real.log n ≤
      (kThresholdAlphaMinus2 n : ℝ) - (kThresholdAlphaMinusOne n : ℝ)

/-- Auxiliary asymptotic: eventually `Real.log n ≤ (n : ℝ) ^ (1 / 2 : ℝ)`. -/
private lemma log_le_rpow_half_eventually :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      Real.log n ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := by
  have hlittle : Real.log =o[atTop] (fun x : ℝ => x ^ ((1 : ℝ) / 2)) :=
    isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)
  have hbound : ∀ᶠ x : ℝ in atTop,
      ‖Real.log x‖ ≤ 1 * ‖x ^ ((1 : ℝ) / 2)‖ :=
    hlittle.bound (by norm_num : (0 : ℝ) < 1)
  rw [Filter.eventually_atTop] at hbound
  obtain ⟨X, hX⟩ := hbound
  refine ⟨max ⌈X⌉₊ 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn_ge_X : X ≤ (n : ℝ) := by
    have h1 : X ≤ (⌈X⌉₊ : ℝ) := Nat.le_ceil X
    have h2 : (⌈X⌉₊ : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (le_trans (Nat.le_max_left _ _) hn)
    linarith
  have hX_bound := hX (n : ℝ) hn_ge_X
  have hrpow_nn : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_nonneg hn_pos.le _
  have hnorm_rpow : ‖(n : ℝ) ^ ((1 : ℝ) / 2)‖ = (n : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.norm_of_nonneg hrpow_nn
  have hlog_le_abs : Real.log n ≤ |Real.log n| := le_abs_self _
  have hnorm_log : ‖Real.log n‖ = |Real.log n| := Real.norm_eq_abs _
  rw [hnorm_log, hnorm_rpow, one_mul] at hX_bound
  exact hlog_le_abs.trans hX_bound

/-- Softened-rate `(α − 2)` gap sublemma: eventually `log n ≤ kThresholdAlphaMinus2 n − kThresholdAlphaMinusOne n`.

Proof: from `kThreshold_gap_alpha_minus_2` at `ε = 1/2` we get `n^{1/2} ≤ gap` eventually;
combined with `log n ≤ n^{1/2}` eventually. -/
theorem kThreshold_alphaMinus2_log_gap : KThresholdLogGapSource := by
  obtain ⟨n₁, h₁⟩ := kThreshold_gap_alpha_minus_2
    (show (0 : ℝ) < 1 / 2 by norm_num)
  obtain ⟨n₂, h₂⟩ := log_le_rpow_half_eventually
  refine ⟨max n₁ n₂, fun n hn => ?_⟩
  have hn1 : n₁ ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn2 : n₂ ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hgap : (n : ℝ) ^ (1 - (1 / 2 : ℝ)) ≤
      (kThresholdAlphaMinus2 n : ℝ) - (kThresholdAlphaMinusOne n : ℝ) :=
    h₁ n hn1
  have hlog : Real.log n ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := h₂ n hn2
  have heq : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [heq] at hgap
  exact hlog.trans hgap

end

end Problem625
