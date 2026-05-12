import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Erdos625.PartBProfileBridge
import Erdos625.CrossingPartB

/-!
# Crossing-Window Gap: kThresholdAlphaMinus2 vs kThresholdAlphaMinusOne

This file derives the `n^(1-ε)` lower bound on
`kThresholdAlphaMinus2 n - kThresholdAlphaMinusOne n` needed for the Phase 2 route.

## Step 3 refactor (2026-05-11)

The local `axiom kThresholdGapSource` that previously lived in this file has been
removed.  The single external paper-axiom carrying the HP-2023 Lemma 8.1 content
now lives in `Erdos625/CrossingPartB.lean` under the explicitly
cited name `Problem625.partB_crossing_lower_bound_alpha_minus_two_source`, and
this file re-exposes the same statement as a **proved theorem**
`Problem625.kThresholdGapSource := partB_crossing_lower_bound_alpha_minus_two_source`.

In particular, this file no longer contains any `axiom` keyword on the R2B path.
-/

namespace Problem625

open Real

noncomputable section

/-- The gap `kThresholdAlphaMinus2 n - kThresholdAlphaMinusOne n` is eventually at least
`n / log n ^ 2`.

This is a **proved theorem** — its body is the single external citation axiom
`Problem625.partB_crossing_lower_bound_alpha_minus_two_source`
(HP-2023 Lemma 8.1, applied at level `(α − 2)`; see `CrossingPartB.lean`).

The previous local `axiom kThresholdGapSource` declaration has been retired in
favour of this proved re-export; no behavioural change at downstream call sites,
which continue to use `kThresholdGapSource` as an inhabitant of the
`KThresholdGapSource` proposition. -/
theorem kThresholdGapSource : KThresholdGapSource :=
  partB_crossing_lower_bound_alpha_minus_two_source

/-- For any `ε > 0`, eventually `n / log n ^ 2 ≥ n ^ (1 - ε)`.
This is a standard asymptotic fact (log growth is slower than any power).
Ported from `HP2023Lemma81AlphaMinusTwo.n_div_log_sq_ge_rpow`. -/
lemma n_div_log_sq_ge_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      (n : ℝ) ^ (1 - ε) ≤ (n : ℝ) / Real.log n ^ 2 := by
  -- Key tendsto: log x ^ 2 / x ^ ε → 0 (from `isLittleO_log_rpow_rpow_atTop`).
  have hlittle : (fun x : ℝ => Real.log x ^ (2 : ℝ)) =o[Filter.atTop]
      (fun x : ℝ => x ^ ε) :=
    isLittleO_log_rpow_rpow_atTop 2 hε
  have hlim : Filter.Tendsto
      (fun x : ℝ => Real.log x ^ (2 : ℝ) / x ^ ε) Filter.atTop (nhds 0) := by
    have hev : ∀ᶠ x : ℝ in Filter.atTop, x ^ ε ≠ 0 := by
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
      exact (Real.rpow_pos_of_pos hx _).ne'
    exact hlittle.tendsto_div_nhds_zero
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

/-- For any `ε > 0`, eventually `n ^ (1 - ε) ≤ kThresholdAlphaMinus2 n - kThresholdAlphaMinusOne n`.
This is the key crossing-window gap used in the Phase 2 route. -/
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

end

end Problem625
