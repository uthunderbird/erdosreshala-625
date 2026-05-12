import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Erdos625.PartBAlphaMinusTwoFirstMomentAxiom

/-!
# Part B `(α − 2)` first-moment → threshold-witness bridge (non-circular)

This file exposes the proved Nat-side bridge

```
∃ n₀, ∀ n ≥ n₀,
  kThresholdAlphaMinusOne n + ⌈n / log² n⌉ ≤ kThresholdAlphaMinus2 n
```

derived non-circularly from the narrower first-moment-below-one axiom
`partB_alphaMinusTwo_firstMomentBelowOne_source` (in
`PartBAlphaMinusTwoFirstMomentAxiom.lean`) via the `Nat.find` definition of
`firstMomentThreshold`.

Sitting strictly **below** `CrossingPartB.lean` and `CumulantAlphaMinusTwo.lean`
in the import DAG, this module lets `CumulantAlphaMinusTwo.lean` derive its
`KThresholdGapSource`-shaped cumulant-gap proposition as a `theorem` rather
than as an axiom — discharging the threshold-gap statement from the narrower
first-moment-`<1` paper-axiom without circularity.

This is the same proof that `PartBAlphaMinusTwoFirstMoment.lean` previously
contained inline; that file now `exact`s the theorem proved here (so no
mathematical content is duplicated).
-/

namespace Problem625

open Real

noncomputable section

/-- **Nat-side threshold-witness bridge (proved, non-circular).**

For all sufficiently large `n`,
`kThresholdAlphaMinusOne n + ⌈n / log² n⌉ ≤ kThresholdAlphaMinus2 n`.

Derived from `partB_alphaMinusTwo_firstMomentBelowOne_source` (R2B Step 3.2
narrowed paper-axiom) via the `Nat.find` definition of `firstMomentThreshold`.
Does **not** use `kThresholdGapSource` /
`partB_alphaMinusTwo_cumulant_gap_source` (no circularity). -/
theorem kThresholdAlphaMinusOne_add_ceil_n_div_logsq_le_kThresholdAlphaMinus2 :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      kThresholdAlphaMinusOne n + ⌈(n : ℝ) / Real.log n ^ 2⌉₊ ≤
        kThresholdAlphaMinus2 n := by
  obtain ⟨n₀, hsrc⟩ := partB_alphaMinusTwo_firstMomentBelowOne_source
  refine ⟨n₀, fun n hn => ?_⟩
  set K : ℕ := kThresholdAlphaMinusOne n + ⌈(n : ℝ) / Real.log n ^ 2⌉₊ with hK_def
  have hlt : ∀ k : ℕ, k < K →
      expectedTBoundedColorings n k (kThresholdAlphaMinus2Level n) < 1 := hsrc n hn
  have hnot : ∀ k : ℕ, k < K →
      ¬ ((1 : ℝ) ≤ expectedTBoundedColorings n k (kThresholdAlphaMinus2Level n)) := by
    intro k hk hge
    exact (lt_irrefl (1 : ℝ)) (lt_of_le_of_lt hge (hlt k hk))
  have hle_find : K ≤ Nat.find (fmtExists n (kThresholdAlphaMinus2Level n)
      (kThresholdAlphaMinus2Level_pos n)) :=
    Nat.le_find_iff _ _ |>.mpr (by intro m hm; exact hnot m hm)
  have hK_le : K ≤ kThresholdAlphaMinus2 n := by
    simpa [kThresholdAlphaMinus2, firstMomentThreshold] using hle_find
  exact hK_le

end

end Problem625
