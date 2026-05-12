import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Erdos625.PartBProfileBridge
import Erdos625.PartBAlphaMinusTwoFirstMomentAxiom
import Erdos625.PartBAlphaMinusTwoFirstMomentBridge

/-!
# Cumulant `(α − 2)` — R6 Direct Paper-Citation Front

This file is the **R6 direct paper-citation front** for the Part B threshold-gap
proposition at level `(α − 2)`.  It exposes a single non-derivative axiom that
asserts the gap

```
∃ n₀, ∀ n ≥ n₀,  n / log² n  ≤  kThresholdAlphaMinus2 n − kThresholdAlphaMinusOne n
```

directly as a paper citation, without routing through the intermediate
first-moment-below-one axiom in `CrossingPartB.lean`.

This is intentionally the *direct* front: there is no Lean-side derivation
between this axiom and the Part B threshold-gap.  The citation is the gap itself.

The axiom is stated with the unfolded body (rather than referring to
`Problem625.KThresholdGapSource`) so that this file can sit *below*
`CrossingPartB.lean` in the import DAG and be consumed by it.
-/

namespace Problem625

open Real

noncomputable section

/-! ## Historical note (axiom → theorem, 2026-05-11)

The declaration below was originally a single load-bearing axiom
`partB_alphaMinusTwo_cumulant_gap_source : KThresholdGapSource` citing
Heckel–Panagiotou, *Colouring random graphs: Tame colourings*,
arXiv:2306.07253 (2023), **Lemma 8.1** at level `(α − 2)`.

It has been **discharged on the Lean side** as a `theorem` whose proof routes
through the Nat-side bridge
`Problem625.kThresholdAlphaMinusOne_add_ceil_n_div_logsq_le_kThresholdAlphaMinus2`
(in `PartBAlphaMinusTwoFirstMomentBridge.lean`), which in turn derives the
threshold-gap from the **narrower** first-moment-`<1` paper-axiom
`Problem625.partB_alphaMinusTwo_firstMomentBelowOne_source`
(in `PartBAlphaMinusTwoFirstMomentAxiom.lean`) via the `Nat.find` definition
of `firstMomentThreshold`.  No circular reference to `kThresholdGapSource`. -/

/-- **Proved (R2B Step 3.2 discharge).**

Derived non-circularly from the narrower first-moment-`<1` paper-axiom
`partB_alphaMinusTwo_firstMomentBelowOne_source` via the Nat-side bridge
`kThresholdAlphaMinusOne_add_ceil_n_div_logsq_le_kThresholdAlphaMinus2`
(in `PartBAlphaMinusTwoFirstMomentBridge.lean`), combined with
`Nat.le_ceil : x ≤ ⌈x⌉₊`. No circular reference to `kThresholdGapSource`. -/
theorem partB_alphaMinusTwo_cumulant_gap_source :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      (n : ℝ) / Real.log n ^ 2 ≤
        (kThresholdAlphaMinus2 n : ℝ) - (kThresholdAlphaMinusOne n : ℝ) := by
  obtain ⟨n₀, hbridge⟩ :=
    kThresholdAlphaMinusOne_add_ceil_n_div_logsq_le_kThresholdAlphaMinus2
  refine ⟨n₀, fun n hn => ?_⟩
  have hNat : kThresholdAlphaMinusOne n + ⌈(n : ℝ) / Real.log n ^ 2⌉₊ ≤
      kThresholdAlphaMinus2 n := hbridge n hn
  -- Cast to ℝ.
  have hReal : (kThresholdAlphaMinusOne n : ℝ) +
      ((⌈(n : ℝ) / Real.log n ^ 2⌉₊ : ℕ) : ℝ) ≤
        (kThresholdAlphaMinus2 n : ℝ) := by
    exact_mod_cast hNat
  have hceil : (n : ℝ) / Real.log n ^ 2 ≤
      ((⌈(n : ℝ) / Real.log n ^ 2⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  linarith

end

end Problem625
