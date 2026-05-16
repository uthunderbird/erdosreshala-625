import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Erdos625.PartBProfileBridge

/-!
# Crossing Part B — Deep-Crossing Residue Bridge

This file contains:
- The narrowed paper axiom `partB_alphaMinusTwo_firstMomentBelowOne_source`
  (HP-2023 Lemma 8.1 first-moment paragraph at level α−2)
- The Nat-side threshold-witness bridge (proved)
- The cumulant gap theorem `partB_alphaMinusTwo_cumulant_gap_source` (proved)
- The gap definition `KThresholdGapSource` and its proof `partB_crossing_lower_bound_alpha_minus_two_source`
- The paper axioms A3 and A4 for the crossing window
- Helper theorems for the first-moment multinomial decomposition

## Source

* Annika Heckel and Konstantinos Panagiotou. "Colouring random graphs: Tame colourings."
  arXiv:2306.07253 (2023). **Lemma 8.1**, applied at the `(α − 2)`-bounded level.
-/

namespace Problem625

open Real

noncomputable section

/-- **Narrowed paper-axiom: first-moment `< 1` window at level `(α − 2)`.**

States that for every `k` strictly below `kThresholdAlphaMinusOne n + ⌈n / log² n⌉`,
the expected number of `(α − 2)`-bounded ordered cochromatic `k`-colourings of
`G(n, 1/2)` is strictly less than `1`, eventually in `n`.

**Source (single citation).**
Heckel–Panagiotou, arXiv:2306.07253, **proof of Lemma 8.1**, first-moment
input paragraph, instantiated at level `(α − 2)` over a window of width
`⌈n / log² n⌉` above `kThresholdAlphaMinusOne n`. -/
axiom partB_alphaMinusTwo_firstMomentBelowOne_source :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      ∀ k : ℕ, k < kThresholdAlphaMinusOne n + ⌈(n : ℝ) / Real.log n ^ 2⌉₊ →
        expectedTBoundedColorings n k (kThresholdAlphaMinus2Level n) < 1

/-- **Nat-side threshold-witness bridge (proved).**

For all sufficiently large `n`,
`kThresholdAlphaMinusOne n + ⌈n / log² n⌉ ≤ kThresholdAlphaMinus2 n`.

Derived from `partB_alphaMinusTwo_firstMomentBelowOne_source` via the `Nat.find`
definition of `firstMomentThreshold`. -/
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

/-- **Proved (R2B Step 3.2 discharge).**

Derives `n / log² n ≤ kThresholdAlphaMinus2 n − kThresholdAlphaMinusOne n`
from `kThresholdAlphaMinusOne_add_ceil_n_div_logsq_le_kThresholdAlphaMinus2`
via `Nat.le_ceil`. -/
theorem partB_alphaMinusTwo_cumulant_gap_source :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      (n : ℝ) / Real.log n ^ 2 ≤
        (kThresholdAlphaMinus2 n : ℝ) - (kThresholdAlphaMinusOne n : ℝ) := by
  obtain ⟨n₀, hbridge⟩ :=
    kThresholdAlphaMinusOne_add_ceil_n_div_logsq_le_kThresholdAlphaMinus2
  refine ⟨n₀, fun n hn => ?_⟩
  have hNat : kThresholdAlphaMinusOne n + ⌈(n : ℝ) / Real.log n ^ 2⌉₊ ≤
      kThresholdAlphaMinus2 n := hbridge n hn
  have hReal : (kThresholdAlphaMinusOne n : ℝ) +
      ((⌈(n : ℝ) / Real.log n ^ 2⌉₊ : ℕ) : ℝ) ≤
        (kThresholdAlphaMinus2 n : ℝ) := by exact_mod_cast hNat
  have hceil : (n : ℝ) / Real.log n ^ 2 ≤
      ((⌈(n : ℝ) / Real.log n ^ 2⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  linarith

/-- The asymptotic gap `kThresholdAlphaMinus2 n − kThresholdAlphaMinusOne n ≥ n / log² n`,
phrased as a `Prop`. -/
def KThresholdGapSource : Prop :=
  ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
    (n : ℝ) / Real.log n ^ 2 ≤
      (kThresholdAlphaMinus2 n : ℝ) - (kThresholdAlphaMinusOne n : ℝ)

/-- Direct deterministic bridge from the exact threshold frontier to the
`n / log² n` threshold gap used downstream. -/
theorem KThresholdGapSource_of_eventual_thresholdGap
    (hgap :
      ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
        kThresholdAlphaMinusOne n + ⌈(n : ℝ) / Real.log n ^ 2⌉₊ ≤
          firstMomentThreshold n (kThresholdAlphaMinus2Level n)
            (kThresholdAlphaMinus2Level_pos n)) :
    KThresholdGapSource := by
  obtain ⟨n₀, hgap'⟩ := hgap
  refine ⟨n₀, fun n hn => ?_⟩
  have hNat : kThresholdAlphaMinusOne n + ⌈(n : ℝ) / Real.log n ^ 2⌉₊ ≤
      kThresholdAlphaMinus2 n := by
    simpa [kThresholdAlphaMinus2] using hgap' n hn
  have hReal : (kThresholdAlphaMinusOne n : ℝ) +
      ((⌈(n : ℝ) / Real.log n ^ 2⌉₊ : ℕ) : ℝ) ≤
        (kThresholdAlphaMinus2 n : ℝ) := by exact_mod_cast hNat
  have hceil : (n : ℝ) / Real.log n ^ 2 ≤
      ((⌈(n : ℝ) / Real.log n ^ 2⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  linarith

/-- The crossing lower bound, proved from `partB_alphaMinusTwo_cumulant_gap_source`. -/
theorem partB_crossing_lower_bound_alpha_minus_two_source : KThresholdGapSource :=
  partB_alphaMinusTwo_cumulant_gap_source

/-- Direct re-export of the gap as an existential. -/
theorem partB_crossing_lower_bound_alpha_minus_two :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      (n : ℝ) / Real.log n ^ 2 ≤
        (kThresholdAlphaMinus2 n : ℝ) - (kThresholdAlphaMinusOne n : ℝ) :=
  partB_crossing_lower_bound_alpha_minus_two_source

/-- **`(α − 2)`-bounded first-moment multinomial decomposition.**

The expected number of `(α − 2)`-bounded ordered cochromatic `k`-colourings equals
the sum of per-profile multinomial contributions. -/
theorem partB_alpha_minus_two_first_moment_multinomial_bound
    (n k : ℕ) :
    expectedTBoundedColorings n k (kThresholdAlphaMinus2Level n) =
      ∑ f ∈ coloringProfileFinset n k (kThresholdAlphaMinus2Level n),
        profileContribution n f :=
  expectedTBoundedColorings_eq_profileContribution_sum n k
    (kThresholdAlphaMinus2Level n)

/-- **Threshold-gap → first-moment-below-one bridge.**

If the witness gap is at or below the `(α − 2)`-level first-moment threshold,
then for every `k` below the gap, the expected count is `< 1`. -/
theorem partB_alphaMinusTwo_firstMomentBelowOne_of_thresholdGap
    (n : ℕ)
    (hgap : kThresholdAlphaMinusOne n + ⌈(n : ℝ) / Real.log n ^ 2⌉₊ ≤
              firstMomentThreshold n (kThresholdAlphaMinus2Level n)
                (kThresholdAlphaMinus2Level_pos n))
    {k : ℕ}
    (hk : k < kThresholdAlphaMinusOne n + ⌈(n : ℝ) / Real.log n ^ 2⌉₊) :
    expectedTBoundedColorings n k (kThresholdAlphaMinus2Level n) < 1 := by
  have hk' : k < firstMomentThreshold n (kThresholdAlphaMinus2Level n)
      (kThresholdAlphaMinus2Level_pos n) := lt_of_lt_of_le hk hgap
  exact expectedTBoundedColorings_lt_one_of_lt_firstMomentThreshold
    n (kThresholdAlphaMinus2Level n) k (kThresholdAlphaMinus2Level_pos n) hk'

/-- **Eventual threshold-gap frontier → first-moment source.**

This is the converse reduction to
`kThresholdAlphaMinusOne_add_ceil_n_div_logsq_le_kThresholdAlphaMinus2` at the
source level: to discharge the first-moment paper axiom, it suffices to prove
eventually that the left edge of the `(α − 2)` crossing window lies below the
`(α − 2)` first-moment threshold. -/
theorem partB_alphaMinusTwo_firstMomentBelowOne_of_eventual_thresholdGap
    (hgap :
      ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
        kThresholdAlphaMinusOne n + ⌈(n : ℝ) / Real.log n ^ 2⌉₊ ≤
          firstMomentThreshold n (kThresholdAlphaMinus2Level n)
            (kThresholdAlphaMinus2Level_pos n)) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      ∀ k : ℕ, k < kThresholdAlphaMinusOne n + ⌈(n : ℝ) / Real.log n ^ 2⌉₊ →
        expectedTBoundedColorings n k (kThresholdAlphaMinus2Level n) < 1 := by
  obtain ⟨n₀, hgap'⟩ := hgap
  refine ⟨n₀, fun n hn k hk => ?_⟩
  exact partB_alphaMinusTwo_firstMomentBelowOne_of_thresholdGap n (hgap' n hn) hk

/-- **Exact source frontier.**

The first-moment source window is equivalent to the eventual threshold-gap
statement.  Thus the remaining mathematical content of
`partB_alphaMinusTwo_firstMomentBelowOne_source` is precisely an asymptotic
lower bound on the `(α − 2)` first-moment threshold, not a separate
probabilistic step. -/
theorem partB_alphaMinusTwo_firstMomentBelowOne_iff_eventual_thresholdGap :
    (∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      ∀ k : ℕ, k < kThresholdAlphaMinusOne n + ⌈(n : ℝ) / Real.log n ^ 2⌉₊ →
        expectedTBoundedColorings n k (kThresholdAlphaMinus2Level n) < 1) ↔
    (∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      kThresholdAlphaMinusOne n + ⌈(n : ℝ) / Real.log n ^ 2⌉₊ ≤
        firstMomentThreshold n (kThresholdAlphaMinus2Level n)
          (kThresholdAlphaMinus2Level_pos n)) := by
  constructor
  · intro hsrc
    obtain ⟨n₀, hsrc'⟩ := hsrc
    refine ⟨n₀, fun n hn => ?_⟩
    set K : ℕ := kThresholdAlphaMinusOne n + ⌈(n : ℝ) / Real.log n ^ 2⌉₊
      with hK_def
    have hlt : ∀ k : ℕ, k < K →
        expectedTBoundedColorings n k (kThresholdAlphaMinus2Level n) < 1 := hsrc' n hn
    have hnot : ∀ k : ℕ, k < K →
        ¬ ((1 : ℝ) ≤ expectedTBoundedColorings n k (kThresholdAlphaMinus2Level n)) := by
      intro k hk hge
      exact (lt_irrefl (1 : ℝ)) (lt_of_le_of_lt hge (hlt k hk))
    exact Nat.le_find_iff _ _ |>.mpr (by intro m hm; exact hnot m hm)
  · intro hgap
    exact partB_alphaMinusTwo_firstMomentBelowOne_of_eventual_thresholdGap hgap

/-- Paper-backed χ lower-bound whp at level α−2 for crossing windows.

    Source: HP-2023 arXiv:2306.07253 Lemma 8.1 (chi_{α-2} ≥ k_{α-2} - 1 whp) +
    Markov-style first-moment argument; the slack `n^{0.99}` covers the
    `α-2` analogue of Heckel 2024's downgrade. Anchored at the upper threshold
    `kThresholdAlphaMinus2 n`.

    **Hypothesis surface — `¬ InMainRangeMod ε n`.**
    The two halves: (a) DEEP crossing: μ_α(n) < n^{x₀+ε}; (b) HIGH regime:
    μ_α(n) > n^{1-ε}, which is vacuous for large n (absorbed by `∃ n₀`). -/
axiom chi_alphaMinusTwo_lower_bound_whp (ε : ℝ) (hε_pos : 0 < ε) (hε_small : ε < 0.001) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ¬ InMainRangeMod ε n →
      1 - ENNReal.ofReal ε ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          (kThresholdAlphaMinus2 n : ℝ) - (n : ℝ) ^ (0.99 : ℝ) ≤
            (chromaticNumber G : ℝ)}

/-- Paper-backed ζ upper-bound whp at level α−2 for crossing windows.

    Source: Heckel 2024 arXiv:2409.17614 Proposition 5(b) + Azuma–Hoeffding,
    adapted from (α−1)-bounded to (α−2)-bounded cocolorings. Anchored at
    `kThresholdAlphaMinusOne n`, slack `n^{0.99}`.

    **Disclosure:** Heckel 2024 restricts to (α−1)-bounded profiles; the (α−2)
    adaptation is natural via HP-2023 §8 which uses the same machinery at both
    levels `a ∈ {α−2, α−1}`, and HP-2023 §6.3–6.5 second-moment lemmas stated
    for general a-bounded profiles transfer verbatim. -/
axiom zeta_alphaMinusTwo_upper_bound_whp (ε : ℝ) (hε_pos : 0 < ε) (hε_small : ε < 0.001) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ¬ InMainRangeMod ε n →
      1 - ENNReal.ofReal ε ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          (cochromaticNumber G : ℝ) ≤
            (kThresholdAlphaMinusOne n : ℝ) + (n : ℝ) ^ (0.99 : ℝ)}

end

end Problem625
