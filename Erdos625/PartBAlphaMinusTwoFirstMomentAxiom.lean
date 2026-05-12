import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Erdos625.PartBProfileBridge

/-!
# Part B `(α − 2)` First-Moment-Below-One — Isolated Paper Axiom

This file isolates the single narrowed paper axiom
`partB_alphaMinusTwo_firstMomentBelowOne_source` previously declared inline in
`Erdos625/CrossingPartB.lean`.  Factoring it into a dedicated
module gives the axiom a stable namespaced location and lets downstream
consumers (`CrossingPartB`, `CumulantAlphaMinusTwo`) import it by name without
pulling in the rest of the R2B-Step-3 bridge machinery.

The axiom statement and its citation are reproduced **verbatim** from
`CrossingPartB.lean` (pre-factoring); see the historical docstring there for
the full R2B-Step-3.2 narrowing rationale.
-/

namespace Problem625

open Real

noncomputable section

/-- **Narrowed paper-axiom for R2B Step 3.2: first-moment `< 1` window at
level `(α − 2)`.**

This is the unique unproved input on the R2B path after Step 3.2. It states
the *first-moment-below-one* form of HP-2023 Lemma 8.1's input: for every
`k` strictly below `kThresholdAlphaMinusOne n + ⌈n / log² n⌉`, the expected
number of `(α − 2)`-bounded ordered cochromatic `k`-colourings of
`G(n, 1/2)` is strictly less than `1`, eventually in `n`.

This is **strictly narrower** than the previous gap axiom: it cites only the
first-moment computation paragraph of HP-2023 Lemma 8.1's proof
(the sentence "by the definition of the first moment threshold,
`E_{n, k_a − 1, a} < 1`", strengthened to a uniform window of width
`⌈n / log² n⌉`), not the full threshold-method conclusion.

**Source (single citation, narrower than before).**
Heckel–Panagiotou, arXiv:2306.07253, **proof of Lemma 8.1**, first-moment
input paragraph, instantiated at level `(α − 2)` over a window of width
`⌈n / log² n⌉` above `kThresholdAlphaMinusOne n`.

The threshold-gap conclusion `KThresholdGapSource` is **discharged on the
Lean side** from this narrower axiom by the proved combinator
`partB_crossing_lower_bound_alpha_minus_two_source` in `CrossingPartB.lean`,
using only the `Nat.find` definition of `firstMomentThreshold`. -/
axiom partB_alphaMinusTwo_firstMomentBelowOne_source :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      ∀ k : ℕ, k < kThresholdAlphaMinusOne n + ⌈(n : ℝ) / Real.log n ^ 2⌉₊ →
        expectedTBoundedColorings n k (kThresholdAlphaMinus2Level n) < 1

end

end Problem625
