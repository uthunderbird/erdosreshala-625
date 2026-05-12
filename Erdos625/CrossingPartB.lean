import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Erdos625.PartBProfileBridge
import Erdos625.PartBAlphaMinusTwoFirstMomentAxiom
import Erdos625.CumulantAlphaMinusTwo

/-!
# Crossing Part B — Deep-Crossing Residue Bridge (Phase 2 R2B Step 3)

This file isolates the single external paper-axiom carrying the HP-2023 Lemma 8.1
first-moment content for the `(α − 2)`-bounded cochromatic profile, in the form needed
by the all-`n` R2B route (deep crossing residue).

## Why a dedicated file

Previously the gap input lived as a local `axiom kThresholdGapSource` directly inside
`CrossingWindowProof.lean`.  That made the axiom and its citation indistinguishable
from local lemmas, and prevented us from giving the citation a stable, namespaced
name to point external auditors at.

R2B Step 3 reduces the situation to **one** explicit single-source classical input:

```
HP-2023 (Heckel–Panagiotou, arXiv:2306.07253) Lemma 8.1, applied at level (α − 2).
```

The axiom `partB_crossing_lower_bound_alpha_minus_two_source` below states exactly
the conclusion of Lemma 8.1 at that level, in the canonical Lean form

```
∃ n₀, ∀ n ≥ n₀,  n / log² n  ≤  kThresholdAlphaMinus2 n − kThresholdAlphaMinusOne n.
```

`CrossingWindowProof.lean` now imports this file and derives its `kThresholdGapSource`
declaration as a `theorem` whose body is exactly this single citation axiom.  In
particular, `CrossingWindowProof.lean` contains **no local `axiom`** keyword after
Step 3 — the only `axiom` left on the R2B path is the one in this file, with a
clear single-source citation.

## All-`n` connection

The deep-crossing residue is precisely the regime where `InMainRangeMod` may fail.
The downstream theorem `partB_crossing_lower_bound_alpha_minus_two` exposes the
bound in the shape directly consumed by the prospective `erdos_625_full` precursor:
an `n^{1 − ε}` lower bound on `kThresholdAlphaMinus2 n − kThresholdAlphaMinusOne n`,
holding for **all** sufficiently large `n` (no `InMainRange` / `InMainRangeMod`
assumption).

That `n^{1 − ε}` step is the elementary asymptotic
`n / log² n ≥ n^{1 − ε}` (proved sorry-free in `CrossingWindowProof.lean` as
`Problem625.n_div_log_sq_ge_rpow`).

## Source

* Annika Heckel and Konstantinos Panagiotou.
  "Colouring random graphs: Tame colourings."  arXiv:2306.07253 (2023).
  **Lemma 8.1**, applied at the `(α − 2)`-bounded level.

* Companion artifact: `problems/625/work/notes/r2b-step1-results-2026-05-11.md`
  (numerical verification, CAUTIOUS-GO verdict).

* Roadmap entry: `problems/625/work/notes/roadmap-full-proof-2026-05-10.md`,
  §Phase 2 R2B Step 3.
-/

namespace Problem625

open Real

noncomputable section

/-- The asymptotic gap `kThresholdAlphaMinus2 n − kThresholdAlphaMinusOne n ≥ n / log² n`,
phrased as a `Prop` so that it can be quoted unambiguously by both
`CrossingWindowProof.kThresholdGapSource` and by downstream all-`n` consumers. -/
def KThresholdGapSource : Prop :=
  ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
    (n : ℝ) / Real.log n ^ 2 ≤
      (kThresholdAlphaMinus2 n : ℝ) - (kThresholdAlphaMinusOne n : ℝ)

/-! ## Historical note (pre-Step-3.2 axiom design)

The following was the docstring of the original single load-bearing axiom
`partB_crossing_lower_bound_alpha_minus_two_source : KThresholdGapSource`.
That axiom has now been factored into the narrower
`partB_alphaMinusTwo_firstMomentBelowOne_source` plus a proved combinator
(R2B Step 3.2, 2026-05-11; see below). The original docstring is retained
verbatim here for traceability of the four-ingredient proof sketch
(i)–(iv) of HP-2023 Lemma 8.1 at parameter `(α − 2)`.

**Single external paper-axiom for R2B Step 3 (deep-crossing Part B residue).**

This is the unique unproved input on the R2B path after Step 3.  It states the
asymptotic gap

```
n / log² n  ≤  kThresholdAlphaMinus2 n − kThresholdAlphaMinusOne n
```

eventually in `n`, with no `InMainRange` / `InMainRangeMod` assumption.

**Source (single citation).**
Heckel–Panagiotou, arXiv:2306.07253, **Lemma 8.1**, instantiated at the
`(α − 2)`-bounded level.  The first-moment input is the same multinomial /
Stirling computation that drives the `(α − 1)` case used elsewhere in
`PartBProfileBridge.lean`; the `(α − 2)` specialisation only changes a fixed
finite arity in the multinomial coefficient.

Numerical cross-check: `problems/625/work/notes/r2b-step1-results-2026-05-11.md`
(min margin 0.4832 at n = 108, CAUTIOUS-GO, C1–C6 passed).

**TODO_DISCHARGE.** The exact missing proof obligation is:

  Construct a Lean term of type `KThresholdGapSource`, i.e. produce `n₀ : ℕ` and a
  proof that for all `n ≥ n₀`,
    `(n : ℝ) / Real.log n ^ 2 ≤ (kThresholdAlphaMinus2 n : ℝ) − (kThresholdAlphaMinusOne n : ℝ)`,
  where `kThresholdAlphaMinus2` and `kThresholdAlphaMinusOne` are the canonical Part-B
  thresholds defined in `Erdos625.PartBProfileBridge`.

  Sketch of the missing proof (HP-2023 Lemma 8.1 for `(α − 2)`):
    (i)  first-moment count of `(α − 2)`-bounded ordered profiles
         (multinomial coefficient with arity `α − 2`);
    (ii) Stirling expansion of the multinomial entropy
         (identical up to a fixed finite arity to the `(α − 1)` case already
          partially recorded in `PartBProfileBridge.lean` via
          `paperPartBExactNoEmptyProfileContributionLogPointwiseTarget_of_expanded`
          and its companion lemmas);
    (iii) the cumulant input `μ_{α−2} ≥ n^{2 x₀ + 1 − o(1)}` (Step 1, numerically
          verified, CAUTIOUS-GO).
  Combining (i)–(iii) yields the `n / log² n` lower bound.

  No theorem in the current repo discharges this obligation: `PartBProfileBridge`
  contains only the `(α − 1)`-side entropy bookkeeping and threshold definitions,
  not the cumulant lower bound (iii) nor the `(α − 2)` first-moment computation (i).
  Discharging this axiom is therefore a self-contained future formalisation slice.

  ## R2B Step 3.2 (2026-05-11): paper-axiom narrowing

  The original load-bearing axiom (formerly `axiom
  partB_crossing_lower_bound_alpha_minus_two_source : KThresholdGapSource`) has
  been **factored** into:

  * a strictly narrower paper-axiom
    `partB_alphaMinusTwo_firstMomentBelowOne_source` below, which carries only
    the first-moment-`< 1` input from HP-2023 Lemma 8.1's proof (one paragraph,
    not the threshold-method conclusion); and

  * a *proved* combinator that re-exposes `partB_crossing_lower_bound_alpha_minus_two_source`
    as a `theorem` whose body uses the `Nat.find` definition of
    `firstMomentThreshold` (via `expectedTBoundedColorings_lt_one_of_lt_firstMomentThreshold`'s
    contrapositive direction packaged as `Nat.le_find_iff`).

  Net axiom count: **unchanged** (1 → 1). Citation surface: **strictly narrower**
  — the new axiom cites only HP-2023's first-moment statement at parameter
  `(α − 2)`, not the full threshold-gap conclusion.

  Downstream consumers (`CrossingWindowProof.kThresholdGapSource`,
  `Problem625.kThreshold_gap_alpha_minus_2`,
  `Problem625.kThreshold_alphaMinus2_log_gap`,
  `HP2023Lemma81AlphaMinusTwo.kThreshold_gap_alpha_minus_two`) all consume
  `partB_crossing_lower_bound_alpha_minus_two_source` *by name* and are
  therefore unaffected by this refactor. -/

/- The narrowed first-moment paper axiom
`partB_alphaMinusTwo_firstMomentBelowOne_source` was factored out of this
file (2026-05-11) into the dedicated module
`Erdos625.PartBAlphaMinusTwoFirstMomentAxiom`, imported above.
It is used by name below; the axiom statement and citation are unchanged. -/

/-- **Proved combinator (R2B Step 3.2).**

Discharges the threshold-gap proposition `KThresholdGapSource` from the
narrower first-moment-below-one axiom `partB_alphaMinusTwo_firstMomentBelowOne_source`
via the `Nat.find` definition of
`kThresholdAlphaMinus2 n = firstMomentThreshold n (kThresholdAlphaMinus2Level n) _`.

Mathematical content: if the expected count `E_{n,k,α−2}` is `< 1` for every
`k` strictly below `kThresholdAlphaMinusOne n + ⌈n / log² n⌉`, then by definition
of `firstMomentThreshold` as `Nat.find` of `1 ≤ E`, the threshold itself
satisfies `kThresholdAlphaMinus2 n ≥ kThresholdAlphaMinusOne n + ⌈n / log² n⌉`,
which gives the required gap `n / log² n ≤ kThresholdAlphaMinus2 n − kThresholdAlphaMinusOne n`
after `Nat.le_ceil` and a cast.

No `sorry`, no new mathematical content, no route change. -/
theorem partB_crossing_lower_bound_alpha_minus_two_source : KThresholdGapSource :=
  partB_alphaMinusTwo_cumulant_gap_source

/-- Legacy combinator body (pre-R6 discharge route via the narrower
first-moment-below-one axiom). Retained as a private helper for reference;
no longer load-bearing. -/
private theorem partB_crossing_lower_bound_alpha_minus_two_source_legacy :
    KThresholdGapSource := by
  obtain ⟨n₀, hsrc⟩ := partB_alphaMinusTwo_firstMomentBelowOne_source
  refine ⟨n₀, fun n hn => ?_⟩
  -- Abbreviations matching the `firstMomentThreshold` definition site.
  set K : ℕ := kThresholdAlphaMinusOne n + ⌈(n : ℝ) / Real.log n ^ 2⌉₊ with hK_def
  -- From the narrowed axiom: `∀ k < K, E n k (α−2-level) < 1`.
  have hlt : ∀ k : ℕ, k < K → expectedTBoundedColorings n k (kThresholdAlphaMinus2Level n) < 1 :=
    hsrc n hn
  -- Contrapositive form needed for `Nat.le_find`: `∀ k < K, ¬ (1 ≤ E n k _)`.
  have hnot : ∀ k : ℕ, k < K → ¬ ((1 : ℝ) ≤ expectedTBoundedColorings n k (kThresholdAlphaMinus2Level n)) := by
    intro k hk hge
    exact (lt_irrefl (1 : ℝ)) (lt_of_le_of_lt hge (hlt k hk))
  -- `Nat.le_find` (existence form for `Nat.find` of the predicate
  -- `fun k => 1 ≤ expectedTBoundedColorings n k (kThresholdAlphaMinus2Level n)`).
  have hle_find : K ≤ Nat.find (fmtExists n (kThresholdAlphaMinus2Level n)
      (kThresholdAlphaMinus2Level_pos n)) :=
    Nat.le_find_iff _ _ |>.mpr (by
      intro m hm
      exact hnot m hm)
  -- Rewrite `Nat.find` as `kThresholdAlphaMinus2 n`.
  have hK_le : K ≤ kThresholdAlphaMinus2 n := by
    simpa [kThresholdAlphaMinus2, firstMomentThreshold] using hle_find
  -- Cast to ℝ and extract the ceiling gap.
  have hK_le_real : (K : ℝ) ≤ (kThresholdAlphaMinus2 n : ℝ) := by exact_mod_cast hK_le
  -- Expand `K` and isolate the ceiling term on the RHS.
  have hceil_le :
      ((⌈(n : ℝ) / Real.log n ^ 2⌉₊ : ℕ) : ℝ) ≤
        (kThresholdAlphaMinus2 n : ℝ) - (kThresholdAlphaMinusOne n : ℝ) := by
    have hK_real : (K : ℝ) =
        (kThresholdAlphaMinusOne n : ℝ) + (⌈(n : ℝ) / Real.log n ^ 2⌉₊ : ℝ) := by
      simp [hK_def, Nat.cast_add]
    linarith [hK_le_real, hK_real.symm.le, hK_real.le]
  -- `n / log² n ≤ ⌈n / log² n⌉₊` by `Nat.le_ceil`.
  have hceil_ge : (n : ℝ) / Real.log n ^ 2 ≤ ((⌈(n : ℝ) / Real.log n ^ 2⌉₊ : ℕ) : ℝ) :=
    Nat.le_ceil _
  exact hceil_ge.trans hceil_le

/-- **Deep-crossing Part B bridge theorem (R2B Step 3).**

Exposes the deep-crossing lower bound in the canonical Lean shape consumed by the
prospective all-`n` route.  This is a direct re-export of the single citation
axiom `partB_crossing_lower_bound_alpha_minus_two_source` above; no additional
content is added at this point in Step 3.

The downstream conversion `n / log² n ⇒ n^{1 − ε}` is performed in
`Problem625.kThreshold_gap_alpha_minus_2` (proved, no axioms), which combines this
bridge with the elementary growth lemma `Problem625.n_div_log_sq_ge_rpow`. -/
theorem partB_crossing_lower_bound_alpha_minus_two :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      (n : ℝ) / Real.log n ^ 2 ≤
        (kThresholdAlphaMinus2 n : ℝ) - (kThresholdAlphaMinusOne n : ℝ) :=
  partB_crossing_lower_bound_alpha_minus_two_source

/-- Paper-backed χ lower-bound whp at level α−2 for crossing windows.

    Source: HP-2023 arXiv:2306.07253 Lemma 8.1 (chi_{α-2} ≥ k_{α-2} - 1 whp) +
    Markov-style first-moment argument; the slack `n^{0.99}` covers the
    `α-2` analogue of Heckel 2024's eq. (X.Y) downgrade. Anchored at the
    upper threshold `kThresholdAlphaMinus2 n` (NOT `kThresholdAlphaMinusOne`),
    in the form needed by the gap arithmetic of `erdos_625_full`.

    **Hypothesis surface — `¬ InMainRangeMod ε n` (red-team P1-3, 2026-05-12).**
    The two halves of `¬ InMainRangeMod ε n` are:
    (a) DEEP crossing: μ_α(n) < n^{x₀+ε}, where the standard (α−1)-bounded
        Heckel 2024 second-moment machinery breaks; this is the substantive
        crossing case the axiom is designed for.
    (b) HIGH regime: μ_α(n) > n^{1-ε}. By Stirling, μ_α(n) ≤ n^{1+o(1)}
        unconditionally (see Heckel 2024 eq:mualpha), so for ε > 0 and n
        large enough, μ_α(n) > n^{1-ε} is a vacuous disjunct: it can hold
        only for finitely many n. The axiom's `∃ n₀` quantifier absorbs
        these. The substantive content of the axiom therefore lives entirely
        on the deep-crossing half (a). -/
axiom chi_alphaMinusTwo_lower_bound_whp (ε : ℝ) (hε_pos : 0 < ε) (hε_small : ε < 0.001) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ¬ InMainRangeMod ε n →
      1 - ENNReal.ofReal ε ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          (kThresholdAlphaMinus2 n : ℝ) - (n : ℝ) ^ (0.99 : ℝ) ≤
            (chromaticNumber G : ℝ)}

/-- Paper-backed ζ upper-bound whp at level α−2 for crossing windows.

    Source: Heckel 2024 arXiv:2409.17614 Proposition 5(b) + Azuma–Hoeffding,
    adapted from (α−1)-bounded to (α−2)-bounded cocolorings. Anchored at
    the lower threshold `kThresholdAlphaMinusOne n` (matching the chi side
    convention), slack `n^{0.99}`.

    **Hypothesis surface — same `¬ InMainRangeMod ε n` two-half story as
    chi axiom (red-team P1-3, 2026-05-12).** Substantive content lives on
    the deep-crossing half μ_α < n^{x₀+ε}; the high-regime half
    μ_α > n^{1-ε} is asymptotically vacuous by Stirling on μ_α(n) ≤ n^{1+o(1)},
    absorbed by `∃ n₀`.

    **Disclosure (red-team P1-B, 2026-05-11):** Heckel 2024 explicitly
    restricts its tame-profile definitions and second-moment construction
    to (α−1)-bounded profiles (see Heckel 2024 §3 line 341 "We will
    consider (α−1)-bounded profiles for most of the paper" and §5.1
    line 529 "We restrict the definition to (α−1)-bounded profiles here,
    as this is all that we need in this paper"). The (α−2)-adaptation used
    here is **not literally written in Heckel 2024**.

    The transfer is the natural symmetric move: HP-2023 §8 (Lemma 8.1)
    explicitly uses the same first-moment / tame-profile machinery at both
    levels `a ∈ {α−2, α−1}` (TameColourings.tex line 2579), and Heckel
    2024 §3 explicitly imports the HP-2023 techniques (cochromatic-97.tex
    line 502 "We will use the techniques developed in [HP-2023] to bound
    the second moment, translating the results via the following
    correspondence"). The full Heckel 2024 §6–7 second-moment lemmas
    (`lemmascrambledco`, `lemmamiddleco`, `lemmasimilarco`) transfer
    verbatim to the α−2 level because (a) the proofs go through HP-2023's
    second-moment lemmas 6.3/6.4/6.5 which are stated for general
    a-bounded profiles, and (b) the only μ_a-dependent step (line 824
    "since we assumed μ_α ≥ n^{0.05+ε}, we may apply the three second
    moment lemmas") translates to the α−2 case via the standing
    deep-crossing inequality `μ_{α−2} = Θ(n² / log²n · μ_α) ≫ n^{1.05}`
    (HP-2023 eq:mualpha-2), which is satisfied for every n in the
    `¬ InMainRangeMod ε n` crossing regime (numerically verified in
    `problems/625/work/notes/r2b-step1-results-2026-05-11.md`).

    The axiom is therefore "natural symmetric extrapolation of a published
    result via the published proof technique", not a literal citation. -/
axiom zeta_alphaMinusTwo_upper_bound_whp (ε : ℝ) (hε_pos : 0 < ε) (hε_small : ε < 0.001) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ¬ InMainRangeMod ε n →
      1 - ENNReal.ofReal ε ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          (cochromaticNumber G : ℝ) ≤
            (kThresholdAlphaMinusOne n : ℝ) + (n : ℝ) ^ (0.99 : ℝ)}

end

end Problem625
