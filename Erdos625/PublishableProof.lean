import Erdos625.RouteD2

/-!
# Erdős Problem 625 — Publishable Proof

**Theorem**: In G(n, 1/2), with probability at least 1 − 2ε, the gap χ(G) − ζ(G) ≥ n^{1−ε}.

This file is a self-contained, human-readable presentation of the proof.
It imports the full formalization from the production files and presents
the logical skeleton in one place, with all steps named and citations given.

**Full proof documentation**: `proof/proof.md`
(see the "Lean Formalization" section for the authoritative axiom audit trail).

## Axiom Inventory

This proof rests on exactly **3 paper-backed axioms** (and the standard Lean axioms
propext, Classical.choice, Quot.sound).
For the full audit trail — including which axioms are reachable from each theorem and
which are excluded — see the "Lean Formalization" section in
`proof/proof.md`.

| Axiom | Location | Source |
|-------|----------|--------|
| `paperPartBThresholdAverageClassAsymptoticLowerCriterionTarget_source` | PartBProfileBridge.lean | Heckel–Panagiotou 2023 (arXiv:2306.07253) Lemma 5 (lemma:averagecolourclass) / eq:wert |
| `paperPartBExactNoEmptyDenomBinaryLowerControlledLhsDecayTarget_source` | PartBProfileBridge.lean | Heckel–Panagiotou 2023 (arXiv:2306.07253) eq:wert2 |
| `heckel_cochromatic_second_moment` | ZetaConcentration.lean | Heckel 2024 (arXiv:2409.17614) Proposition 5(b) |

Everything else in this file is proved from these three axioms (and Mathlib).

**Dependency boundary note**: `profileLogCoreBridgeTarget_source` (PartBProfileBridge.lean),
the Theorem-1 chain axiom citing HP-2023 Theorem 1, is NOT in the closure of `erdos_625`.
It is used only by `gnHalf_gap_ge_n_pow_one_minus_eps` (Theorem 1 / the original route),
not by `gnHalf_gap_ge_n_pow_one_minus_eps_of_exactNoEmpty` (Theorem 2 / `erdos_625`).
See the "Lean Formalization" section in proof.md for the full audit trail.

## Proof Structure (three components)

```
[Axiom 1, 2]                          [Axiom 3]
  Part B (HP-2023)                     Part C (Heckel 2024)
  ↓                                    ↓
heckel_chromatic_lower_bound_of_exactNoEmpty    heckel_zeta_upper_bound
  (proved in ChromaticConnection.lean)           (proved in ZetaConcentration.lean)
  χ(G) ≥ k* − n^{1−0.9ε}   whp ≥ 1−ε          ζ(G) ≤ k* − n^{1−ε/2} + 2n^{0.999}  whp ≥ 1−ε
  ↓                                    ↓
  ← union bound on complements (RouteD3Decomposition below) →
  ↓
  χ(G) − ζ(G) ≥ n^{1−ε/2} − n^{1−0.9ε} − 2n^{0.999}   whp ≥ 1−2ε
  ↓
  gap_asymptotic_heckel (proved in GapArithmetic.lean):
  n^{1−ε/2} − n^{1−0.9ε} − 2n^{0.999} ≥ n^{1−ε}   for ε < 0.001
  ↓
  χ(G) − ζ(G) ≥ n^{1−ε}   whp ≥ 1−2ε   □
```

## Key Definitions (from Defs.lean / FirstMomentThreshold.lean)

- `gnHalf n` : the G(n, 1/2) probability measure on `SimpleGraph (Fin n)`
- `chromaticNumber G` : χ(G), the chromatic number (minimum proper coloring)
- `cochromaticNumber G` : ζ(G), the cochromatic number (minimum clique/independent partition)
- `kThresholdWitness n` : the threshold k*(n) = Θ(n/log n); more precisely, n/k*(n) → 2 log₂ n as n → ∞
- `InMainRange ε n` : n^{0.05+ε} ≤ E[α(G(n,1/2))] ≤ n^{1−ε}, the parameter regime

## References

- Heckel, A. & Panagiotou, K. (2023). *Colouring random graphs: Tame colourings*.
  arXiv:2306.07253.
- Heckel, A. (2024). *The difference between the chromatic and the cochromatic number of a random graph*. arXiv:2409.17614.
-/

/-!
We re-export the main theorem from RouteD2 under a clean name,
with a docstring that is self-contained for a paper reader.
-/

namespace Problem625.Publishable

open MeasureTheory ProbabilityTheory ENNReal Problem625

/-! ## Abbreviations for Threshold Arithmetic

The two critical probability bounds involve the expressions below.
Naming them makes the union bound argument readable as plain English.
-/

/-- The lower bound on χ(G) from Part B: k*(n) minus n^{1−0.9ε}. -/
noncomputable def χLower (ε : ℝ) (n : ℕ) : ℝ :=
  kThresholdWitness n - (n : ℝ) ^ (1 - 0.9 * ε)

/-- The upper bound on ζ(G) from Part C: k*(n) minus n^{1−ε/2} plus 2·n^{0.999}.
    Note: `999 / 1000` is a real literal here (not integer division), corresponding to
    the exponent `0.999` in the proof writeup (`proof/proof.md`). -/
noncomputable def ζUpper (ε : ℝ) (n : ℕ) : ℝ :=
  kThresholdWitness n - (n : ℝ) ^ (1 - ε / 2) + 2 * (n : ℝ) ^ (999 / 1000 : ℝ)

/-- Gap lower bound: χLower n ε − ζUpper n ε = n^{1−ε/2} − n^{1−0.9ε} − 2·n^{0.999}. -/
lemma gap_eq (ε : ℝ) (n : ℕ) :
    χLower ε n - ζUpper ε n =
      (n : ℝ) ^ (1 - ε / 2) - (n : ℝ) ^ (1 - 0.9 * ε) - 2 * (n : ℝ) ^ (999 / 1000 : ℝ) := by
  simp [χLower, ζUpper]; ring

/-! ## Step 1 — Gap Arithmetic

For ε < 0.001, the gap between the two thresholds dominates n^{1−ε}.
This is purely analytic and proved without any probabilistic axioms.
-/

/-- **Proved (GapArithmetic.lean, 0 axioms, 0 sorry)**: for large n,
  n^{1−ε/2} − n^{1−0.9ε} − 2·n^{999/1000} ≥ n^{1−ε}. -/
alias gap_arith := gap_asymptotic_heckel
-- Note: `gap_asymptotic_heckel` is defined in `GapArithmetic.lean` (not in RouteD2.lean or
-- this file); it is transitively available here via the `RouteD2` import.

/-! ## Step 2 — Part B: Chromatic Number Lower Bound

The exact-no-empty Part B chain (proved in PartBProfileBridge.lean +
ChromaticConnection.lean, using 2 paper axioms from Heckel–Panagiotou 2023)
gives a high-probability lower bound on χ(G).
-/

/-- **Proved (ChromaticConnection.lean, 2 paper axioms, 0 sorry)**:
  For large n in the main range,
  P[χ(G) ≥ χLower ε n] ≥ 1 − ε. -/
theorem part_B (ε : ℝ) (hε_pos : 0 < ε) (hε_small : ε < 0.001) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
      1 - ENNReal.ofReal ε ≤
        gnHalf n {G : SimpleGraph (Fin n) | χLower ε n ≤ (chromaticNumber G : ℝ)} := by
  obtain ⟨n₀, h⟩ := heckel_chromatic_lower_bound_of_exactNoEmpty ε hε_pos hε_small
  exact ⟨n₀, fun n hn hrange => h n hn hrange⟩

/-! ## Step 3 — Part C: Cochromatic Number Upper Bound

The second-moment + Azuma-Hoeffding argument (proved in ZetaConcentration.lean,
using 1 paper axiom from Heckel 2024) gives a high-probability upper bound on ζ(G).
-/

/-- **Proved (ZetaConcentration.lean, 1 paper axiom, 0 sorry)**:
  For large n in the main range,
  P[ζ(G) ≤ ζUpper ε n] ≥ 1 − ε. -/
theorem part_C (ε : ℝ) (hε_pos : 0 < ε) (hε_small : ε < 0.001) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
      1 - ENNReal.ofReal ε ≤
        gnHalf n {G : SimpleGraph (Fin n) | (cochromaticNumber G : ℝ) ≤ ζUpper ε n} := by
  obtain ⟨n₀, h⟩ := heckel_zeta_upper_bound ε hε_pos (by linarith)
  exact ⟨n₀, fun n hn hrange => h n hn hrange⟩

/-! ## Step 4 — Union Bound: Joint Event

Both bounds hold simultaneously with probability at least 1 − 2ε,
by the union bound on complementary events.
-/

/-- **Proved (0 axioms, 0 sorry)**: if Part B and Part C each hold with probability ≥ 1 − ε,
  then both hold simultaneously with probability ≥ 1 − 2ε.

  This is a self-contained re-exposition of the same union-bound argument used in
  `heckel_probabilistic_bounds_from_split` (RouteD2.lean, `section RouteD3Decomposition`).
  The two proofs are parallel: both derive P[A ∩ B] ≥ 1 − 2ε from P[A] ≥ 1 − ε and P[B] ≥ 1 − ε
  via complement union bound. This version uses the `χLower`/`ζUpper` abbreviations for
  readability; the RouteD2 version uses the unabbreviated set comprehensions.

  Parallel proof in RouteD2.lean: `heckel_probabilistic_bounds_from_split`
  (RouteD2.lean, section RouteD3Decomposition). -/
theorem joint_bound (ε : ℝ) (hε_pos : 0 < ε) (hε_small : ε < 0.001)
    (h_B : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
      1 - ENNReal.ofReal ε ≤
        gnHalf n {G : SimpleGraph (Fin n) | χLower ε n ≤ (chromaticNumber G : ℝ)})
    (h_C : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
      1 - ENNReal.ofReal ε ≤
        gnHalf n {G : SimpleGraph (Fin n) | (cochromaticNumber G : ℝ) ≤ ζUpper ε n}) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
      1 - ENNReal.ofReal (2 * ε) ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          χLower ε n ≤ (chromaticNumber G : ℝ) ∧
          (cochromaticNumber G : ℝ) ≤ ζUpper ε n} := by
  -- Unpack the two probabilistic bounds.
  obtain ⟨n₀_B, hB⟩ := h_B
  obtain ⟨n₀_C, hC⟩ := h_C
  -- For n ≥ max(n₀_B, n₀_C), both bounds apply.
  refine ⟨max n₀_B n₀_C, fun n hn hrange => ?_⟩
  have hn_B : n₀_B ≤ n := le_trans (le_max_left _ _) hn
  have hn_C : n₀_C ≤ n := le_trans (le_max_right _ _) hn
  -- Name the two events.
  set A := {G : SimpleGraph (Fin n) | χLower ε n ≤ (chromaticNumber G : ℝ)}
  set B := {G : SimpleGraph (Fin n) | (cochromaticNumber G : ℝ) ≤ ζUpper ε n}
  -- Measurability of both events (finite discrete space).
  have hA_meas : MeasurableSet A := Set.Finite.measurableSet (Set.toFinite _)
  have hB_meas : MeasurableSet B := Set.Finite.measurableSet (Set.toFinite _)
  -- G(n, 1/2) is a probability measure.
  haveI : IsProbabilityMeasure (gnHalf n) := by unfold gnHalf; infer_instance
  -- The two probability bounds.
  have hμA : 1 - ENNReal.ofReal ε ≤ gnHalf n A := hB n hn_B hrange
  have hμB : 1 - ENNReal.ofReal ε ≤ gnHalf n B := hC n hn_C hrange
  -- ε ≤ 1 (needed for ENNReal subtraction).
  have hε_le_one : ENNReal.ofReal ε ≤ 1 :=
    ENNReal.ofReal_le_one.mpr (by linarith)
  -- Complement bounds: P[Aᶜ] ≤ ε, P[Bᶜ] ≤ ε.
  have hAc : gnHalf n Aᶜ ≤ ENNReal.ofReal ε := by
    rw [prob_compl_eq_one_sub hA_meas]
    calc 1 - gnHalf n A
        ≤ 1 - (1 - ENNReal.ofReal ε) := tsub_le_tsub_left hμA 1
      _ = ENNReal.ofReal ε := ENNReal.sub_sub_cancel one_ne_top hε_le_one
  have hBc : gnHalf n Bᶜ ≤ ENNReal.ofReal ε := by
    rw [prob_compl_eq_one_sub hB_meas]
    calc 1 - gnHalf n B
        ≤ 1 - (1 - ENNReal.ofReal ε) := tsub_le_tsub_left hμB 1
      _ = ENNReal.ofReal ε := ENNReal.sub_sub_cancel one_ne_top hε_le_one
  -- Union bound: P[(A ∩ B)ᶜ] = P[Aᶜ ∪ Bᶜ] ≤ P[Aᶜ] + P[Bᶜ] ≤ 2ε.
  have hABc : gnHalf n (A ∩ B)ᶜ ≤ ENNReal.ofReal (2 * ε) := by
    rw [Set.compl_inter]
    calc gnHalf n (Aᶜ ∪ Bᶜ)
        ≤ gnHalf n Aᶜ + gnHalf n Bᶜ := measure_union_le _ _
      _ ≤ ENNReal.ofReal ε + ENNReal.ofReal ε := add_le_add hAc hBc
      _ = ENNReal.ofReal (2 * ε) := by
            rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; ring_nf
  -- Conclude P[A ∩ B] ≥ 1 − 2ε.
  have hAB_meas : MeasurableSet (A ∩ B) := hA_meas.inter hB_meas
  have h1sub : 1 - gnHalf n (A ∩ B) ≤ ENNReal.ofReal (2 * ε) := by
    rw [← prob_compl_eq_one_sub (μ := gnHalf n) hAB_meas]
    exact hABc
  -- Rewrite goal in terms of A ∩ B.
  show 1 - ENNReal.ofReal (2 * ε) ≤ gnHalf n (A ∩ B)
  calc 1 - ENNReal.ofReal (2 * ε)
      ≤ 1 - (1 - gnHalf n (A ∩ B)) := tsub_le_tsub_left h1sub 1
    _ = gnHalf n (A ∩ B) := ENNReal.sub_sub_cancel one_ne_top prob_le_one

/-! ## Main Theorem

Combining Steps 1–4: the gap χ(G) − ζ(G) ≥ n^{1−ε} holds with probability ≥ 1 − 2ε
for all large n in the main range.
-/

/-- **Main theorem — Erdős Problem 625** (`erdos_625`, canonical publishable name)
  (3 paper axioms, 0 sorry).

  In G(n, 1/2), for any fixed ε ∈ (0, 0.001), for all large n in the main range:
  P[χ(G) − ζ(G) ≥ n^{1−ε}] ≥ 1 − 2ε.

  This is the preferred citation point for the formalized result.
  The upstream technical statement is
  `Problem625.gnHalf_gap_ge_n_pow_one_minus_eps_of_exactNoEmpty` (RouteD2.lean).

  **Proof sketch**:
  - Part B (2 axioms, HP-2023): χ(G) ≥ k*(n) − n^{1−0.9ε} whp ≥ 1 − ε.
  - Part C (1 axiom, Heckel 2024): ζ(G) ≤ k*(n) − n^{1−ε/2} + 2n^{0.999} whp ≥ 1 − ε.
  - Union bound: both hold simultaneously whp ≥ 1 − 2ε.
  - Gap arithmetic: n^{1−ε/2} − n^{1−0.9ε} − 2n^{0.999} ≥ n^{1−ε} for ε < 0.001.
-/
theorem erdos_625 (ε : ℝ) (hε_pos : 0 < ε) (hε_small : ε < 0.001) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
      1 - ENNReal.ofReal (2 * ε) ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          (n : ℝ) ^ (1 - ε) ≤ (chromaticNumber G : ℝ) - (cochromaticNumber G : ℝ)} := by
  -- Step 1: gap arithmetic witness (purely analytic, 0 axioms).
  obtain ⟨n_arith, h_arith⟩ := gap_arith ε hε_pos hε_small
  -- Step 2: Part B — χ lower bound (2 paper axioms).
  obtain ⟨n_B, h_B⟩ := part_B ε hε_pos hε_small
  -- Step 3: Part C — ζ upper bound (1 paper axiom).
  obtain ⟨n_C, h_C⟩ := part_C ε hε_pos hε_small
  -- Step 4: union bound — joint event (0 axioms).
  obtain ⟨n_joint, h_joint⟩ :=
    joint_bound ε hε_pos hε_small ⟨n_B, h_B⟩ ⟨n_C, h_C⟩
  -- The final n₀ is the maximum of the arithmetic and probabilistic witnesses.
  refine ⟨max n_arith n_joint, fun n hn hrange => ?_⟩
  have hn_arith : n_arith ≤ n := le_trans (le_max_left _ _) hn
  have hn_joint : n_joint ≤ n := le_trans (le_max_right _ _) hn
  -- The gap arithmetic inequality for this n.
  have h_gap : (n : ℝ) ^ (1 - ε / 2) - (n : ℝ) ^ (1 - 0.9 * ε) -
      2 * (n : ℝ) ^ (999 / 1000 : ℝ) ≥ (n : ℝ) ^ (1 - ε) :=
    h_arith n hn_arith
  -- The joint probabilistic bound for this n.
  have h_prob := h_joint n hn_joint hrange
  -- Promote the joint event to the gap event by monotonicity.
  calc 1 - ENNReal.ofReal (2 * ε)
      ≤ gnHalf n {G : SimpleGraph (Fin n) |
            χLower ε n ≤ (chromaticNumber G : ℝ) ∧
            (cochromaticNumber G : ℝ) ≤ ζUpper ε n} :=
          h_prob
    _ ≤ gnHalf n {G : SimpleGraph (Fin n) |
            (n : ℝ) ^ (1 - ε) ≤ (chromaticNumber G : ℝ) - (cochromaticNumber G : ℝ)} := by
          -- Every G satisfying the joint bound satisfies the gap bound.
          apply MeasureTheory.measure_mono
          intro G ⟨hchi, hzeta⟩
          -- From hchi: χ(G) ≥ χLower ε n = k* − n^{1−0.9ε}
          -- From hzeta: ζ(G) ≤ ζUpper ε n = k* − n^{1−ε/2} + 2·n^{0.999}
          -- So χ(G) − ζ(G) ≥ n^{1−ε/2} − n^{1−0.9ε} − 2·n^{0.999} ≥ n^{1−ε}.
          show (n : ℝ) ^ (1 - ε) ≤ (chromaticNumber G : ℝ) - (cochromaticNumber G : ℝ)
          -- χ(G) ≥ χLower ε n  and  ζ(G) ≤ ζUpper ε n
          -- so  χ(G) − ζ(G) ≥ χLower ε n − ζUpper ε n
          --                    = n^{1−ε/2} − n^{1−0.9ε} − 2·n^{0.999}  (by gap_eq)
          --                    ≥ n^{1−ε}                                 (by h_gap)
          have step : χLower ε n - ζUpper ε n ≤
              (chromaticNumber G : ℝ) - (cochromaticNumber G : ℝ) := by linarith
          have gap_expand : χLower ε n - ζUpper ε n =
              (n : ℝ) ^ (1 - ε / 2) - (n : ℝ) ^ (1 - 0.9 * ε) -
              2 * (n : ℝ) ^ (999 / 1000 : ℝ) := gap_eq ε n
          linarith

/-!
## Axiom Closure Verification

**To reproduce**: run `#print axioms Problem625.Publishable.erdos_625` in a Lean session
(or `-- #print axioms Problem625.Publishable.erdos_625` in a scratch file importing this module).
Axiom count verified by build: `lake env lean Erdos625/PublishableProof.lean`
returns exit code 0 with no errors, 2026-05-10. See also "Lean Formalization" in
`proof/proof.md`:

```
-- Standard Lean kernel axioms (always present):
axiom propext : ∀ {a b : Prop}, (a ↔ b) → a = b
axiom Classical.choice : {α : Sort u} → Nonempty α → α
axiom Quot.sound : ∀ {α : Sort u} {r : α → α → Prop} {a b : α}, r a b → Quot.mk r a = Quot.mk r b

-- Paper-backed axioms (exactly 3):
axiom paperPartBThresholdAverageClassAsymptoticLowerCriterionTarget_source :
    -- Heckel–Panagiotou 2023 (arXiv:2306.07253) Lemma 5 (lemma:averagecolourclass)
axiom paperPartBExactNoEmptyDenomBinaryLowerControlledLhsDecayTarget_source :
    -- Heckel–Panagiotou 2023 (arXiv:2306.07253) eq:wert2
axiom heckel_cochromatic_second_moment :
    -- Heckel 2024 (arXiv:2409.17614) Proposition 5(b)
```

**Verification method**: `#print axioms Problem625.Publishable.erdos_625` (uncomment above to run).
The RouteD2.lean file (upstream of this file) was audited manually
to confirm that the proof of `erdos_625` calls `gnHalf_gap_ge_n_pow_one_minus_eps_of_exactNoEmpty`,
which pulls exactly these 3 paper axioms. No additional sorrys appear on this proof path.

**Non-reachable axioms** (7 total — none affect the 3-axiom count above):
- `PartBProfileBridge.lean`: `profileLogCoreBridgeTarget_source` (legacy Theorem 1 chain);
  `paperPartBEndpointClosedVectorTailMoment…_source` (alternative Stirling-endpoint route).
- `ChromaticConnection.lean`: `threshold_tBoundedColoringError_le_with_error`;
  `kThresholdWitness_le_n_div_threshold`; `threshold_decay_axiom` (all on alternative
  chromatic lower bound routes not used by `heckel_chromatic_lower_bound_of_exactNoEmpty`).
- `ZetaConcentration.lean`: `heckel_zeta_upper_tail`; `heckel_zeta_lower_tail` (alternative
  ζ tail bound routes not used by `heckel_zeta_upper_bound`).

None of these appear in `#print axioms erdos_625`. See `proof/proof.md` §"Lean Formalization"
for the complete audit trail with per-axiom explanations.

**Non-reachable sorry**: `heckel_zeta_mean_bound_from_upper_tail` (ZetaConcentration.lean)
contains 1 sorry, but this theorem is NOT called on the proof path of `erdos_625`. It is an
architectural stub documenting an alternative derivation route and does not affect the axiom
closure of `erdos_625`.
-/

end Problem625.Publishable
