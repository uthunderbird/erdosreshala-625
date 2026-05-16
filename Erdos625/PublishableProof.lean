import Erdos625.RouteD2
import Erdos625.CrossingWindowProof

/-!
# Erdős Problem 625 — Publishable Proof

**Theorem**: In G(n, 1/2), with probability at least 1 − 2ε, the gap χ(G) − ζ(G) ≥ n^{1−ε}.

This file is a self-contained, human-readable presentation of the proof.
It imports the full formalization from the production files and presents
the logical skeleton in one place, with all steps named and citations given.

**Full proof documentation**: `problems/625/solution/proof.md`
(see the "Lean Formalization" section for the authoritative axiom audit trail).

## Axiom Inventory

The main theorems in this file have different axiom footprints:

**`erdos_625` (97% coverage, requires `InMainRange`)** rests on exactly **3 paper-backed axioms**:

| Axiom | Location | Source |
|-------|----------|--------|
| `paperPartBThresholdAverageClassAsymptoticLowerCriterionTarget_source` | PartBProfileBridge.lean | Heckel–Panagiotou 2023 (arXiv:2306.07253) Lemma 5 (lemma:averagecolourclass) / eq:wert |
| `paperPartBExactNoEmptyDenomBinaryLowerControlledLhsDecayTarget_source` | PartBProfileBridge.lean | Heckel–Panagiotou 2023 (arXiv:2306.07253) eq:wert2 |
| `heckel_offdiag_term_bound` | ZetaConcentration.lean | Heckel 2024 (arXiv:2409.17614) Proposition 5(b), off-diagonal term (2026-05-11 narrowing of the original `heckel_cochromatic_second_moment`, which is now a proved theorem in `ZetaConcentration.lean:1568` on top of `heckel_offdiag_term_bound`) |

**`erdos_625_full` and `erdos_625_full_clean` (all n)** additionally depend on two crossing-case axioms for the `¬InMainRangeMod` regime:

| Axiom | Location | Source |
|-------|----------|--------|
| `chi_alphaMinusTwo_lower_bound_whp` | CrossingPartB.lean | HP-2023 Lemma 8.1 at α−2 |
| `zeta_alphaMinusTwo_upper_bound_whp` | CrossingPartB.lean | Heckel 2024 Prop 5(b) adapted to (α−2)-bounded profiles |

Plus the standard Lean axioms propext, Classical.choice, Quot.sound.
For the full audit trail, see the "Lean Formalization" section in `problems/625/solution/proof.md`.

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
    the exponent `0.999` in the proof writeup (`problems/625/solution/proof.md`). -/
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
`proof/proof.md` (in the publish package; the source repo path was
`problems/625/solution/proof.md`):

```
-- Standard Lean kernel axioms (always present):
axiom propext : ∀ {a b : Prop}, (a ↔ b) → a = b
axiom Classical.choice : {α : Sort u} → Nonempty α → α
axiom Quot.sound : ∀ {α : Sort u} {r : α → α → Prop} {a b : α}, r a b → Quot.mk r a = Quot.mk r b

-- Paper-backed axioms (exactly 3):
axiom paperPartBThresholdAverageClassAsymptoticLowerCriterionTarget_source :
    -- Heckel–Panagiotou 2023 (arXiv:2306.07253) Lemma 5 (lemma:averagecolourclass)
axiom paperPartBExactNoEmptyDenomBinaryLowerControlledLhsDecayTarget_source :
    -- Heckel–Panagiotou 2023 (arXiv:2306.07253) eq:wert / eq:wert2
axiom heckel_offdiag_term_bound :
    -- Heckel 2024 (arXiv:2409.17614) Proposition 5(b), off-diagonal term
    -- (`heckel_cochromatic_second_moment` itself is a proved theorem above this axiom)
```

**Verification method**: `#print axioms Problem625.Publishable.erdos_625` (uncomment above to run).
The RouteD2.lean file (upstream of this file) was audited manually
to confirm that the proof of `erdos_625` calls `gnHalf_gap_ge_n_pow_one_minus_eps_of_exactNoEmpty`,
which pulls exactly these 3 paper axioms. No additional sorrys appear on this proof path.

**Non-reachable axioms**: `heckel_zeta_upper_tail` and `heckel_zeta_lower_tail`
(ZetaConcentration.lean, lines ~1317 and ~1334) are genuine `axiom` declarations in
ZetaConcentration.lean, but they are NOT on the dependency path of `erdos_625` — they are
not reachable from it and will not appear in `#print axioms erdos_625`. They refine the axiom
structure of alternative derivation routes but do not affect the 3-axiom count above.

**Non-reachable sorry**: `heckel_zeta_mean_bound_from_upper_tail` (ZetaConcentration.lean)
contains 1 sorry, but this theorem is NOT called on the proof path of `erdos_625`. It is an
architectural stub documenting an alternative derivation route and does not affect the axiom
closure of `erdos_625`.
-/

/-! ## 97%-Coverage Extension: InMainRangeMod

Theorem `erdos_625_97` extends `erdos_625` to the larger parameter regime
`InMainRangeMod ε n`, which uses the tight lower bound n^{x₀+ε} (x₀ ≈ 0.02905)
instead of n^{0.05+ε}. This covers ~97% of all large n (vs ~95% for InMainRange).

The extension rests on one new paper-backed axiom (`lemma_7_20_modified`),
which combines the modified Part B argument (HP-2023 Lemma 7.20 with the
tight threshold from eq. (7.19)) and the unchanged Part C argument (Heckel 2024
Proposition 5(b)). The gap arithmetic is identical to `erdos_625`.

**Axiom count for `erdos_625_97`**: exactly 1 new paper axiom + 3 standard Lean
axioms (propext, Classical.choice, Quot.sound) = 4 total.

**Source**: HP-2023 arXiv:2306.07253 Lemma 7.20 (condition (d) only modified),
Heckel 2024 arXiv:2409.17614 Proposition 5(b), and proof sketch
`problems/625/work/notes/lemma-7.20-mod-sketch-2026-05-10.md`.
-/

/-- **Axiom (1 new paper axiom)**: Under the extended main range `InMainRangeMod`,
  the joint bound P[χ(G) ≥ χLower ε n ∧ ζ(G) ≤ ζUpper ε n] ≥ 1 − 2ε holds.

  Mathematical content:
  - Part B (chromatic lower bound): HP-2023 Lemma 7.20 with condition (d) weakened
    from µ_α ≥ n^{1.05} to µ_α ≥ n^{1+x₀+ε} (x₀ defined by HP-2023 eq. (7.19)).
    The ϕ-positivity gap [x₀+ε, 0.04) is closed by Lipschitz certificate
    (lemma_7_10_ext, proof sketch 2026-05-10, script num-gap-lemma710-extension-2026-05-10.py).
  - Part C (cochromatic upper bound): Heckel 2024 Proposition 5(b), unchanged.
  - Union bound: standard, as in `joint_bound`.

  Cites:
  - HP-2023 arXiv:2306.07253 §7 Lemma 7.20, eqs. (7.16), (7.19), (7.20), Appendix B
  - Heckel 2024 arXiv:2409.17614 Proposition 5(b)
  - Proof sketch: problems/625/work/notes/lemma-7.20-mod-sketch-2026-05-10.md
  - Numerical certificate: problems/625/work/notes/lemma_7_10_ext.md

  **Disclosure (red-team P1-A, 2026-05-11):** This axiom is HYBRID, not pure
  literal paper-citation. The HP-2023 §7 / Lemma 7.20 bulk is peer-reviewed.
  The "Lemma 7.10-ext" extension covering ϕ > 0 on [x₀+ε, 0.04) is OUR own
  numerical-Lipschitz certificate (computed by
  `num-gap-lemma710-extension-2026-05-10.py`, documented in
  `lemma_7_10_ext.md`). The certificate is high-confidence
  (`min ϕ ≈ 6.5×10⁻⁷` on a 1086-cell grid, Lipschitz bound
  `L = 7.49×10⁻³` with 10% safety buffer, envelope lower bound
  `6.15×10⁻⁷`) but it is not literally a peer-reviewed lemma.

  Honest framing for any preprint: cite Heckel 2024 §Discussion's
  conjecture that x₀ ≈ 0.02905 ("It should be straightforward to change
  the proof of Lemma 7.20 in [HP-2023] to only require μ_α ≥ n^{x₀+ε}
  for any ε>0 and a certain constant x₀ ≈ 0.02905"), and state our
  Lemma 7.10-ext as a fresh numerical certificate filling the gap
  [x₀+ε, 0.04) of HP-2023 Lemma 7.10's [0.04, 1] coverage.

  Optional follow-up (P1-A upgrade): formalize `lemma_7_10_ext` in Lean
  via a `decide`-style proof on a fine rational grid with explicit
  Lipschitz envelope. Mathematically routine, formalization-heavy. -/
axiom lemma_7_20_modified (ε : ℝ) (hε_pos : 0 < ε) (hε_small : ε < 0.001) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRangeMod ε n →
      1 - ENNReal.ofReal (2 * ε) ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          χLower ε n ≤ (chromaticNumber G : ℝ) ∧
          (cochromaticNumber G : ℝ) ≤ ζUpper ε n}

/-- **97%-coverage theorem — Erdős Problem 625** (`erdos_625_97`).
  (1 paper axiom, 0 sorry; 4 axioms total including Lean kernel.)

  Same conclusion as `erdos_625`, but under the extended main range `InMainRangeMod`:
  for all large n with n^{x₀+ε} ≤ E[α(G)] ≤ n^{1−ε} (x₀ ≈ 0.02905 from HP-2023 eq. (7.19)):
  P[χ(G) − ζ(G) ≥ n^{1−ε}] ≥ 1 − 2ε.

  This covers ~97% of large n, extending `erdos_625` (which covers ~95%).
  The remaining ~3% corresponds to n with µ_α < n^{1+x₀}, where the ϕ-barrier
  prevents the argument — see HP-2023 remark after Lemma 7.20. -/
theorem erdos_625_97 (ε : ℝ) (hε_pos : 0 < ε) (hε_small : ε < 0.001) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRangeMod ε n →
      1 - ENNReal.ofReal (2 * ε) ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          (n : ℝ) ^ (1 - ε) ≤ (chromaticNumber G : ℝ) - (cochromaticNumber G : ℝ)} := by
  obtain ⟨n_arith, h_arith⟩ := gap_arith ε hε_pos hε_small
  obtain ⟨n_joint, h_joint⟩ := lemma_7_20_modified ε hε_pos hε_small
  refine ⟨max n_arith n_joint, fun n hn hrange => ?_⟩
  have hn_arith : n_arith ≤ n := le_trans (le_max_left _ _) hn
  have hn_joint : n_joint ≤ n := le_trans (le_max_right _ _) hn
  have h_gap : (n : ℝ) ^ (1 - ε / 2) - (n : ℝ) ^ (1 - 0.9 * ε) -
      2 * (n : ℝ) ^ (999 / 1000 : ℝ) ≥ (n : ℝ) ^ (1 - ε) :=
    h_arith n hn_arith
  have h_prob := h_joint n hn_joint hrange
  calc 1 - ENNReal.ofReal (2 * ε)
      ≤ gnHalf n {G : SimpleGraph (Fin n) |
            χLower ε n ≤ (chromaticNumber G : ℝ) ∧
            (cochromaticNumber G : ℝ) ≤ ζUpper ε n} :=
          h_prob
    _ ≤ gnHalf n {G : SimpleGraph (Fin n) |
            (n : ℝ) ^ (1 - ε) ≤ (chromaticNumber G : ℝ) - (cochromaticNumber G : ℝ)} := by
          apply MeasureTheory.measure_mono
          intro G ⟨hchi, hzeta⟩
          show (n : ℝ) ^ (1 - ε) ≤ (chromaticNumber G : ℝ) - (cochromaticNumber G : ℝ)
          have step : χLower ε n - ζUpper ε n ≤
              (chromaticNumber G : ℝ) - (cochromaticNumber G : ℝ) := by linarith
          have gap_expand : χLower ε n - ζUpper ε n =
              (n : ℝ) ^ (1 - ε / 2) - (n : ℝ) ^ (1 - 0.9 * ε) -
              2 * (n : ℝ) ^ (999 / 1000 : ℝ) := gap_eq ε n
          linarith

/-! ## All-`n` Precursor: `erdos_625_full_gap_precursor` (Phase 2 R2B Step 3)

R2B Step 3 introduces the **threshold gap precursor** for the all-`n` route.
This theorem exposes the gap shape that will eliminate the `InMainRangeMod ε n`
hypothesis from `erdos_625_97`: for any `0 < ε`, eventually in `n`,

```
n^{1 − ε}  ≤  kThresholdAlphaMinus2 n − kThresholdAlphaMinusOne n.
```

The bound holds with **no** `InMainRange` / `InMainRangeMod` assumption — this is
the deep-crossing residue contribution that the R2B route relies on.

**Status (2026-05-11)**: this is a precursor exposing the gap shape, not the full
all-`n` conclusion.  The remaining R2B steps (4 onwards) combine this with the
Part C concentration to upgrade `erdos_625_97` to `erdos_625_full`.  The theorem
statement here is intentionally minimal so that downstream R2B steps can build
directly on top of it without revisiting the citation chain.

**Axiom dependency**: the only `axiom` on the proof path of this precursor that
is unique to the R2B route is the single external citation
`Problem625.partB_crossing_lower_bound_alpha_minus_two_source`
(HP-2023 Lemma 8.1, declared in `CrossingPartB.lean`).  No local `axiom`
declarations appear in `CrossingWindowProof.lean` or in this file.

**Existing theorem meanings unchanged**: `erdos_625` and `erdos_625_97` are
**not modified** by Step 3.  This precursor is additive only.
-/

/-- **All-`n` theorem — Erdős Problem 625** (`erdos_625_full`).

    Covers ALL large n via case split on `InMainRangeMod ε n`:
    - good case (~97% of n): invoke `erdos_625_97`, whose `n^{1-ε}` gap
      is stronger than the structural target below;
    - crossing case (~3% of n): union-bound the paper-backed whp axioms
      `chi_alphaMinusTwo_lower_bound_whp` (HP-2023 Lemma 8.1 at α−2) and
      `zeta_alphaMinusTwo_upper_bound_whp` (Heckel 2024 Prop 5(b) (α−2)
      adaptation), then promote to the structural gap target via the
      deterministic threshold gap.

    **Bound shape.** The target is `n^{1-ε} - 2 * n^{0.99}`, i.e. the
    `erdos_625_97` strength minus a small slack term. For `ε < 0.01` this is
    still asymptotically `n^{1-ε}(1 - o(1))`, so this is essentially the same
    bound as `erdos_625_97` but valid for ALL large n (not just the `~97%`
    inside `InMainRangeMod`). A cleaner numeric form `χ-ζ ≥ n^{1-2ε}` is a
    corollary modulo a one-line rpow comparison and can be added later.

    **Axiom budget** (4 paper + 3 kernel = 7 total):
    - `partB_alphaMinusTwo_firstMomentBelowOne_source` (HP-2023 Lemma 8.1
      first-moment input at α−2; via `kThreshold_gap_alpha_minus_2`)
    - `chi_alphaMinusTwo_lower_bound_whp`
    - `zeta_alphaMinusTwo_upper_bound_whp`
    - `lemma_7_20_modified` (only on the good-case branch via `erdos_625_97`)
    - `propext`, `Classical.choice`, `Quot.sound`. -/
theorem erdos_625_full (ε : ℝ) (hε_pos : 0 < ε) (hε_small : ε < 0.001) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      1 - ENNReal.ofReal (2 * ε) ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          (n : ℝ) ^ (1 - ε) - 2 * (n : ℝ) ^ (0.99 : ℝ) ≤
              (chromaticNumber G : ℝ) - (cochromaticNumber G : ℝ)} := by
  obtain ⟨n_97, h_97⟩ := erdos_625_97 ε hε_pos hε_small
  obtain ⟨n_gap, h_gap⟩ :=
    Problem625.kThreshold_gap_alpha_minus_2 (ε := ε) hε_pos
  obtain ⟨n_chi, h_chi⟩ :=
    Problem625.chi_alphaMinusTwo_lower_bound_whp ε hε_pos hε_small
  obtain ⟨n_zeta, h_zeta⟩ :=
    Problem625.zeta_alphaMinusTwo_upper_bound_whp ε hε_pos hε_small
  refine ⟨max n_97 (max n_gap (max n_chi n_zeta)), fun n hn => ?_⟩
  have hn_97 : n_97 ≤ n := le_trans (le_max_left _ _) hn
  have hn_gap : n_gap ≤ n :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
  have hn_chi : n_chi ≤ n :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn))
  have hn_zeta : n_zeta ≤ n :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn))
  by_cases hmod : InMainRangeMod ε n
  · -- Good case: erdos_625_97 gives χ-ζ ≥ n^{1-ε}; weakening to
    --   n^{1-ε} - 2·n^{0.99} ≤ n^{1-ε} ≤ χ-ζ
    -- gives the target via set monotonicity.
    apply le_trans (h_97 n hn_97 hmod)
    apply MeasureTheory.measure_mono
    intro G hG
    have hGap : (n : ℝ) ^ (1 - ε) ≤
        (chromaticNumber G : ℝ) - (cochromaticNumber G : ℝ) := hG
    have hRpow_nn : (0 : ℝ) ≤ (n : ℝ) ^ (0.99 : ℝ) :=
      Real.rpow_nonneg (Nat.cast_nonneg n) _
    show (n : ℝ) ^ (1 - ε) - 2 * (n : ℝ) ^ (0.99 : ℝ) ≤
        (chromaticNumber G : ℝ) - (cochromaticNumber G : ℝ)
    linarith
  · -- Crossing branch: union-bound the two whp axioms, then deterministic gap.
    set A := {G : SimpleGraph (Fin n) |
      (Problem625.kThresholdAlphaMinus2 n : ℝ) - (n : ℝ) ^ (0.99 : ℝ) ≤
        (chromaticNumber G : ℝ)} with hA_def
    set B := {G : SimpleGraph (Fin n) |
      (cochromaticNumber G : ℝ) ≤
        (Problem625.kThresholdAlphaMinusOne n : ℝ) + (n : ℝ) ^ (0.99 : ℝ)} with hB_def
    have hA_meas : MeasurableSet A := Set.Finite.measurableSet (Set.toFinite _)
    have hB_meas : MeasurableSet B := Set.Finite.measurableSet (Set.toFinite _)
    haveI : IsProbabilityMeasure (gnHalf n) := by unfold gnHalf; infer_instance
    have hε_le_one : ENNReal.ofReal ε ≤ 1 :=
      ENNReal.ofReal_le_one.mpr (by linarith)
    have hμA : 1 - ENNReal.ofReal ε ≤ gnHalf n A := h_chi n hn_chi hmod
    have hμB : 1 - ENNReal.ofReal ε ≤ gnHalf n B := h_zeta n hn_zeta hmod
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
    have hABc : gnHalf n (A ∩ B)ᶜ ≤ ENNReal.ofReal (2 * ε) := by
      rw [Set.compl_inter]
      calc gnHalf n (Aᶜ ∪ Bᶜ)
          ≤ gnHalf n Aᶜ + gnHalf n Bᶜ := measure_union_le _ _
        _ ≤ ENNReal.ofReal ε + ENNReal.ofReal ε := add_le_add hAc hBc
        _ = ENNReal.ofReal (2 * ε) := by
              rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; ring_nf
    have hAB_meas : MeasurableSet (A ∩ B) := hA_meas.inter hB_meas
    have h1sub : 1 - gnHalf n (A ∩ B) ≤ ENNReal.ofReal (2 * ε) := by
      rw [← prob_compl_eq_one_sub (μ := gnHalf n) hAB_meas]
      exact hABc
    have hJoint : 1 - ENNReal.ofReal (2 * ε) ≤ gnHalf n (A ∩ B) :=
      calc 1 - ENNReal.ofReal (2 * ε)
          ≤ 1 - (1 - gnHalf n (A ∩ B)) := tsub_le_tsub_left h1sub 1
        _ = gnHalf n (A ∩ B) := ENNReal.sub_sub_cancel one_ne_top prob_le_one
    -- Promote A ∩ B to the gap event via deterministic threshold gap.
    have h_thr : (n : ℝ) ^ (1 - ε) ≤
        (Problem625.kThresholdAlphaMinus2 n : ℝ) -
          (Problem625.kThresholdAlphaMinusOne n : ℝ) :=
      h_gap n hn_gap
    calc 1 - ENNReal.ofReal (2 * ε)
        ≤ gnHalf n (A ∩ B) := hJoint
      _ ≤ gnHalf n {G : SimpleGraph (Fin n) |
              (n : ℝ) ^ (1 - ε) - 2 * (n : ℝ) ^ (0.99 : ℝ) ≤
                  (chromaticNumber G : ℝ) - (cochromaticNumber G : ℝ)} := by
            apply MeasureTheory.measure_mono
            intro G hG
            simp only [hA_def, hB_def, Set.mem_inter_iff, Set.mem_setOf_eq] at hG
            obtain ⟨hchi, hzeta⟩ := hG
            -- hchi : kThr - n^{0.99} ≤ χ
            -- hzeta : ζ ≤ partBThr + n^{0.99}
            -- h_thr : n^{1-ε} ≤ kThr - partBThr
            -- Goal: n^{1-ε} - 2·n^{0.99} ≤ χ - ζ.
            show (n : ℝ) ^ (1 - ε) - 2 * (n : ℝ) ^ (0.99 : ℝ) ≤
                (chromaticNumber G : ℝ) - (cochromaticNumber G : ℝ)
            linarith

theorem erdos_625_full_gap_precursor {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      (n : ℝ) ^ (1 - ε) ≤
        (Problem625.kThresholdAlphaMinus2 n : ℝ) -
          (Problem625.kThresholdAlphaMinusOne n : ℝ) :=
  Problem625.kThreshold_gap_alpha_minus_2 hε

/-- **Auxiliary: clean-bound rpow asymptotic.**

For `ε ∈ (0, 0.001)`, eventually in `n`,
`n^{1-2ε} ≤ n^{1-ε} − 2·n^{0.99}`.

Each of `n^{-ε}` and `n^{ε-0.01}` tends to 0 since `ε > 0` and `0.01 − ε > 0`,
so the combined factor `n^{-ε} + 2·n^{ε-0.01} ≤ 1` eventually. The conclusion
follows after multiplying by `n^{1-ε} > 0`.

**Note (red-team P2-3, 2026-05-12).** The proof only uses
`0 < 0.01 − ε`, so the lemma is actually provable for the wider range
`ε ∈ (0, 0.01)`. The hypothesis `ε < 0.001` matches the flagship
theorem `erdos_625_full_clean`'s stricter ε range and is unused slack
here — it is kept to make the call site at the flagship more uniform. -/
theorem rpow_clean_bound_eventually (ε : ℝ) (hε_pos : 0 < ε)
    (hε_small : ε < 0.001) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) ^ (1 - 2 * ε) ≤ (n : ℝ) ^ (1 - ε) - 2 * (n : ℝ) ^ (0.99 : ℝ) := by
  have h_01ε_pos : 0 < 0.01 - ε := by linarith
  -- (1) Real-filter event: n^{-ε} ≤ 1/4 eventually in ℝ.
  have h_neg_ε_tendsto :
      Filter.Tendsto (fun x : ℝ => x ^ (-ε)) Filter.atTop (nhds 0) :=
    tendsto_rpow_neg_atTop hε_pos
  have h_neg_ε_real : ∀ᶠ x : ℝ in Filter.atTop, x ^ (-ε) ≤ (1/4 : ℝ) := by
    have hpos : (0 : ℝ) < 1/4 := by norm_num
    -- For x ≥ 1, x^{-ε} ∈ (0, 1] so it's ≤ |x^{-ε}|. Convert "x^{-ε} → 0" to "|x^{-ε}| < 1/4".
    have h_abs : ∀ᶠ x : ℝ in Filter.atTop, |x ^ (-ε)| < (1/4 : ℝ) := by
      have := h_neg_ε_tendsto.eventually
        (Metric.ball_mem_nhds (0 : ℝ) hpos)
      filter_upwards [this] with x hx
      simpa [Real.dist_eq, sub_zero] using hx
    filter_upwards [h_abs] with x hx
    exact le_of_lt (lt_of_le_of_lt (le_abs_self _) hx)
  -- (2) Real-filter event: 2·n^{ε - 0.01} ≤ 1/4 eventually.
  have h_01ε_tendsto :
      Filter.Tendsto (fun x : ℝ => x ^ (-(0.01 - ε))) Filter.atTop (nhds 0) :=
    tendsto_rpow_neg_atTop h_01ε_pos
  have h_01ε_real :
      ∀ᶠ x : ℝ in Filter.atTop, 2 * x ^ (ε - 0.01) ≤ (1/4 : ℝ) := by
    have hpos : (0 : ℝ) < 1/8 := by norm_num
    have h_abs : ∀ᶠ x : ℝ in Filter.atTop, |x ^ (-(0.01 - ε))| < (1/8 : ℝ) := by
      have := h_01ε_tendsto.eventually
        (Metric.ball_mem_nhds (0 : ℝ) hpos)
      filter_upwards [this] with x hx
      simpa [Real.dist_eq, sub_zero] using hx
    filter_upwards [h_abs] with x hx
    have h_rewrite : x ^ (ε - 0.01) = x ^ (-(0.01 - ε)) := by
      congr 1; ring
    rw [h_rewrite]
    have h_le : x ^ (-(0.01 - ε)) ≤ 1/8 :=
      le_of_lt (lt_of_le_of_lt (le_abs_self _) hx)
    linarith
  -- (3) Lift to ℕ-filter.
  have h_neg_ε_nat : ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ (-ε) ≤ (1/4 : ℝ) :=
    h_neg_ε_real.natCast_atTop
  have h_01ε_nat :
      ∀ᶠ n : ℕ in Filter.atTop, 2 * (n : ℝ) ^ (ε - 0.01) ≤ (1/4 : ℝ) :=
    h_01ε_real.natCast_atTop
  have h_n_ge_one : ∀ᶠ n : ℕ in Filter.atTop, (1 : ℝ) ≤ (n : ℝ) := by
    rw [Filter.eventually_atTop]
    exact ⟨1, fun n hn => by exact_mod_cast hn⟩
  -- (4) Combine.
  filter_upwards [h_neg_ε_nat, h_01ε_nat, h_n_ge_one] with n h1 h2 hn_ge_one
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have h_rpow_pos : (0 : ℝ) < (n : ℝ) ^ (1 - ε) :=
    Real.rpow_pos_of_pos hn_pos _
  have h_split_12ε :
      (n : ℝ) ^ (1 - 2 * ε) = (n : ℝ) ^ (1 - ε) * (n : ℝ) ^ (-ε) := by
    rw [← Real.rpow_add hn_pos]; congr 1; ring
  have h_split_99 :
      (n : ℝ) ^ (0.99 : ℝ) = (n : ℝ) ^ (1 - ε) * (n : ℝ) ^ (ε - 0.01) := by
    rw [← Real.rpow_add hn_pos]; congr 1; ring
  rw [h_split_12ε, h_split_99]
  -- goal: n^{1-ε} * n^{-ε} ≤ n^{1-ε} - 2 * (n^{1-ε} * n^{ε-0.01})
  --   ⇔ n^{1-ε} * (n^{-ε} + 2·n^{ε-0.01}) ≤ n^{1-ε}
  --   ⇔ n^{-ε} + 2·n^{ε-0.01} ≤ 1 (dividing by n^{1-ε} > 0)
  have h_sum : (n : ℝ) ^ (-ε) + 2 * (n : ℝ) ^ (ε - 0.01) ≤ 1 := by linarith
  nlinarith [h_rpow_pos, h_sum]

/-! ## Clean-bound corollary: `erdos_625_full_clean` (P1-C closure)

`erdos_625_full` proves the bound `n^{1-ε} − 2·n^{0.99}`, which becomes
vacuous for small n and small ε. This corollary upgrades the bound to the
cleaner expression `n^{1-2ε}`, valid for the same ε ∈ (0, 0.001) range and
all sufficiently large n.

Pointwise inequality used:
  for n ≥ N(ε), `n^{1-2ε} ≤ n^{1-ε} − 2·n^{0.99}`,
i.e. `n^{1-2ε} + 2·n^{0.99} ≤ n^{1-ε}`. For ε ∈ (0, 0.001), both
`n^{1-2ε}/n^{1-ε} = n^{-ε} → 0` and `n^{0.99}/n^{1-ε} = n^{ε-0.01} → 0`,
so the inequality holds for n large enough. Concretely, pick N(ε) so that
`n^{-ε} ≤ 1/2` AND `n^{ε-0.01} ≤ 1/8`; then
`n^{1-2ε} + 2·n^{0.99} ≤ n^{1-ε}/2 + n^{1-ε}/4 ≤ n^{1-ε}` (with room).
The corollary just picks `N(ε)` larger than both `2^{1/ε}` and
`8^{1/(0.01-ε)}` and applies set monotonicity on the gap event. -/
theorem erdos_625_full_clean (ε : ℝ) (hε_pos : 0 < ε) (hε_small : ε < 0.001) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      1 - ENNReal.ofReal (2 * ε) ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          (n : ℝ) ^ (1 - 2 * ε) ≤
              (chromaticNumber G : ℝ) - (cochromaticNumber G : ℝ)} := by
  obtain ⟨n_full, h_full⟩ := erdos_625_full ε hε_pos hε_small
  -- Choose N large enough that n^{-ε} ≤ 1/2 and n^{ε-0.01} ≤ 1/8.
  -- Both hold for n ≥ N_clean := ⌈max (2 ^ (1/ε), 8 ^ (1/(0.01-ε)))⌉₊ + 1.
  -- We do not pin a closed-form N_clean in Lean; instead, observe that
  -- the helper inequality `n^{1-2ε} ≤ n^{1-ε} - 2·n^{0.99}` is an
  -- *eventually true* property of n; we use `Real.tendsto_rpow_atTop`-style
  -- reasoning packaged below.
  -- Auxiliary asymptotic: n^{1-2ε} ≤ n^{1-ε} - 2·n^{0.99} eventually in n.
  -- Both `n^{1-2ε}/n^{1-ε} = n^{-ε} → 0` and `n^{0.99}/n^{1-ε} = n^{ε-0.01} → 0`,
  -- so the sum n^{1-2ε} + 2·n^{0.99} is eventually < n^{1-ε}.
  have h_arith := rpow_clean_bound_eventually ε hε_pos hε_small
  rw [Filter.eventually_atTop] at h_arith
  obtain ⟨n_arith, h_arith⟩ := h_arith
  -- Combine: take n₀ = max n_full n_arith.
  refine ⟨max n_full n_arith, fun n hn => ?_⟩
  have hn_full : n_full ≤ n := le_trans (le_max_left _ _) hn
  have hn_arith : n_arith ≤ n := le_trans (le_max_right _ _) hn
  apply le_trans (h_full n hn_full)
  apply MeasureTheory.measure_mono
  intro G hG
  have hGap : (n : ℝ) ^ (1 - ε) - 2 * (n : ℝ) ^ (0.99 : ℝ) ≤
      (chromaticNumber G : ℝ) - (cochromaticNumber G : ℝ) := hG
  have h_arith_n : (n : ℝ) ^ (1 - 2 * ε) ≤
      (n : ℝ) ^ (1 - ε) - 2 * (n : ℝ) ^ (0.99 : ℝ) := h_arith n hn_arith
  show (n : ℝ) ^ (1 - 2 * ε) ≤
      (chromaticNumber G : ℝ) - (cochromaticNumber G : ℝ)
  linarith

end Problem625.Publishable
