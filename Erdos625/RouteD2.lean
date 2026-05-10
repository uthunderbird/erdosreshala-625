import Mathlib.Data.Real.Basic
import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Erdos625.Defs
import Erdos625.GapArithmetic
import Erdos625.FirstMomentThreshold
import Erdos625.ChromaticConnection
import Erdos625.ZetaConcentration

/-!
# Problem 625 — Route D-2: Final Conditional Theorem

Closes the formalization using a proved Part B (χ lower bound) and one axiom for
Part C (ζ upper bound). The arithmetic cancellation (gap_formula_cancellation,
gap_asymptotic_heckel) is proved sorry-free in GapArithmetic.

**Axiom inventory** (0 in this file; expected upstream dependency boundary after wiring):
- `kThresholdWitness_le_n_div_threshold` (ChromaticConnection.lean) — Part B witness estimate
- `heckel_zeta_mean_upper_bound` (ZetaConcentration.lean) — mean estimate for ζ
- `heckel_zeta_upper_bound` is now a THEOREM proved in ZetaConcentration.lean
  (from the mean axiom + Azuma-Hoeffding infrastructure, **0 sorry**)

Note: the last completed RouteD2 target verification predates this wiring edit. A fresh RouteD2
target check is still pending because dependency replay was resource-heavy.

**Honest status**: The main theorem `gnHalf_gap_ge_n_pow_one_minus_eps` now uses:
- Part B: `heckel_chromatic_lower_bound_of_paper_bridge`
  (proved conditionally via ChromaticConnection + FirstMomentThreshold + PartBProfileBridge;
   depends on `profileLogCoreBridgeTarget_source`, which replaces the old live axiom
   `threshold_tBoundedColoringError_le_with_error` with a paper-backed bridge)
- Part C: `heckel_zeta_upper_bound` (theorem, ZetaConcentration.lean, **0 sorry, 1 axiom**)
-/

namespace Problem625

open MeasureTheory ProbabilityTheory ENNReal

-- Note: `heckel_zeta_upper_bound` is now a theorem proved in ZetaConcentration.lean.
-- It is imported above and used directly below.
-- The remaining axiom is `heckel_zeta_mean_upper_bound` (ZetaConcentration.lean).

/-! ## Route D-3: Decomposing the joint bound into Part B + Part C -/

section RouteD3Decomposition

/-- The joint bound follows from Part B (`h_chi`) + Part C (`h_zeta`), combined via a union
  bound on complements. The witness is `kThresholdWitness`.

  The `h_meas_chi` / `h_meas_zeta` hypotheses assert measurability of the relevant
  event sets — a standard side condition that any concrete probabilistic axiom must supply.
-/
theorem heckel_probabilistic_bounds_from_split (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (h_meas_chi : ∀ n : ℕ,
        MeasurableSet {G : SimpleGraph (Fin n) |
          kThresholdWitness n - (n : ℝ)^(1 - 0.9 * ε) ≤ (chromaticNumber G : ℝ)})
    (h_meas_zeta : ∀ n : ℕ,
        MeasurableSet {G : SimpleGraph (Fin n) |
          (cochromaticNumber G : ℝ) ≤
            kThresholdWitness n - (n : ℝ)^(1 - ε / 2) + 2 * (n : ℝ)^(999 / 1000 : ℝ)})
    (h_chi : ∃ n₀_B : ℕ, ∀ n : ℕ, n₀_B ≤ n → InMainRange ε n →
      1 - ENNReal.ofReal ε ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          kThresholdWitness n - (n : ℝ)^(1 - 0.9 * ε) ≤ (chromaticNumber G : ℝ)})
    (h_zeta : ∃ n₀_C : ℕ, ∀ n : ℕ, n₀_C ≤ n → InMainRange ε n →
      1 - ENNReal.ofReal ε ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          (cochromaticNumber G : ℝ) ≤
            kThresholdWitness n - (n : ℝ)^(1 - ε / 2) + 2 * (n : ℝ)^(999 / 1000 : ℝ)}) :
    ∃ k_t : ℕ → ℝ,
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
      1 - ENNReal.ofReal (2 * ε) ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          k_t n - (n : ℝ)^(1 - 0.9 * ε) ≤ (chromaticNumber G : ℝ) ∧
          (cochromaticNumber G : ℝ) ≤
            k_t n - (n : ℝ)^(1 - ε / 2) + 2 * (n : ℝ)^(999 / 1000 : ℝ)} := by
  obtain ⟨n₀_B, h_B⟩ := h_chi
  obtain ⟨n₀_C, h_C⟩ := h_zeta
  refine ⟨kThresholdWitness, max n₀_B n₀_C, fun n hn hrange => ?_⟩
  have hn_B : n₀_B ≤ n := le_trans (le_max_left _ _) hn
  have hn_C : n₀_C ≤ n := le_trans (le_max_right _ _) hn
  -- Let A = χ-event, B = ζ-event, μ = gnHalf n (IsProbabilityMeasure)
  -- Goal: μ(A ∩ B) ≥ 1 - 2ε
  -- Strategy: μ((A∩B)ᶜ) = μ(Aᶜ ∪ Bᶜ) ≤ μ(Aᶜ) + μ(Bᶜ) ≤ ε + ε = 2ε
  --           so μ(A∩B) = 1 - μ((A∩B)ᶜ) ≥ 1 - 2ε
  set A := {G : SimpleGraph (Fin n) |
      kThresholdWitness n - (n : ℝ)^(1 - 0.9 * ε) ≤ (chromaticNumber G : ℝ)} with hA_def
  set B := {G : SimpleGraph (Fin n) |
      (cochromaticNumber G : ℝ) ≤
        kThresholdWitness n - (n : ℝ)^(1 - ε / 2) + 2 * (n : ℝ)^(999 / 1000 : ℝ)} with hB_def
  have hA_meas : MeasurableSet A := h_meas_chi n
  have hB_meas : MeasurableSet B := h_meas_zeta n
  have hAB_meas : MeasurableSet (A ∩ B) := hA_meas.inter hB_meas
  haveI : IsProbabilityMeasure (gnHalf n) := by
    unfold gnHalf
    infer_instance
  have hμA : 1 - ENNReal.ofReal ε ≤ gnHalf n A := h_B n hn_B hrange
  have hμB : 1 - ENNReal.ofReal ε ≤ gnHalf n B := h_C n hn_C hrange
  -- μ(Aᶜ) ≤ ε  (from μ(Aᶜ) = 1 - μ(A) ≤ 1 - (1-ε) = ε)
  have hε_le_one : ENNReal.ofReal ε ≤ 1 := by
    apply ENNReal.ofReal_le_one.mpr; linarith
  have hAc : gnHalf n Aᶜ ≤ ENNReal.ofReal ε := by
    rw [prob_compl_eq_one_sub hA_meas]
    calc 1 - gnHalf n A ≤ 1 - (1 - ENNReal.ofReal ε) := tsub_le_tsub_left hμA 1
      _ = ENNReal.ofReal ε := ENNReal.sub_sub_cancel one_ne_top hε_le_one
  have hBc : gnHalf n Bᶜ ≤ ENNReal.ofReal ε := by
    rw [prob_compl_eq_one_sub hB_meas]
    calc 1 - gnHalf n B ≤ 1 - (1 - ENNReal.ofReal ε) := tsub_le_tsub_left hμB 1
      _ = ENNReal.ofReal ε := ENNReal.sub_sub_cancel one_ne_top hε_le_one
  -- μ((A∩B)ᶜ) = μ(Aᶜ ∪ Bᶜ) ≤ μ(Aᶜ) + μ(Bᶜ) ≤ 2ε
  have hABc_le : gnHalf n (A ∩ B)ᶜ ≤ ENNReal.ofReal (2 * ε) := by
    rw [Set.compl_inter]
    calc gnHalf n (Aᶜ ∪ Bᶜ)
        ≤ gnHalf n Aᶜ + gnHalf n Bᶜ := measure_union_le _ _
      _ ≤ ENNReal.ofReal ε + ENNReal.ofReal ε := add_le_add hAc hBc
      _ = ENNReal.ofReal (2 * ε) := by
          rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; ring_nf
  -- Goal: 1 - 2ε ≤ μ(A∩B). Rewrite goal set, then use μ(A∩B) = 1 - μ((A∩B)ᶜ) ≥ 1 - 2ε
  have goal_set : {G : SimpleGraph (Fin n) |
      kThresholdWitness n - (n : ℝ)^(1 - 0.9 * ε) ≤ (chromaticNumber G : ℝ) ∧
      (cochromaticNumber G : ℝ) ≤
        kThresholdWitness n - (n : ℝ)^(1 - ε / 2) + 2 * (n : ℝ)^(999 / 1000 : ℝ)} = A ∩ B := by
    simp [hA_def, hB_def, Set.inter_def]
  rw [goal_set]
  -- goal: 1 - ofReal(2ε) ≤ μ(A∩B)
  -- from hABc_le: μ((A∩B)ᶜ) ≤ 2ε, and prob_compl: μ((A∩B)ᶜ) = 1 - μ(A∩B)
  -- so 1 - μ(A∩B) ≤ 2ε, i.e. 1 - 2ε ≤ μ(A∩B) (in ENNReal, using tsub_le_tsub_left)
  have hABc_eq : gnHalf n (A ∩ B)ᶜ = 1 - gnHalf n (A ∩ B) :=
    prob_compl_eq_one_sub hAB_meas
  have h1sub : 1 - gnHalf n (A ∩ B) ≤ ENNReal.ofReal (2 * ε) := hABc_eq ▸ hABc_le
  calc 1 - ENNReal.ofReal (2 * ε)
      ≤ 1 - (1 - gnHalf n (A ∩ B)) := tsub_le_tsub_left h1sub 1
    _ = gnHalf n (A ∩ B) := ENNReal.sub_sub_cancel one_ne_top prob_le_one

end RouteD3Decomposition

/-! ## Main Gap Theorem -/

section RouteD2

/-- **Route D-2: Main gap theorem** — uses proved Part B + axiom for Part C

  For ε ∈ (0, 0.001) and n in the main range (n^{0.05+ε} ≤ μ_α ≤ n^{1-ε}),
  with probability ≥ 1 − 2ε:

      χ(G(n,1/2)) − ζ(G(n,1/2)) ≥ n^{1-ε}

  **Proof structure**:
  1. Part B (proved): `heckel_chromatic_lower_bound_of_paper_bridge` — whp χ(G) ≥ k_t − n^{1-0.9ε}
     Depends on `profileLogCoreBridgeTarget_source` (paper-backed axiom, HP-2023 Lemma 5 +
     eq:wert/eq:wert2), which replaced the old wrong-direction
     `kThresholdWitness_le_n_div_threshold` and the direct live axiom
     `threshold_tBoundedColoringError_le_with_error`.
  2. Part C (proved theorem, 1 paper axiom, 0 sorry): `heckel_zeta_upper_bound` — whp ζ(G) ≤ k_t − n^{1-ε/2} + 2n^{0.999}
  3. Combined via `heckel_probabilistic_bounds_from_split` (union bound on complements).
  4. From gap_asymptotic_heckel: k₁ − k₂ ≥ n^{1-ε} (arithmetic, proved).
  5. On the joint event: χ(G) − ζ(G) ≥ k₁ − k₂ ≥ n^{1-ε} (k_t cancels).

  **Checked axiom count (2026-05-10)**: 2
  - `profileLogCoreBridgeTarget_source` (PartBProfileBridge.lean:16890, HP-2023 arXiv:2306.07253 Lemma 5 + eq:wert/eq:wert2)
  - `heckel_cochromatic_second_moment` (ZetaConcentration.lean:1406, Heckel 2024 arXiv:2409.17614 Proposition 5(2))
  **Sorry count in checked dependency path**: 0

  Sources:
  - Heckel, A. (2024). arXiv:2409.17614, Theorem 1.
  - Heckel, A. & Panagiotou, K. (2023). arXiv:2306.07253, Lemma 8.1.
-/
theorem gnHalf_gap_ge_n_pow_one_minus_eps (ε : ℝ) (hε_pos : 0 < ε) (hε_small : ε < 0.001) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
      1 - ENNReal.ofReal (2 * ε) ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          (n : ℝ)^(1 - ε) ≤
            (chromaticNumber G : ℝ) - (cochromaticNumber G : ℝ)} := by
  obtain ⟨n_arith, h_arith⟩ := gap_asymptotic_heckel ε hε_pos hε_small
  -- Part B: χ lower bound (legacy checked route; the wired replacement is blocked
  -- by the direction audit for `kThresholdWitness_le_n_div_threshold`).
  obtain ⟨n₀_B, h_B⟩ := heckel_chromatic_lower_bound_of_paper_bridge ε hε_pos hε_small
  -- Part C: ζ upper bound (axiom — requires Proposition 5(b) + Azuma-Hoeffding)
  obtain ⟨n₀_C, h_C⟩ := heckel_zeta_upper_bound ε hε_pos (by linarith)
  -- Measurability (finite sets of graphs on Fin n are measurable)
  have h_meas_chi : ∀ n : ℕ,
      MeasurableSet {G : SimpleGraph (Fin n) |
        kThresholdWitness n - (n : ℝ)^(1 - 0.9 * ε) ≤ (chromaticNumber G : ℝ)} :=
    fun n => Set.Finite.measurableSet (Set.toFinite _)
  have h_meas_zeta : ∀ n : ℕ,
      MeasurableSet {G : SimpleGraph (Fin n) |
        (cochromaticNumber G : ℝ) ≤
          kThresholdWitness n - (n : ℝ)^(1 - ε / 2) + 2 * (n : ℝ)^(999 / 1000 : ℝ)} :=
    fun n => Set.Finite.measurableSet (Set.toFinite _)
  -- Combine Part B + Part C via union-bound decomposition
  obtain ⟨k_t, n_prob, h_prob⟩ :=
    heckel_probabilistic_bounds_from_split ε hε_pos (by linarith)
      h_meas_chi h_meas_zeta
      ⟨n₀_B, h_B⟩
      ⟨n₀_C, h_C⟩
  refine ⟨max n_arith n_prob, fun n hn hrange => ?_⟩
  have hn_arith : n_arith ≤ n := le_trans (le_max_left _ _) hn
  have hn_prob  : n_prob ≤ n  := le_trans (le_max_right _ _) hn
  have h_gap   := h_arith n hn_arith
  have h_joint := h_prob n hn_prob hrange
  calc 1 - ENNReal.ofReal (2 * ε)
      ≤ gnHalf n {G : SimpleGraph (Fin n) |
            k_t n - (n : ℝ)^(1 - 0.9 * ε) ≤ (chromaticNumber G : ℝ) ∧
            (cochromaticNumber G : ℝ) ≤
              k_t n - (n : ℝ)^(1 - ε / 2) + 2 * (n : ℝ)^(999 / 1000 : ℝ)} :=
          h_joint
    _ ≤ gnHalf n {G : SimpleGraph (Fin n) |
            (n : ℝ)^(1 - ε) ≤ (chromaticNumber G : ℝ) - (cochromaticNumber G : ℝ)} := by
        apply MeasureTheory.measure_mono
        intro G ⟨hchi, hzeta⟩
        set χv := (chromaticNumber G : ℝ)
        set ζv := (cochromaticNumber G : ℝ)
        set A  := (n : ℝ)^(1 - 0.9 * ε)
        set B  := (n : ℝ)^(1 - ε / 2)
        set C  := (n : ℝ)^(999 / 1000 : ℝ)
        set D  := (n : ℝ)^(1 - ε)
        have step1 : B - A - 2 * C ≤ χv - ζv := by linarith
        exact le_trans h_gap step1

/-- Main gap theorem via the fully proved exact-no-empty Part B chain.

  **Checked axiom count (2026-05-10)**: 3
  - `paperPartBThresholdAverageClassAsymptoticLowerCriterionTarget_source` (PartBProfileBridge.lean, HP-2023 arXiv:2306.07253 lemma:averagecolourclass)
  - `paperPartBExactNoEmptyDenomBinaryLowerControlledLhsDecayTarget_source` (PartBProfileBridge.lean, HP-2023 arXiv:2306.07253 eq:wert/eq:wert2)
  - `heckel_cochromatic_second_moment` (ZetaConcentration.lean, Heckel 2024 arXiv:2409.17614 Proposition 5(2))

  Note: `heckel_zeta_mean_upper_bound` is a proved theorem (ZetaConcentration.lean:1587), not an axiom.
  **Sorry count**: 0
-/
theorem gnHalf_gap_ge_n_pow_one_minus_eps_of_exactNoEmpty
    (ε : ℝ) (hε_pos : 0 < ε) (hε_small : ε < 0.001) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
      1 - ENNReal.ofReal (2 * ε) ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          (n : ℝ)^(1 - ε) ≤
            (chromaticNumber G : ℝ) - (cochromaticNumber G : ℝ)} := by
  obtain ⟨n_arith, h_arith⟩ := gap_asymptotic_heckel ε hε_pos hε_small
  -- Part B: χ lower bound via exact-no-empty proved chain (0 sorrys, 2 paper axioms)
  obtain ⟨n₀_B, h_B⟩ := heckel_chromatic_lower_bound_of_exactNoEmpty ε hε_pos hε_small
  -- Part C: ζ upper bound (axiom — requires Proposition 5(b) + Azuma-Hoeffding)
  obtain ⟨n₀_C, h_C⟩ := heckel_zeta_upper_bound ε hε_pos (by linarith)
  have h_meas_chi : ∀ n : ℕ,
      MeasurableSet {G : SimpleGraph (Fin n) |
        kThresholdWitness n - (n : ℝ)^(1 - 0.9 * ε) ≤ (chromaticNumber G : ℝ)} :=
    fun n => Set.Finite.measurableSet (Set.toFinite _)
  have h_meas_zeta : ∀ n : ℕ,
      MeasurableSet {G : SimpleGraph (Fin n) |
        (cochromaticNumber G : ℝ) ≤
          kThresholdWitness n - (n : ℝ)^(1 - ε / 2) + 2 * (n : ℝ)^(999 / 1000 : ℝ)} :=
    fun n => Set.Finite.measurableSet (Set.toFinite _)
  obtain ⟨k_t, n_prob, h_prob⟩ :=
    heckel_probabilistic_bounds_from_split ε hε_pos (by linarith)
      h_meas_chi h_meas_zeta
      ⟨n₀_B, h_B⟩
      ⟨n₀_C, h_C⟩
  refine ⟨max n_arith n_prob, fun n hn hrange => ?_⟩
  have hn_arith : n_arith ≤ n := le_trans (le_max_left _ _) hn
  have hn_prob  : n_prob ≤ n  := le_trans (le_max_right _ _) hn
  have h_gap   := h_arith n hn_arith
  have h_joint := h_prob n hn_prob hrange
  calc 1 - ENNReal.ofReal (2 * ε)
      ≤ gnHalf n {G : SimpleGraph (Fin n) |
            k_t n - (n : ℝ)^(1 - 0.9 * ε) ≤ (chromaticNumber G : ℝ) ∧
            (cochromaticNumber G : ℝ) ≤
              k_t n - (n : ℝ)^(1 - ε / 2) + 2 * (n : ℝ)^(999 / 1000 : ℝ)} :=
          h_joint
    _ ≤ gnHalf n {G : SimpleGraph (Fin n) |
            (n : ℝ)^(1 - ε) ≤ (chromaticNumber G : ℝ) - (cochromaticNumber G : ℝ)} := by
        apply MeasureTheory.measure_mono
        intro G ⟨hchi, hzeta⟩
        set χv := (chromaticNumber G : ℝ)
        set ζv := (cochromaticNumber G : ℝ)
        set A  := (n : ℝ)^(1 - 0.9 * ε)
        set B  := (n : ℝ)^(1 - ε / 2)
        set C  := (n : ℝ)^(999 / 1000 : ℝ)
        set D  := (n : ℝ)^(1 - ε)
        have step1 : B - A - 2 * C ≤ χv - ζv := by linarith
        exact le_trans h_gap step1

end RouteD2

end Problem625
-- Axiom audit
-- Axiom audit
