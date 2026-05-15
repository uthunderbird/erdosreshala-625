import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Adapted
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Erdos625.Defs
import Erdos625.FirstMomentThreshold
import Erdos625.BoundedDifferences
import Erdos625.IndepMoments

/-!
# Problem 625 — ζ Concentration via Azuma-Hoeffding

This file factors the `heckel_zeta_upper_bound` axiom (formerly in RouteD2.lean) into:

1. **Proved theorem** (this file): Mean estimate `heckel_zeta_mean_upper_bound`
   — E[ζ(G(n,1/2))] ≤ kThresholdWitness(n) − n^{1−ε/2} + n^{0.999}
   (0 sorry; proved by contradiction using Paley-Zygmund + Azuma lower tail)

2. **Theorem** (this file): Azuma-Hoeffding tail bound `zeta_azuma_tail_bound`
   — P[ζ(G) ≥ E[ζ] + t] ≤ exp(−t²/2n)
   Proved via Mathlib's `measure_sum_ge_le_of_hasCondSubgaussianMGF` + vertex-exposure filtration.

3. **Theorem** (this file): Exponential decay `zeta_exp_decay_eventually_le`
   — exp(−n^{0.998}/2) ≤ ε eventually
   Proved by Archimedean property and `Real.tendsto_rpow_atTop_of_pos`.

4. **Theorem** (this file): `heckel_zeta_upper_bound`
   — fully proved from (1) + (2) + (3). No axiom; 0 sorry for the outer theorem.

**CURRENT STATE (verified 2026-05-13; updated after named source-seam cleanup)**:
0 local proof placeholders in this module, 1 load-bearing axiom, and one
architectural source seam:
- `heckel_offdiag_term_bound` (load-bearing axiom, Heckel 2024 Proposition 5(b) off-diagonal term; a 2026-05-11 narrowing of the original `heckel_cochromatic_second_moment`, which is now a proved theorem on top of `heckel_offdiag_term_bound`; the proved theorem is what `heckel_zeta_paley_zygmund` consumes)
- `heckel_zeta_upper_tail`, `heckel_zeta_lower_tail` (non-load-bearing axioms; refine the axiom structure but not used in main proof chain)
- `heckel_zeta_mean_bound_from_upper_tail_source`: source seam for the architectural theorem showing derivation route; NOT used in main proof
- `heckel_zeta_mean_upper_bound`: PROVED theorem (0 sorry; proved by contradiction using Paley-Zygmund + Azuma lower tail)
- `zeta_azuma_tail_bound`, `zeta_azuma_lower_tail_bound`, `zeta_exp_decay_eventually_le`: all PROVED (0 sorry).
- `zeta_layer_decomposition`: proved (0 sorry) — E[ζ] = Σ_{k<n} P[ζ > k] via layer decomposition.
All Azuma/Doob infrastructure proved: `doobDiff_telescope`, `doobDiff_hasCondSubgaussianMGF`. Build: clean.

**Session history:**
Session 58: `zeta_exp_decay_eventually_le` proved (no sorry).
Session 59: `instStandardBorelSpaceGraph` proved (closes one Azuma barrier).
Session 60: Vertex-exposure filtration infrastructure added (no sorry):
  - `vertexExposureMSpace n i`, `vertexExposureFiltration_mono`, `vertexExposureMSpace_le_top`
  - `vertexExposureFiltration n`, `cochromaticNumber_measurable`, `doobMartingale_stronglyAdapted`
Later sessions: `doobDiff_telescope` and `doobDiff_hasCondSubgaussianMGF` proved (0 sorry).

## Proof sketch for the vertex-exposure martingale component

Define filtration ℱ_i = σ(edges incident to vertices 0, …, i−1) on SimpleGraph (Fin n).
Define Doob martingale M_i G = 𝔼[ζ(G) | ℱ_i]. Then:
- ζ(G) − 𝔼[ζ(G)] = Σᵢ (M_i − M_{i-1})  (telescope)
- |M_i − M_{i-1}| ≤ 1  (by `cochromaticNumber_bounded_diff_singleton`, BoundedDifferences.lean)
- Each difference is in [−1, 1] with conditional mean 0 → conditionally sub-Gaussian with c = 1
- Apply `measure_sum_ge_le_of_hasCondSubgaussianMGF` with n steps and cY i = 1:
    P[Σ Y_i ≥ t] ≤ exp(−t²/(2n))

## References
- Heckel, A. (2024). arXiv:2409.17614
- McDiarmid, C. (1989). On the method of bounded differences.
- Mathlib: `measure_sum_ge_le_of_hasCondSubgaussianMGF`
-/

namespace Problem625

open MeasureTheory ProbabilityTheory Real ENNReal

-- Required instances for finite graph probability space

private instance instMeasurableSingletonGraph (n : ℕ) :
    MeasurableSingletonClass (SimpleGraph (Fin n)) := by
  constructor; intro G
  have heq : ({G} : Set (SimpleGraph (Fin n))) = SimpleGraph.Adj ⁻¹' {G.Adj} := by
    ext H; simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => h ▸ rfl, SimpleGraph.ext⟩
  rw [heq]
  exact SimpleGraph.measurable_adj (MeasurableSet.singleton G.Adj)

/-- `SimpleGraph (Fin n)` is a standard Borel space.
  Chain: `Fintype (SimpleGraph (Fin n))` (Mathlib Basic.lean:114) →
  `Countable` → `MeasurableSingletonClass` (proved above) →
  `DiscreteMeasurableSpace` (MeasurableSingletonClass.toDiscreteMeasurableSpace,
    Defs.lean:549) → `StandardBorelSpace`
  (standardBorelSpace_of_discreteMeasurableSpace, Polish/Basic.lean:120). -/
instance instStandardBorelSpaceGraph (n : ℕ) :
    StandardBorelSpace (SimpleGraph (Fin n)) :=
  inferInstance

/-! ## Vertex-Exposure Filtration on SimpleGraph (Fin n)

We define the vertex-exposure filtration ℱ_i on `SimpleGraph (Fin n)` — the σ-algebra
generated by all edge-indicator events `{G | G.Adj u w = b}` for pairs with `u.val < i` or
`w.val < i`.  Because `SimpleGraph (Fin n)` carries the discrete measurable space (all
singletons measurable, proved via `instMeasurableSingletonGraph`), every set is measurable
and the filtration satisfies its monotonicity condition trivially.

Two adjacent lemmas are proved here (both 0-sorry, directly used in the Azuma/Doob setup):
1. `vertexExposureFiltration_mono` — the filtration is monotone in i.
2. `cochromaticNumber_stronglyAdapted` — the cochromatic-number process is strongly adapted.
-/

section VertexExposureFiltration

/-- The vertex-exposure σ-algebra at stage `i`: the σ-algebra generated by all edge-indicator
    events `{G : SimpleGraph (Fin n) | G.Adj u w = b}` for pairs `(u, w)` where `u.val < i`.
    Stage 0 is trivial (no vertices revealed); stage n exposes all adjacencies from vertices
    0, …, n−1, recovering the full (discrete) σ-algebra.

    This σ-algebra is a **sub**-σ-algebra of the ambient discrete measurable space on
    `SimpleGraph (Fin n)` (every generator is a union of singletons, hence measurable). -/
@[reducible]
def vertexExposureMSpace (n i : ℕ) : MeasurableSpace (SimpleGraph (Fin n)) :=
  MeasurableSpace.generateFrom
    {S : Set (SimpleGraph (Fin n)) |
      ∃ (u : Fin n) (_ : u.val < i) (w : Fin n) (b : Bool),
        S = {G : SimpleGraph (Fin n) | G.Adj u w = b}}

/-- The vertex-exposure filtration is monotone: revealing more vertices gives a larger σ-algebra.

    **Proof**: For `i ≤ j`, every generator of `vertexExposureMSpace n i` (which has witness
    `u.val < i`) also satisfies `u.val < j`, so it is a generator of `vertexExposureMSpace n j`.
    `generateFrom_mono` then gives the monotonicity. -/
theorem vertexExposureFiltration_mono (n : ℕ) {i j : ℕ} (hij : i ≤ j) :
    vertexExposureMSpace n i ≤ vertexExposureMSpace n j := by
  apply MeasurableSpace.generateFrom_mono
  intro S ⟨u, hu_lt, w, b, hS⟩
  exact ⟨u, Nat.lt_of_lt_of_le hu_lt hij, w, b, hS⟩

/-- Every generator of `vertexExposureMSpace n i` is measurable in the ambient discrete
    measurable space on `SimpleGraph (Fin n)` (all sets are measurable there). -/
private theorem vertexExposureMSpace_le_top (n i : ℕ) :
    vertexExposureMSpace n i ≤ (inferInstance : MeasurableSpace (SimpleGraph (Fin n))) := by
  apply MeasurableSpace.generateFrom_le
  intro S ⟨u, _, w, b, hS⟩
  -- In the discrete measurable space, every set is measurable (all singletons are measurable)
  rw [hS]
  -- {G | G.Adj u w = b} is a finite set in the finite type SimpleGraph (Fin n)
  have : Set.Finite {G : SimpleGraph (Fin n) | G.Adj u w = b} := Set.toFinite _
  exact this.measurableSet

/-- The vertex-exposure filtration as a `Filtration ℕ _` value on `SimpleGraph (Fin n)`.

    This is the core infrastructure for the Doob martingale argument in `zeta_azuma_tail_bound`.
    The filtration satisfies:
    - `ℱ 0 = ⊥` (no vertices revealed; generated by empty set)
    - `ℱ i ≤ ℱ j` for `i ≤ j` (proved: `vertexExposureFiltration_mono`)
    - `ℱ i ≤ ⊤` (the discrete ambient measurable space; proved: `vertexExposureMSpace_le_top`) -/
def vertexExposureFiltration (n : ℕ) :
    Filtration ℕ (inferInstance : MeasurableSpace (SimpleGraph (Fin n))) where
  seq i := vertexExposureMSpace n i
  mono' {i j} hij := vertexExposureFiltration_mono n hij
  le' i := vertexExposureMSpace_le_top n i

/-- The cochromatic number is **measurable** in the ambient discrete measurable space on
    `SimpleGraph (Fin n)`. This is the prerequisite for forming the conditional expectation
    `E[ζ | ℱ_i]` (the Doob martingale), which requires the function to be integrable w.r.t. `gnHalf n`.

    **Proof**: In the discrete measurable space, every function from a finite type is measurable
    (every preimage is a finite union of singletons). -/
theorem cochromaticNumber_measurable (n : ℕ) :
    Measurable (fun G : SimpleGraph (Fin n) => (cochromaticNumber G : ℝ)) := by
  -- SimpleGraph (Fin n) has the discrete measurable space; every function from it is measurable
  apply Measurable.of_discrete

/-- The Doob martingale `M i G = E[ζ(G) | ℱ_i G]` (conditional expectation of the cochromatic
    number given the first i vertices' adjacencies) is **strongly adapted** to `vertexExposureFiltration n`.

    **Proof**: By `MeasureTheory.stronglyMeasurable_condExp`, any conditional expectation
    `μ[f | m]` is strongly measurable w.r.t. the conditioning σ-algebra `m`. Applying this with
    `m = vertexExposureMSpace n i` gives `StronglyMeasurable[vertexExposureMSpace n i]` for each i. -/
theorem doobMartingale_stronglyAdapted (n : ℕ) :
    StronglyAdapted (vertexExposureFiltration n)
      (fun (i : ℕ) (G : SimpleGraph (Fin n)) =>
        (gnHalf n)[(fun G' => (cochromaticNumber G' : ℝ)) | vertexExposureMSpace n i] G) := by
  intro i
  -- condExp is always strongly measurable w.r.t. the conditioning σ-algebra
  exact stronglyMeasurable_condExp

/-- The vertex-exposure σ-algebra at stage 0 is the trivial (bottom) σ-algebra.
    No generators exist (no u.val < 0), so `generateFrom ∅ = ⊥`. -/
lemma vertexExposureMSpace_zero (n : ℕ) :
    vertexExposureMSpace n 0 = ⊥ := by
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    rintro S ⟨u, hu, _, _, _⟩
    exact absurd hu (Nat.not_lt_zero u.val)
  · exact bot_le

/-- The vertex-exposure σ-algebra at stage `n-1` (for n ≥ 1) equals the full discrete σ-algebra.
    Every singleton `{G}` is generated: `{G} = ⋂_{u,w : Fin n, u.val < n-1} {H | H.Adj u w = G.Adj u w}`.
    By symmetry of SimpleGraph, every edge is covered since for any {a,b} with a ≠ b,
    min(a.val, b.val) < n-1 (both vals are < n, so at least one is ≤ n-2 = (n-1)-1). -/
-- Helper: every singleton in SimpleGraph (Fin n) is measurable in vertexExposureMSpace n (n-1).
private lemma vertexExposureMSpace_pred_singleton_measurable (n : ℕ) (hn : 0 < n)
    (G : SimpleGraph (Fin n)) :
    MeasurableSet[vertexExposureMSpace n (n - 1)] {G} := by
  classical  -- use classical decidability throughout
  -- Helper: for u.val < n-1, the set {H | H.Adj u w ↔ G.Adj u w} is measurable.
  -- This follows from {H | H.Adj u w} and {H | ¬ H.Adj u w} being generators.
  have gen_iff : ∀ (u : Fin n) (_ : u.val < n - 1) (w : Fin n),
      MeasurableSet[vertexExposureMSpace n (n - 1)]
        {H : SimpleGraph (Fin n) | H.Adj u w ↔ G.Adj u w} := by
    intro u hu w
    by_cases hguw : G.Adj u w
    · -- {H | H.Adj u w ↔ True} = {H | H.Adj u w} = {H | H.Adj u w = true}
      -- The generator in vertexExposureMSpace uses Bool: {H | H.Adj u w = b} where b : Bool
      -- Here b = true, so the generator set is {H | H.Adj u w = true}
      convert MeasurableSpace.measurableSet_generateFrom
          (show {H : SimpleGraph (Fin n) | H.Adj u w = true} ∈
            {S | ∃ (v : Fin n) (_ : v.val < n - 1) (w' : Fin n) (b : Bool),
              S = {H : SimpleGraph (Fin n) | H.Adj v w' = b}} from
            ⟨u, hu, w, true, rfl⟩) using 1
      ext H; simp [hguw]
    · convert MeasurableSpace.measurableSet_generateFrom
          (show {H : SimpleGraph (Fin n) | H.Adj u w = false} ∈
            {S | ∃ (v : Fin n) (_ : v.val < n - 1) (w' : Fin n) (b : Bool),
              S = {H : SimpleGraph (Fin n) | H.Adj v w' = b}} from
            ⟨u, hu, w, false, rfl⟩) using 1
      ext H; simp [hguw]
  -- {G} = ⋂ over pairs (u.val < n-1, w) of {H | H.Adj u w ↔ G.Adj u w}
  have h_eq : ({G} : Set (SimpleGraph (Fin n))) =
      ⋂ (uw : {p : Fin n × Fin n | p.1.val < n - 1}),
        {H : SimpleGraph (Fin n) | H.Adj uw.1.1 uw.1.2 ↔ G.Adj uw.1.1 uw.1.2} := by
    ext H
    simp only [Set.mem_singleton_iff, Set.mem_iInter, Subtype.forall, Set.mem_setOf_eq]
    constructor
    · intro heq ⟨u, w⟩ _; rw [heq]
    · intro h
      ext a b
      by_cases ha : a.val < n - 1
      · exact h (a, b) ha
      · by_cases hb : b.val < n - 1
        · rw [SimpleGraph.adj_comm H, SimpleGraph.adj_comm G]; exact h (b, a) hb
        · have hab : a = b := by ext; omega
          simp [hab]
  rw [h_eq]
  apply MeasurableSet.iInter
  rintro ⟨⟨u, w⟩, huw⟩
  exact gen_iff u huw w

lemma vertexExposureMSpace_pred_eq_top (n : ℕ) (hn : 0 < n) :
    vertexExposureMSpace n (n - 1) =
      (inferInstance : MeasurableSpace (SimpleGraph (Fin n))) := by
  apply le_antisymm
  · exact vertexExposureMSpace_le_top n (n - 1)
  · -- Show every set is measurable in vertexExposureMSpace n (n-1).
    -- Suffices to show every singleton {G} is measurable (then any set = ⋃ singletons is measurable).
    intro s _hs
    -- s = ⋃_{G ∈ s} {G} (finite union of singletons, since SimpleGraph (Fin n) is finite)
    have h_eq : s = ⋃ G ∈ s, {G} := (Set.biUnion_of_singleton s).symm
    rw [h_eq]
    apply Set.Finite.measurableSet_biUnion (Set.toFinite s)
    intro G _
    exact vertexExposureMSpace_pred_singleton_measurable n hn G

end VertexExposureFiltration

/-! ## Azuma-Hoeffding Concentration -/

section AzumaConcentration

/-!
### Auxiliary lemmas for `zeta_azuma_tail_bound`

These three lemmas isolate the key proof components for the Azuma tail bound.
All are fully proved (0 sorry). Together they imply `zeta_azuma_tail_bound`.

1. `doobDiff_telescope` — Σ Y_i = ζ − E[ζ] a.e.  (condExp_bot/condExp_of_stronglyMeasurable)
2. `doobDiff_hasCondSubgaussianMGF` — each Y_i has cond subgaussian c = 1
   (Hoeffding's lemma via [-1,1] bound + condExpKernel mean-zero)
3. `doobDiff_Y0_subgaussian` — Y 0 = 0, trivially sub-Gaussian

The outer theorem `zeta_azuma_tail_bound` then follows by applying
`measure_sum_ge_le_of_hasCondSubgaussianMGF` and rewriting the telescope.
-/

-- The Doob difference process Y i G = E[ζ|ℱ_i](G) − E[ζ|ℱ_{i−1}](G)
-- with Y 0 G = 0 (no prior filtration stage).
private noncomputable def doobDiff (n : ℕ) (i : ℕ) (G : SimpleGraph (Fin n)) : ℝ :=
  match i with
  | 0     => 0
  | i + 1 =>
    (gnHalf n)[(fun G' => (cochromaticNumber G' : ℝ)) | vertexExposureMSpace n (i + 1)] G -
    (gnHalf n)[(fun G' => (cochromaticNumber G' : ℝ)) | vertexExposureMSpace n i] G

/-- **[Telescope — PROVED]**
  The Doob differences sum to ζ(G) − E[ζ(G)] almost surely.

  Proof path:
  - `Σ_{i<n} Y_i = E[ζ|ℱ_n] − E[ζ|ℱ_0]`  by telescoping (each Y_{i+1} = E[ζ|ℱ_{i+1}]−E[ζ|ℱ_i])
  - `E[ζ|ℱ_n] = ζ` a.e. because `vertexExposureMSpace n n = ⊤`
    (all u.val < n cover every edge; generators = all singletons)
    → `condExp_of_stronglyMeasurable` with hf : `StronglyMeasurable[⊤] (ζ : ℝ)` applies.
  - `E[ζ|ℱ_0] = E[ζ]` a.e. because `vertexExposureMSpace n 0 = ⊥`
    (no u.val < 0 exists; empty generator → trivial σ-algebra = ⊥)
    → `condExp_bot` applies.

  **Principal blocker**: proving `vertexExposureMSpace n n = ⊤` in Lean.
  Approach: show every singleton `{G}` is generated. `{G} = ⋂_{u,w,b} {H | H.Adj u w = G.Adj u w}`,
  a finite intersection of generators. Uses `Fintype.finite (Fin n × Fin n)`.
-/
private lemma doobDiff_telescope (n : ℕ) (hn : 0 < n) :
    ∀ᵐ G ∂(gnHalf n),
      ∑ i ∈ Finset.range n, doobDiff n i G =
        (cochromaticNumber G : ℝ) -
          ∫ G' : SimpleGraph (Fin n), (cochromaticNumber G' : ℝ) ∂(gnHalf n) := by
  haveI : IsProbabilityMeasure (gnHalf n) := by unfold gnHalf; infer_instance
  -- Denote f i G = E[ζ | ℱ_i] G = (gnHalf n)[(cochromaticNumber ·) | ℱ_i] G
  -- Then doobDiff n 0 G = 0, doobDiff n (i+1) G = f (i+1) G - f i G
  -- So ∑ i ∈ range n, doobDiff n i G = ∑ i ∈ range (n-1), (f (i+1) G - f i G) = f (n-1) G - f 0 G
  -- = ζ(G) - E[ζ] using f(n-1) = ζ a.e. (vertexExposureMSpace n (n-1) = ⊤) and f 0 = E[ζ] (bot).
  set f : ℕ → SimpleGraph (Fin n) → ℝ :=
    fun i G => (gnHalf n)[(fun G' => (cochromaticNumber G' : ℝ)) | vertexExposureMSpace n i] G
  -- The sum over range n equals f(n-1) - f(0) a.e., proved by telescoping.
  -- Step 1: Show sum = f(n-1) - f(0) a.e.
  have h_sum_tel : ∀ᵐ G ∂(gnHalf n),
      ∑ i ∈ Finset.range n, doobDiff n i G = f (n - 1) G - f 0 G := by
    -- Rewrite: ∑ i ∈ range n, doobDiff n i = doobDiff n 0 + ∑ i ∈ range (n-1), doobDiff n (i+1)
    --        = 0 + ∑ i ∈ range (n-1), (f (i+1) - f i)
    --        = f(n-1) - f(0)
    apply Filter.Eventually.of_forall
    intro G
    -- We compute the sum directly using Finset.sum_range_sub.
    -- ∑ i ∈ range n, doobDiff n i G
    -- = ∑ i ∈ range (n-1), doobDiff n (i+1) G  [since doobDiff n 0 G = 0 and reindex]
    -- = ∑ i ∈ range (n-1), (f (i+1) G - f i G) = f (n-1) G - f 0 G
    -- Direct computation: ∑ i ∈ range n, doobDiff n i G = f(n-1) G - f 0 G
    have h_step : ∑ i ∈ Finset.range n, doobDiff n i G = f (n - 1) G - f 0 G := by
      -- Use Finset.sum_range_succ' which gives:
      -- ∑ i ∈ range (m+1), g i = g 0 + ∑ i ∈ range m, g (i+1)
      -- with m = n-1 (so m+1 = n)
      have hn_eq : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn
      -- Apply sum_range_succ' to split off index 0
      have h1 : ∑ i ∈ Finset.range n, doobDiff n i G =
          doobDiff n 0 G + ∑ i ∈ Finset.range (n - 1), doobDiff n (i + 1) G := by
        have hsrs := Finset.sum_range_succ' (f := fun i => doobDiff n i G) (n - 1)
        rw [hn_eq] at hsrs
        linarith [hsrs]
      have h2 : doobDiff n 0 G = 0 := by simp [doobDiff]
      -- doobDiff n (i+1) G = f(i+1) G - f i G by definition
      have h3 : ∀ i, doobDiff n (i + 1) G = f (i + 1) G - f i G := by
        intro i; rfl
      rw [h1, h2, zero_add]
      simp_rw [h3]
      exact Finset.sum_range_sub (fun i => f i G) (n - 1)
    linarith [h_step]
  -- Step 2: f(n-1) = ζ a.e. (since vertexExposureMSpace n (n-1) = ⊤)
  have h_top_eq : vertexExposureMSpace n (n - 1) =
      (inferInstance : MeasurableSpace (SimpleGraph (Fin n))) :=
    vertexExposureMSpace_pred_eq_top n hn
  have h_f_top : ∀ᵐ G ∂(gnHalf n), f (n - 1) G = (cochromaticNumber G : ℝ) := by
    have hf_sm : StronglyMeasurable[vertexExposureMSpace n (n - 1)]
        (fun G : SimpleGraph (Fin n) => (cochromaticNumber G : ℝ)) := by
      rw [h_top_eq]; exact StronglyMeasurable.of_discrete
    have hf_int : Integrable (fun G : SimpleGraph (Fin n) => (cochromaticNumber G : ℝ))
        (gnHalf n) := Integrable.of_finite
    have hm := vertexExposureMSpace_le_top n (n - 1)
    haveI : SigmaFinite ((gnHalf n).trim hm) := inferInstance
    have h_ce : (gnHalf n)[(fun G : SimpleGraph (Fin n) => (cochromaticNumber G : ℝ)) |
        vertexExposureMSpace n (n - 1)] = fun G => (cochromaticNumber G : ℝ) :=
      condExp_of_stronglyMeasurable hm hf_sm hf_int
    exact Filter.Eventually.of_forall (fun G => by simp only [f, h_ce])
  -- Step 3: f(0) = E[ζ] a.e. (since vertexExposureMSpace n 0 = ⊥)
  have h_f_bot : ∀ᵐ G ∂(gnHalf n), f 0 G =
      ∫ G' : SimpleGraph (Fin n), (cochromaticNumber G' : ℝ) ∂(gnHalf n) := by
    have h_bot : vertexExposureMSpace n 0 = ⊥ := vertexExposureMSpace_zero n
    have h_ce : (gnHalf n)[(fun G : SimpleGraph (Fin n) => (cochromaticNumber G : ℝ)) | ⊥] =
        fun _ => ∫ G', (cochromaticNumber G' : ℝ) ∂(gnHalf n) :=
      condExp_bot _
    exact Filter.Eventually.of_forall (fun G => by
      simp only [f]
      rw [show vertexExposureMSpace n 0 = ⊥ from h_bot]
      simp only [h_ce])
  -- Combine
  filter_upwards [h_sum_tel, h_f_top, h_f_bot] with G h_tel h_top' h_bot'
  linarith [h_tel, h_top', h_bot']

/-- **[B1a — Conditional independence: ζ₋ condExp is the same at ℱ_i and ℱ_{i+1}]**
  Let v = ⟨i, _⟩ and ζ₋ G = ζ(G.induce {v}ᶜ). Then E[ζ₋|ℱ_{i+1}] =ᵐ E[ζ₋|ℱ_i].

  **Mathematical content**: In gnHalf n (product Bernoulli(1/2) measure), the edges incident
  to vertex v = ⟨i,_⟩ (those in ℱ_{i+1} \ ℱ_i) are INDEPENDENT of all edges NOT incident to v.
  Since ζ₋ depends only on edges NOT incident to v (it's measurable w.r.t. the σ-algebra of
  non-v-incident edges), ζ₋ is conditionally independent of the extra ℱ_{i+1} information given ℱ_i.
  Therefore E[ζ₋|ℱ_{i+1}] = E[ζ₋|ℱ_i] a.s.

  **Proof route**: Use that gnHalf n = setBernoulli ∘ comap edgeSet (product of Bernoulli per edge).
  The σ-algebras ℱ_i = σ(edges incident to vertices < i) and m_v = σ(edges incident to v)
  are independent sub-σ-algebras of gnHalf n (since their index sets in the product are disjoint
  for the "new" edges in ℱ_{i+1} \ ℱ_i). ζ₋ is measurable w.r.t. the complement m_{-v}.
  Independence of m_{-v} from m_v gives E[ζ₋|ℱ_{i+1}] = E[ζ₋|ℱ_i].

  **Blocker**: Requires connecting gnHalf n product structure to conditional independence
  of σ-subalgebras via iIndepFun / Kernel.iIndepFun in Mathlib.
-/
private lemma zeta_below_condExp_eq (n : ℕ) (i : ℕ) (hi : i < n - 1) :
    let hi_lt : i < n := Nat.lt_of_lt_pred hi
    let v : Fin n := ⟨i, hi_lt⟩
    let zetaBelow := fun G : SimpleGraph (Fin n) =>
      (cochromaticNumber (G.induce ({v}ᶜ : Set (Fin n))) : ℝ)
    (gnHalf n)[zetaBelow | vertexExposureMSpace n (i + 1)] =ᵐ[(gnHalf n)]
      (gnHalf n)[zetaBelow | vertexExposureMSpace n i] := by
  intro hi_lt v zetaBelow
  classical
  haveI hprob : IsProbabilityMeasure (gnHalf n) := by unfold gnHalf; infer_instance
  have hm1 : vertexExposureMSpace n i ≤ (inferInstance : MeasurableSpace (SimpleGraph (Fin n))) :=
    vertexExposureMSpace_le_top n i
  have hm2 : vertexExposureMSpace n (i + 1) ≤ (inferInstance : MeasurableSpace (SimpleGraph (Fin n))) :=
    vertexExposureMSpace_le_top n (i + 1)
  have hm12 : vertexExposureMSpace n i ≤ vertexExposureMSpace n (i + 1) :=
    vertexExposureFiltration_mono n (Nat.le_succ i)
  haveI hsfin1 : SigmaFinite ((gnHalf n).trim hm1) := inferInstance
  haveI hsfin2 : SigmaFinite ((gnHalf n).trim hm2) := inferInstance
  -- All singletons have the same gnHalf n measure (since p = 1/2 = σ p).
  have h_edge_le : ∀ G : SimpleGraph (Fin n),
      G.edgeSet.ncard ≤ (Nat.card (Fin n)).choose 2 := fun G => by
    calc G.edgeSet.ncard
        = G.edgeFinset.card := by rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
      _ ≤ (Fintype.card (Fin n)).choose 2 := SimpleGraph.card_edgeFinset_le_card_choose_two
      _ = (Nat.card (Fin n)).choose 2 := by rw [Nat.card_eq_fintype_card]
  have h_uniform : ∀ G H : SimpleGraph (Fin n), gnHalf n {G} = gnHalf n {H} := by
    intro G H
    simp only [gnHalf, SimpleGraph.binomialRandom_singleton]
    have hσ : unitInterval.toNNReal (unitInterval.symm halfProb) = unitInterval.toNNReal halfProb := by
      congr 1; simp [halfProb, unitInterval.symm, Subtype.ext_iff]; norm_num
    rw [hσ, ← pow_add, ← pow_add,
        Nat.add_sub_cancel' (h_edge_le G), Nat.add_sub_cancel' (h_edge_le H)]
  -- Define flipEdge w: flip edge s(v,w) in G.
  let flipRel : Fin n → SimpleGraph (Fin n) → Fin n → Fin n → Prop :=
    fun w G a b => if s(a, b) = s(v, w) then ¬G.Adj a b else G.Adj a b
  let flipEdge : Fin n → SimpleGraph (Fin n) → SimpleGraph (Fin n) :=
    fun w G => SimpleGraph.fromRel (flipRel w G)
  have h_flip_meas : ∀ w : Fin n, Measurable (flipEdge w) := fun _ => Measurable.of_discrete
  -- flipRel w G is symmetric
  have h_flipRel_symm : ∀ (w : Fin n) (G : SimpleGraph (Fin n)) (a b : Fin n),
      flipRel w G a b = flipRel w G b a := by
    intro w G a b; simp only [flipRel, Sym2.eq_swap, SimpleGraph.adj_comm]
  -- Key adjacency lemma
  have h_flip_adj : ∀ (w : Fin n) (G : SimpleGraph (Fin n)) (a b : Fin n),
      (flipEdge w G).Adj a b ↔ a ≠ b ∧ flipRel w G a b := by
    intro w G a b
    simp only [flipEdge, SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨hab, h | h⟩
      · exact ⟨hab, h⟩
      · exact ⟨hab, h_flipRel_symm w G b a ▸ h⟩
    · rintro ⟨hab, h⟩; exact ⟨hab, Or.inl h⟩
  -- When s(a,b) ≠ s(v,w), flipEdge doesn't change adjacency
  have h_flip_adj_off : ∀ (w : Fin n) (G : SimpleGraph (Fin n)) (a b : Fin n),
      s(a, b) ≠ s(v, w) → ((flipEdge w G).Adj a b ↔ G.Adj a b) := by
    intro w G a b hne
    rw [h_flip_adj]; simp only [flipRel, hne, ite_false]
    exact ⟨And.right, fun h => ⟨G.ne_of_adj h, h⟩⟩
  -- flipEdge w is an involution
  have h_invol : ∀ (w : Fin n) (G : SimpleGraph (Fin n)), flipEdge w (flipEdge w G) = G := by
    intro w G
    ext a b
    rw [h_flip_adj w (flipEdge w G) a b]
    simp only [flipRel]
    split_ifs with heq
    · -- s(a,b) = s(v,w): adjacency is double-flipped
      constructor
      · rintro ⟨hab, h⟩
        rw [h_flip_adj w G a b] at h
        simp only [flipRel, heq, ite_true] at h
        push_neg at h; exact h hab
      · intro hG
        refine ⟨G.ne_of_adj hG, ?_⟩
        -- Goal: ¬(flipEdge w G).Adj a b
        intro h_adj
        rw [h_flip_adj w G a b] at h_adj
        have hfl : flipRel w G a b := h_adj.2
        change (if s(a, b) = s(v, w) then ¬G.Adj a b else G.Adj a b) at hfl
        rw [if_pos heq] at hfl
        exact hfl hG
    · -- s(a,b) ≠ s(v,w): adjacency is unchanged
      exact ⟨fun ⟨_, h⟩ => (h_flip_adj_off w G a b heq).mp h,
             fun hG => ⟨G.ne_of_adj hG, (h_flip_adj_off w G a b heq).mpr hG⟩⟩
  -- flipEdge w preserves gnHalf n
  have h_map_flip : ∀ w : Fin n, (gnHalf n).map (flipEdge w) = gnHalf n := by
    intro w
    apply Measure.ext_of_singleton
    intro G
    rw [Measure.map_apply (h_flip_meas w) (measurableSet_singleton G)]
    have hpreimage : flipEdge w ⁻¹' {G} = {flipEdge w G} := by
      ext H; simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h => by have := congr_arg (flipEdge w) h; rwa [h_invol w H] at this,
             fun h => by rw [h, h_invol w G]⟩
    rw [hpreimage]; exact h_uniform (flipEdge w G) G
  -- zetaBelow is invariant under flipEdge w
  have h_zeta_inv : ∀ (w : Fin n) (G : SimpleGraph (Fin n)),
      zetaBelow (flipEdge w G) = zetaBelow G := by
    intro w G
    show (cochromaticNumber ((flipEdge w G).induce ({v}ᶜ : Set (Fin n))) : ℝ) =
         (cochromaticNumber (G.induce ({v}ᶜ : Set (Fin n))) : ℝ)
    have hgraph : (flipEdge w G).induce ({v}ᶜ : Set (Fin n)) = G.induce ({v}ᶜ : Set (Fin n)) := by
      ext ⟨a, ha⟩ ⟨b, hb⟩
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ha hb
      simp only [SimpleGraph.induce_adj]
      apply h_flip_adj_off
      intro heq
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨rfl, _⟩ | ⟨_, rfl⟩
      · exact ha rfl
      · exact hb rfl
    exact_mod_cast congr_arg cochromaticNumber hgraph
  -- ℱ_i-sets are invariant under preimage of flipEdge w when i < w.val
  have h_fi_inv : ∀ (w : Fin n) (_ : i < w.val)
      (S : Set (SimpleGraph (Fin n))) (_ : MeasurableSet[vertexExposureMSpace n i] S),
      flipEdge w ⁻¹' S = S := by
    intro w hw_gt S hS
    have heq_ms : vertexExposureMSpace n i = MeasurableSpace.generateFrom
        {T : Set (SimpleGraph (Fin n)) | ∃ (u : Fin n) (_ : u.val < i)
          (w' : Fin n) (b : Bool), T = {G : SimpleGraph (Fin n) | G.Adj u w' = b}} := rfl
    rw [heq_ms] at hS
    apply MeasurableSpace.generateFrom_induction _
        (fun s _ => flipEdge w ⁻¹' s = s)
      (fun T hT_mem _ => by
        obtain ⟨u, hu, w', b, rfl⟩ := hT_mem
        ext G
        simp only [Set.mem_preimage, Set.mem_setOf_eq]
        have hne_uw : s(u, w') ≠ s(v, w) := by
          intro heq'
          rw [Sym2.eq_iff] at heq'
          rcases heq' with ⟨huv, _⟩ | ⟨huw, _⟩
          · have : u.val = i := congrArg Fin.val huv; omega
          · have : u.val = w.val := congrArg Fin.val huw; omega
        rw [propext (h_flip_adj_off w G u w' hne_uw)])
      (by simp)
      (fun t _ ht_inv => by rw [Set.preimage_compl, ht_inv])
      (fun s' _ hs'_inv => by rw [Set.preimage_iUnion]; congr 1; funext k; exact hs'_inv k)
      S hS
  -- Main proof: E[zetaBelow|ℱ_{i+1}] =ᵐ E[zetaBelow|ℱ_i]
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm2 Integrable.of_finite
  · intro S _ _; exact integrable_condExp.integrableOn
  · intro S hS _
    -- Define the pi-system of cylinder sets generating ℱ_{i+1}
    -- cylinders = { A ∩ ⋂_{w ∈ W} {G | G.Adj v w = b w} | A ∈ ℱ_i, W ⊆ {w | w.val > i} finite, b : Fin n → Bool }
    let cylinders : Set (Set (SimpleGraph (Fin n))) :=
      {T | ∃ (A : Set (SimpleGraph (Fin n))) (_ : MeasurableSet[vertexExposureMSpace n i] A)
               (W : Finset (Fin n)) (_ : ∀ w ∈ W, i < w.val)
               (b : Fin n → Bool),
             T = A ∩ ⋂ w ∈ W, {G : SimpleGraph (Fin n) | G.Adj v w = b w}}
    -- The property we want to prove on each set
    let P : Set (SimpleGraph (Fin n)) → Prop :=
      fun S => ∫ G in S, (gnHalf n)[zetaBelow | vertexExposureMSpace n i] G ∂gnHalf n =
               ∫ G in S, zetaBelow G ∂gnHalf n
    -- ℱ_{i+1} = generateFrom cylinders
    have h_eq_pi : vertexExposureMSpace n (i + 1) = MeasurableSpace.generateFrom cylinders := by
      apply le_antisymm
      · -- ℱ_{i+1} ≤ generateFrom π: each ℱ_{i+1}-generator is in π
        apply MeasurableSpace.generateFrom_le
        intro T hT_mem
        obtain ⟨u, hu, w, b, rfl⟩ := hT_mem
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hu) with hu_old | hu_eq
        · -- Old generator {G | G.Adj u w = b} ∈ ℱ_i, so it's A ∩ ⋂_{W=∅} ... with A = it
          apply MeasurableSpace.measurableSet_generateFrom
          exact ⟨{G | G.Adj u w = b},
                 MeasurableSpace.measurableSet_generateFrom ⟨u, hu_old, w, b, rfl⟩,
                 ∅, by simp, fun _ => b,
                 by simp⟩
        · -- New generator: u = v
          have huv : u = v := Fin.ext hu_eq
          subst huv
          rcases Nat.lt_trichotomy w.val i with hw_lt | hw_eq | hw_gt
          · -- w.val < i: {G | G.Adj v w = b} ∈ ℱ_i (adj comm)
            apply MeasurableSpace.measurableSet_generateFrom
            refine ⟨{G : SimpleGraph (Fin n) | G.Adj v w = b}, ?_, ∅, by simp, fun _ => b, by simp⟩
            convert MeasurableSpace.measurableSet_generateFrom
                (show {G : SimpleGraph (Fin n) | G.Adj w v = b} ∈
                  {S | ∃ (u : Fin n) (_ : u.val < i) (w' : Fin n) (b : Bool),
                    S = {G : SimpleGraph (Fin n) | G.Adj u w' = b}} from
                  ⟨w, hw_lt, v, b, rfl⟩) using 1
            ext G; simp [SimpleGraph.adj_comm]
          · -- w.val = i: w = v, set is univ or ∅, both in ℱ_i
            have hwv : w = v := Fin.ext (by omega)
            subst hwv
            apply MeasurableSpace.measurableSet_generateFrom
            cases b with
            | false =>
              refine ⟨Set.univ, MeasurableSet.univ, ∅, by simp, fun _ => false, ?_⟩
              ext G; simp [SimpleGraph.irrefl]
            | true =>
              have hempty : MeasurableSet[vertexExposureMSpace n i] (∅ : Set (SimpleGraph (Fin n))) :=
                @MeasurableSet.empty _ (vertexExposureMSpace n i)
              refine ⟨∅, hempty, ∅, by simp, fun _ => true, ?_⟩
              ext G; simp [SimpleGraph.irrefl]
          · -- w.val > i: new edge, use {v} ∩ ⋂_{W={w}} {G.Adj v w = b}
            apply MeasurableSpace.measurableSet_generateFrom
            refine ⟨Set.univ, MeasurableSet.univ, {w}, by simp [hw_gt],
                   fun w' => if w' = w then b else false, ?_⟩
            simp only [Finset.set_biInter_singleton, Set.univ_inter]
            ext G; simp only [Set.mem_setOf_eq, ite_true]
      · -- generateFrom π ≤ ℱ_{i+1}: each cylinder set is ℱ_{i+1}-measurable
        apply MeasurableSpace.generateFrom_le
        rintro T ⟨A, hA, W, hW, b, rfl⟩
        apply MeasurableSet.inter
        · exact hm12 _ hA
        · apply MeasurableSet.biInter (Finset.countable_toSet W)
          intro w hw
          exact MeasurableSpace.measurableSet_generateFrom (show _ ∈ _ from ⟨v, Nat.lt_succ_self i, w, b w, rfl⟩)
    -- cylinders is a π-system
    have h_inter_pi : IsPiSystem cylinders := by
      rintro S1 ⟨A1, hA1, W1, hW1, b1, rfl⟩ S2 ⟨A2, hA2, W2, hW2, b2, rfl⟩ hne
      -- From hne, b1 and b2 are consistent on W1 ∩ W2
      have hconsist : ∀ w ∈ W1 ∩ W2, b1 w = b2 w := by
        intro w hw
        obtain ⟨G, hG⟩ := hne
        simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq] at hG
        have h1 := hG.1.2 w (Finset.mem_inter.mp hw).1
        have h2 := hG.2.2 w (Finset.mem_inter.mp hw).2
        cases hb1 : b1 w <;> cases hb2 : b2 w <;> simp_all
      -- Build merged b
      let b : Fin n → Bool := fun w => if w ∈ W1 then b1 w else b2 w
      refine ⟨A1 ∩ A2, hA1.inter hA2, W1 ∪ W2,
             fun w hw => by simp only [Finset.mem_union] at hw; exact hw.elim (hW1 w) (hW2 w),
             b, ?_⟩
      ext G
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, b]
      constructor
      · intro ⟨⟨hA1G, h1⟩, hA2G, h2⟩
        refine ⟨⟨hA1G, hA2G⟩, fun w hw => ?_⟩
        simp only [Finset.mem_union] at hw
        rcases hw with hwW1 | hwW2
        · simp only [hwW1, ite_true]; exact h1 w hwW1
        · by_cases hwW1' : w ∈ W1
          · simp only [hwW1', ite_true]
            rw [hconsist w (Finset.mem_inter.mpr ⟨hwW1', hwW2⟩)]
            exact h2 w hwW2
          · simp only [hwW1', ite_false]; exact h2 w hwW2
      · intro ⟨⟨hA1G, hA2G⟩, h⟩
        refine ⟨⟨hA1G, fun w hw => ?_⟩, hA2G, fun w hw => ?_⟩
        · have := h w (Finset.mem_union_left W2 hw)
          simp only [hw, ite_true] at this; exact this
        · have := h w (Finset.mem_union_right W1 hw)
          by_cases hwW1' : w ∈ W1
          · simp only [hwW1', ite_true] at this
            rw [hconsist w (Finset.mem_inter.mpr ⟨hwW1', hw⟩)] at this
            exact this
          · simp only [hwW1', ite_false] at this; exact this
    -- P holds for all cylinder sets (by induction on W)
    have h_pi_eq : ∀ T ∈ cylinders, P T := by
      rintro T ⟨A, hA, W, hW, b, rfl⟩
      -- Induction on W
      induction W using Finset.induction_on with
      | empty =>
        have hsimp : A ∩ ⋂ w ∈ (∅ : Finset (Fin n)), {G : SimpleGraph (Fin n) | G.Adj v w = b w} = A := by
          simp
        rw [hsimp]
        exact setIntegral_condExp hm1 Integrable.of_finite hA
      | insert w0 W' hw_notin ih =>
        -- The induction hypothesis for W' (need hW for W')
        have hW' : ∀ w ∈ W', i < w.val := fun w hw => hW w (Finset.mem_insert_of_mem hw)
        have hw0_gt : i < w0.val := hW w0 (Finset.mem_insert_self w0 W')
        -- Let T' = A ∩ ⋂_{w ∈ W'} {G.Adj v w = b w}
        let T' := A ∩ ⋂ w ∈ W', {G : SimpleGraph (Fin n) | G.Adj v w = b w}
        -- Let T+ = T' ∩ {G | G.Adj v w0}, T- = T' ∩ {G | ¬G.Adj v w0}
        let T_plus := T' ∩ {G : SimpleGraph (Fin n) | G.Adj v w0}
        let T_minus := T' ∩ {G : SimpleGraph (Fin n) | ¬G.Adj v w0}
        -- The inserted set is T' ∩ {G.Adj v w0 = b w0}
        -- If b w0 = true, this is T_plus; if b w0 = false, this is T_minus
        -- In both cases, use flip symmetry to conclude P holds
        -- A ∩ ⋂ w ∈ insert w0 W', ... = T' ∩ {G | G.Adj v w0 = b w0}
        have hT'_inter : A ∩ ⋂ w ∈ insert w0 W', {G : SimpleGraph (Fin n) | G.Adj v w = b w} =
            T' ∩ {G : SimpleGraph (Fin n) | G.Adj v w0 = b w0} := by
          rw [Finset.set_biInter_insert]
          simp only [T']
          ext G; simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
          tauto
        -- {G | G.Adj v w0 = b w0} = if b w0 = true then {G | G.Adj v w0} else {G | ¬G.Adj v w0}
        have hT_eq : A ∩ ⋂ w ∈ insert w0 W', {G : SimpleGraph (Fin n) | G.Adj v w = b w} =
            if b w0 = true then T_plus else T_minus := by
          rw [hT'_inter]
          cases hb0 : b w0 with
          | true =>
            simp only [hb0, ite_true, T_plus]
            congr 1
            ext G; simp [hb0]
          | false =>
            simp only [hb0, ite_false, T_minus]
            congr 1
            ext G; simp [hb0]
        -- IH gives P(T')
        have ihT' : P T' := ih hW'
        -- T' = T_plus ⊔ T_minus (disjoint)
        have hT'_eq : T' = T_plus ∪ T_minus := by
          ext G
          simp only [T_plus, T_minus, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
          constructor
          · intro h
            by_cases hadj : G.Adj v w0
            · exact Or.inl ⟨h, hadj⟩
            · exact Or.inr ⟨h, hadj⟩
          · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
        have hT'_disj : Disjoint T_plus T_minus := by
          simp only [Set.disjoint_left, T_plus, T_minus, Set.mem_inter_iff, Set.mem_setOf_eq]
          exact fun G ⟨_, h1⟩ ⟨_, h2⟩ => h2 h1
        -- Measurability
        have hadj_ms : MeasurableSet {G : SimpleGraph (Fin n) | G.Adj v w0} := by
          have : MeasurableSet {G : SimpleGraph (Fin n) | G.Adj v w0 = true} :=
            hm2 _ (MeasurableSpace.measurableSet_generateFrom ⟨v, Nat.lt_succ_self i, w0, true, rfl⟩)
          convert this using 1; ext G; simp
        have hT'_ms : MeasurableSet T' := by
          apply hm2
          exact (hm12 _ hA).inter (MeasurableSet.biInter (Finset.countable_toSet W')
            (fun w _ => MeasurableSpace.measurableSet_generateFrom ⟨v, Nat.lt_succ_self i, w, b w, rfl⟩))
        have hTplus_ms : MeasurableSet T_plus := hT'_ms.inter hadj_ms
        have hTminus_ms : MeasurableSet T_minus := hT'_ms.inter hadj_ms.compl
        -- Use flipEdge w0 symmetry to show ∫_{T+} E = ∫_{T-} E and ∫_{T+} zB = ∫_{T-} zB
        have hvw0 : v ≠ w0 := fun h => absurd hw0_gt (h ▸ Nat.lt_irrefl i)
        have h_preimage_adj : flipEdge w0 ⁻¹' {G : SimpleGraph (Fin n) | G.Adj v w0} =
            {G : SimpleGraph (Fin n) | ¬G.Adj v w0} := by
          ext G
          simp only [Set.mem_preimage, Set.mem_setOf_eq]
          rw [h_flip_adj]
          simp only [flipRel, ite_true]
          constructor
          · rintro ⟨_, hf⟩; exact hf
          · intro h; exact ⟨hvw0, h⟩
        -- flipEdge w0 maps T_plus to T_minus
        -- flipEdge w0 ⁻¹' T' = T' (flipEdge preserves sets not involving edge v-w0)
        have h_flip_T' : flipEdge w0 ⁻¹' T' = T' := by
          have hT'_fi_plus : MeasurableSet[vertexExposureMSpace n (i + 1)] T' :=
            (hm12 _ hA).inter (MeasurableSet.biInter (Finset.countable_toSet W')
              fun w _ => MeasurableSpace.measurableSet_generateFrom ⟨v, Nat.lt_succ_self i, w, b w, rfl⟩)
          -- T' is measurable w.r.t. ℱ_i (since A ∈ ℱ_i and each {G.Adj v w = b w} for w ∈ W' with w.val > i is new)
          -- Actually T' may NOT be ℱ_i-measurable; we need to use ext manually
          ext G
          simp only [T', Set.mem_preimage, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
          have hne_sym : ∀ w ∈ W', s(v, w) ≠ s(v, w0) := by
            intro w hw heq
            rw [Sym2.eq_iff] at heq
            rcases heq with ⟨-, hweq⟩ | ⟨hvw0_eq, -⟩
            · exact hw_notin (hweq ▸ hw)
            · exact hvw0 hvw0_eq
          constructor
          · rintro ⟨hAG, hW'G⟩
            constructor
            · have : G ∈ flipEdge w0 ⁻¹' A := hAG
              rwa [h_fi_inv w0 hw0_gt A hA] at this
            · intro w hw
              simp only [← h_flip_adj_off w0 G v w (hne_sym w hw)]
              exact hW'G w hw
          · rintro ⟨hAG, hW'G⟩
            constructor
            · have : G ∈ flipEdge w0 ⁻¹' A := by
                rwa [h_fi_inv w0 hw0_gt A hA]
              exact this
            · intro w hw
              simp only [h_flip_adj_off w0 G v w (hne_sym w hw)]
              exact hW'G w hw
        have h_flip_Tplus : flipEdge w0 ⁻¹' T_plus = T_minus := by
          simp only [T_plus, T_minus, Set.preimage_inter]
          rw [h_flip_T', h_preimage_adj]
        -- ∫_{T+} zetaBelow = ∫_{T-} zetaBelow by flip
        have h_zeta_sym :
            ∫ G in T_plus, zetaBelow G ∂gnHalf n =
            ∫ G in T_minus, zetaBelow G ∂gnHalf n := by
          conv_lhs =>
            rw [← h_map_flip w0,
                setIntegral_map hTplus_ms AEStronglyMeasurable.of_discrete
                  (h_flip_meas w0).aemeasurable,
                h_flip_Tplus]
          congr 1; ext G; exact h_zeta_inv w0 G
        -- ∫_{T+} E[zB|ℱ_i] = ∫_{T-} E[zB|ℱ_i] by flip
        have h_ce_ptwise_w0 : ∀ G : SimpleGraph (Fin n),
            (gnHalf n)[zetaBelow | vertexExposureMSpace n i] (flipEdge w0 G) =
            (gnHalf n)[zetaBelow | vertexExposureMSpace n i] G := fun G => by
          set g := (gnHalf n)[zetaBelow | vertexExposureMSpace n i]
          have hg_meas : Measurable[vertexExposureMSpace n i] g :=
            stronglyMeasurable_condExp.measurable
          have hS_g := hg_meas (measurableSet_singleton (g G))
          have hmem : flipEdge w0 G ∈ g ⁻¹' {g G} := by
            have : flipEdge w0 G ∈ flipEdge w0 ⁻¹' (g ⁻¹' {g G}) := by
              simp only [Set.mem_preimage, Set.mem_singleton_iff, h_invol]
            rwa [h_fi_inv w0 hw0_gt _ hS_g] at this
          exact Set.mem_singleton_iff.mp (Set.mem_preimage.mp hmem)
        have h_ce_sym :
            ∫ G in T_plus, (gnHalf n)[zetaBelow | vertexExposureMSpace n i] G ∂gnHalf n =
            ∫ G in T_minus, (gnHalf n)[zetaBelow | vertexExposureMSpace n i] G ∂gnHalf n :=
          calc ∫ G in T_plus, (gnHalf n)[zetaBelow | vertexExposureMSpace n i] G ∂gnHalf n
              = ∫ G in T_plus, (gnHalf n)[zetaBelow | vertexExposureMSpace n i] G ∂(gnHalf n).map (flipEdge w0) :=
                  by rw [h_map_flip]
            _ = ∫ G in flipEdge w0 ⁻¹' T_plus,
                    (gnHalf n)[zetaBelow | vertexExposureMSpace n i] (flipEdge w0 G) ∂gnHalf n :=
                setIntegral_map hTplus_ms AEStronglyMeasurable.of_discrete (h_flip_meas w0).aemeasurable
            _ = ∫ G in T_minus,
                    (gnHalf n)[zetaBelow | vertexExposureMSpace n i] (flipEdge w0 G) ∂gnHalf n := by
                rw [h_flip_Tplus]
            _ = ∫ G in T_minus, (gnHalf n)[zetaBelow | vertexExposureMSpace n i] G ∂gnHalf n :=
                setIntegral_congr_fun hTminus_ms (fun G _ => h_ce_ptwise_w0 G)
        -- T' = T_plus ∪ T_minus, so ∫_{T'} = ∫_{T+} + ∫_{T-}
        have h_split_ce : ∫ G in T', (gnHalf n)[zetaBelow | vertexExposureMSpace n i] G ∂gnHalf n =
            ∫ G in T_plus, (gnHalf n)[zetaBelow | vertexExposureMSpace n i] G ∂gnHalf n +
            ∫ G in T_minus, (gnHalf n)[zetaBelow | vertexExposureMSpace n i] G ∂gnHalf n := by
          rw [hT'_eq]
          exact setIntegral_union hT'_disj hTminus_ms
            integrable_condExp.integrableOn integrable_condExp.integrableOn
        have h_split_zeta : ∫ G in T', zetaBelow G ∂gnHalf n =
            ∫ G in T_plus, zetaBelow G ∂gnHalf n +
            ∫ G in T_minus, zetaBelow G ∂gnHalf n := by
          rw [hT'_eq]
          exact setIntegral_union hT'_disj hTminus_ms
            Integrable.of_finite.integrableOn Integrable.of_finite.integrableOn
        -- Conclude P(T_plus) and P(T_minus) from P(T'), h_ce_sym, h_zeta_sym
        have hP_plus : P T_plus := by linarith [ihT', h_split_ce, h_split_zeta, h_ce_sym, h_zeta_sym]
        have hP_minus : P T_minus := by linarith [ihT', h_split_ce, h_split_zeta, h_ce_sym, h_zeta_sym]
        rw [hT_eq]; cases b w0 <;> simp_all
    -- Now apply induction_on_inter (Dynkin's π-λ theorem)
    -- h_eq_pi : vertexExposureMSpace n (i+1) = generateFrom cylinders
    -- induction_on_inter needs h_eq : m = generateFrom s, where m is inferred from hS
    have hind := MeasurableSpace.induction_on_inter (C := fun S _ => P S)
      (h_eq := h_eq_pi) (h_inter := h_inter_pi)
      (empty := by simp [P])
      (basic := h_pi_eq)
      (compl := fun t htm ht_eq => by
        have hms : MeasurableSet t := hm2 t htm
        simp only [P] at ht_eq ⊢
        rw [setIntegral_compl hms integrable_condExp,
            setIntegral_compl hms Integrable.of_finite,
            integral_condExp hm1, ht_eq])
      (iUnion := fun f hf_disj hf_meas hf_eq => by
        simp only [P] at hf_eq ⊢
        have hf_ms : ∀ k, MeasurableSet (f k) := fun k => hm2 _ (hf_meas k)
        rw [integral_iUnion hf_ms hf_disj integrable_condExp.integrableOn,
            integral_iUnion hf_ms hf_disj Integrable.of_finite.integrableOn]
        congr 1; ext k; exact hf_eq k)
    exact hind S hS
  · exact (stronglyMeasurable_condExp.mono hm12).aestronglyMeasurable

/-- **[B1 — Doob differences are a.s. in [-1, 1] — PROVED]**
  For all n, i with i < n - 1, the Doob difference `doobDiff n (i+1)` lies in [-1, 1]
  μ-almost surely.

  **Proof** (using `zeta_below_condExp_eq`):
  Let v = ⟨i, _⟩, ζ₋ G = ζ(G.induce {v}ᶜ).
  By `cochromaticNumber_bounded_diff_singleton v`: ζ₋ ≤ ζ ≤ ζ₋ + 1 pointwise.
  By `condExp_mono`:
    E[ζ₋|ℱ_{i+1}] ≤ E[ζ|ℱ_{i+1}] ≤ E[ζ₋|ℱ_{i+1}] + 1
    E[ζ₋|ℱ_i] ≤ E[ζ|ℱ_i] ≤ E[ζ₋|ℱ_i] + 1
  By `zeta_below_condExp_eq`: E[ζ₋|ℱ_{i+1}] =ᵐ E[ζ₋|ℱ_i].
  Combining: doobDiff = E[ζ|ℱ_{i+1}] - E[ζ|ℱ_i]
    ≤ (E[ζ₋|ℱ_{i+1}] + 1) - E[ζ₋|ℱ_i] =ᵐ 1
    ≥ E[ζ₋|ℱ_{i+1}] - (E[ζ₋|ℱ_i] + 1) =ᵐ -1.
-/
private lemma doobDiff_mem_Icc (n : ℕ) (i : ℕ) (hi : i < n - 1) :
    ∀ᵐ G ∂(gnHalf n), doobDiff n (i + 1) G ∈ Set.Icc (-1 : ℝ) 1 := by
  haveI hprob : IsProbabilityMeasure (gnHalf n) := by unfold gnHalf; infer_instance
  have hm1 : vertexExposureMSpace n i ≤
      (inferInstance : MeasurableSpace (SimpleGraph (Fin n))) := vertexExposureMSpace_le_top n i
  have hm2 : vertexExposureMSpace n (i + 1) ≤
      (inferInstance : MeasurableSpace (SimpleGraph (Fin n))) := vertexExposureMSpace_le_top n (i + 1)
  haveI hsfin1 : SigmaFinite ((gnHalf n).trim hm1) := inferInstance
  haveI hsfin2 : SigmaFinite ((gnHalf n).trim hm2) := inferInstance
  -- Set up vertex v and the functions zeta, zetaBelow
  have hi_lt : i < n := Nat.lt_of_lt_pred hi
  let v : Fin n := ⟨i, hi_lt⟩
  let zeta := fun G : SimpleGraph (Fin n) => (cochromaticNumber G : ℝ)
  let zetaBelow := fun G : SimpleGraph (Fin n) =>
    (cochromaticNumber (G.induce ({v}ᶜ : Set (Fin n))) : ℝ)
  -- Pointwise bounds from cochromaticNumber_bounded_diff_singleton
  have h_lb : ∀ G, zetaBelow G ≤ zeta G := fun G =>
    Nat.cast_le.mpr (cochromaticNumber_bounded_diff_singleton G v).1
  have h_ub : ∀ G, zeta G ≤ zetaBelow G + 1 := fun G => by
    show (cochromaticNumber G : ℝ) ≤ (cochromaticNumber (G.induce ({v}ᶜ : Set (Fin n))) : ℝ) + 1
    have hbd := (cochromaticNumber_bounded_diff_singleton G v).2
    exact_mod_cast hbd
  haveI hfin : IsFiniteMeasure (gnHalf n) := inferInstance
  -- condExp_mono: E[zetaBelow|ℱ_k] ≤ E[zeta|ℱ_k] ≤ E[zetaBelow|ℱ_k] + 1
  have h_lb_i1 : (gnHalf n)[zetaBelow | vertexExposureMSpace n (i + 1)] ≤ᵐ[(gnHalf n)]
      (gnHalf n)[zeta | vertexExposureMSpace n (i + 1)] :=
    condExp_mono (μ := gnHalf n) (m := vertexExposureMSpace n (i + 1))
      Integrable.of_finite Integrable.of_finite (Filter.Eventually.of_forall h_lb)
  have h_ub_i1 : (gnHalf n)[zeta | vertexExposureMSpace n (i + 1)] ≤ᵐ[(gnHalf n)]
      (gnHalf n)[zetaBelow + 1 | vertexExposureMSpace n (i + 1)] :=
    condExp_mono (μ := gnHalf n) (m := vertexExposureMSpace n (i + 1))
      Integrable.of_finite Integrable.of_finite (Filter.Eventually.of_forall h_ub)
  have h_lb_i : (gnHalf n)[zetaBelow | vertexExposureMSpace n i] ≤ᵐ[(gnHalf n)]
      (gnHalf n)[zeta | vertexExposureMSpace n i] :=
    condExp_mono (μ := gnHalf n) (m := vertexExposureMSpace n i)
      Integrable.of_finite Integrable.of_finite (Filter.Eventually.of_forall h_lb)
  have h_ub_i : (gnHalf n)[zeta | vertexExposureMSpace n i] ≤ᵐ[(gnHalf n)]
      (gnHalf n)[zetaBelow + 1 | vertexExposureMSpace n i] :=
    condExp_mono (μ := gnHalf n) (m := vertexExposureMSpace n i)
      Integrable.of_finite Integrable.of_finite (Filter.Eventually.of_forall h_ub)
  -- condExp_add: E[zetaBelow + 1|ℱ_k] =ᵐ E[zetaBelow|ℱ_k] + 1
  have h_add_i1 : (gnHalf n)[zetaBelow + 1 | vertexExposureMSpace n (i + 1)] =ᵐ[(gnHalf n)]
      (gnHalf n)[zetaBelow | vertexExposureMSpace n (i + 1)] + 1 := by
    have h1 : (gnHalf n)[zetaBelow + 1 | vertexExposureMSpace n (i + 1)] =ᵐ[(gnHalf n)]
        (gnHalf n)[zetaBelow | vertexExposureMSpace n (i + 1)] +
        (gnHalf n)[fun (_ : SimpleGraph (Fin n)) => (1 : ℝ) | vertexExposureMSpace n (i + 1)] :=
      condExp_add (μ := gnHalf n) (m := vertexExposureMSpace n (i + 1))
        Integrable.of_finite Integrable.of_finite
    rw [condExp_const (hm := hm2) (1 : ℝ)] at h1
    filter_upwards [h1] with G hG
    simp only [Pi.add_apply, Pi.one_apply] at hG ⊢; linarith
  have h_add_i : (gnHalf n)[zetaBelow + 1 | vertexExposureMSpace n i] =ᵐ[(gnHalf n)]
      (gnHalf n)[zetaBelow | vertexExposureMSpace n i] + 1 := by
    have h1 : (gnHalf n)[zetaBelow + 1 | vertexExposureMSpace n i] =ᵐ[(gnHalf n)]
        (gnHalf n)[zetaBelow | vertexExposureMSpace n i] +
        (gnHalf n)[fun (_ : SimpleGraph (Fin n)) => (1 : ℝ) | vertexExposureMSpace n i] :=
      condExp_add (μ := gnHalf n) (m := vertexExposureMSpace n i)
        Integrable.of_finite Integrable.of_finite
    rw [condExp_const (hm := hm1) (1 : ℝ)] at h1
    filter_upwards [h1] with G hG
    simp only [Pi.add_apply, Pi.one_apply] at hG ⊢; linarith
  -- Conditional independence: E[zetaBelow|ℱ_{i+1}] =ᵐ E[zetaBelow|ℱ_i]
  -- (proved in zeta_below_condExp_eq using the product structure of gnHalf n)
  -- We need to align the zetaBelow definition with the one in zeta_below_condExp_eq
  have h_ci : (gnHalf n)[zetaBelow | vertexExposureMSpace n (i + 1)] =ᵐ[(gnHalf n)]
      (gnHalf n)[zetaBelow | vertexExposureMSpace n i] :=
    zeta_below_condExp_eq n i hi
  -- doobDiff n (i+1) G = E[zeta|ℱ_{i+1}](G) - E[zeta|ℱ_i](G)
  -- Upper bound: ≤ (E[zetaBelow|ℱ_{i+1}] + 1) - E[zetaBelow|ℱ_i] =ᵐ 1
  -- Lower bound: ≥ E[zetaBelow|ℱ_{i+1}] - (E[zetaBelow|ℱ_i] + 1) =ᵐ -1
  filter_upwards [h_lb_i1, h_ub_i1, h_lb_i, h_ub_i, h_add_i1, h_add_i, h_ci] with G
      h_lb_i1' h_ub_i1' h_lb_i' h_ub_i' h_add_i1' h_add_i' h_ci'
  simp only [doobDiff, Set.mem_Icc]
  -- Let a₁ = E[zeta|ℱ_{i+1}](G), a₂ = E[zeta|ℱ_i](G), b = E[zetaBelow|ℱ_i](G)
  -- h_ci': E[zetaBelow|ℱ_{i+1}](G) = b
  -- h_lb_i1': b ≤ a₁; h_ub_i1': a₁ ≤ E[zetaBelow+1|ℱ_{i+1}](G) = b + 1
  -- h_lb_i': b ≤ a₂; h_ub_i': a₂ ≤ E[zetaBelow+1|ℱ_i](G) = b + 1
  have h_add_i1_val : (gnHalf n)[zetaBelow + 1 | vertexExposureMSpace n (i + 1)] G =
      (gnHalf n)[zetaBelow | vertexExposureMSpace n (i + 1)] G + 1 := by
    have := h_add_i1'; simp only [Pi.add_apply, Pi.one_apply] at this; linarith
  have h_add_i_val : (gnHalf n)[zetaBelow + 1 | vertexExposureMSpace n i] G =
      (gnHalf n)[zetaBelow | vertexExposureMSpace n i] G + 1 := by
    have := h_add_i'; simp only [Pi.add_apply, Pi.one_apply] at this; linarith
  -- The doobDiff uses `zeta` = `fun G' => ↑(cochromaticNumber G')` but Lean sees them as different
  -- due to the let binding. Use `show` to convert.
  constructor
  · -- -1 ≤ doobDiff
    show -1 ≤ (gnHalf n)[fun G' : SimpleGraph (Fin n) => (cochromaticNumber G' : ℝ) |
        vertexExposureMSpace n (i + 1)] G -
      (gnHalf n)[fun G' : SimpleGraph (Fin n) => (cochromaticNumber G' : ℝ) |
        vertexExposureMSpace n i] G
    -- Note: zeta = fun G => ↑(cochromaticNumber G), so these are the same
    change -1 ≤ (gnHalf n)[zeta | vertexExposureMSpace n (i + 1)] G -
        (gnHalf n)[zeta | vertexExposureMSpace n i] G
    linarith [h_lb_i1', h_ub_i', h_add_i_val, h_ci']
  · -- doobDiff ≤ 1
    show (gnHalf n)[fun G' : SimpleGraph (Fin n) => (cochromaticNumber G' : ℝ) |
        vertexExposureMSpace n (i + 1)] G -
      (gnHalf n)[fun G' : SimpleGraph (Fin n) => (cochromaticNumber G' : ℝ) |
        vertexExposureMSpace n i] G ≤ 1
    change (gnHalf n)[zeta | vertexExposureMSpace n (i + 1)] G -
        (gnHalf n)[zeta | vertexExposureMSpace n i] G ≤ 1
    linarith [h_lb_i', h_ub_i1', h_add_i1_val, h_ci']

/-- **[B2 — conditional mean of Doob differences is zero — PROVED]**
  For all n, i with i < n - 1, the conditional expectation of `doobDiff n (i+1)` given ℱ_i
  is a.s. zero. This is the martingale property:
  E[E[ζ|ℱ_{i+1}] − E[ζ|ℱ_i] | ℱ_i] = E[ζ|ℱ_i] − E[ζ|ℱ_i] = 0 (tower property).

  **Mathematical argument**: By the tower property of conditional expectation,
  E[E[ζ|ℱ_{i+1}] | ℱ_i] = E[ζ|ℱ_i] (since ℱ_i ⊆ ℱ_{i+1}).
  Therefore E[doobDiff n (i+1) | ℱ_i] = E[E[ζ|ℱ_{i+1}] | ℱ_i] − E[ζ|ℱ_i] = 0 a.s.

  In terms of the condExpKernel: for a.e. ω', the integral of doobDiff n (i+1) w.r.t.
  condExpKernel (gnHalf n) (ℱ_i) ω' equals 0.
-/
private lemma doobDiff_condExpKernel_integral_zero (n : ℕ) (i : ℕ) (hi : i < n - 1)
    [IsProbabilityMeasure (gnHalf n)] :
    ∀ᵐ ω' ∂(gnHalf n).trim ((vertexExposureFiltration n).le i),
      ∫ G, doobDiff n (i + 1) G ∂(condExpKernel (gnHalf n) (vertexExposureFiltration n i) ω') = 0 := by
  -- Notation
  have hmi := (vertexExposureFiltration n).le i
  have hmi1 := (vertexExposureFiltration n).le (i + 1)
  have hii1 : vertexExposureFiltration n i ≤ vertexExposureFiltration n (i + 1) :=
    (vertexExposureFiltration n).mono (Nat.le_succ i)
  haveI : SigmaFinite ((gnHalf n).trim hmi1) := inferInstance
  haveI : SigmaFinite ((gnHalf n).trim hmi) := inferInstance
  -- Step 1: E[doobDiff n (i+1) | ℱ_i] = 0 a.e. under gnHalf n
  -- Argument: E[doobDiff | ℱ_i] = E[E[ζ|ℱ_{i+1}] - E[ζ|ℱ_i] | ℱ_i]
  --         = E[E[ζ|ℱ_{i+1}] | ℱ_i] - E[E[ζ|ℱ_i] | ℱ_i]   (linearity)
  --         = E[ζ|ℱ_i] - E[ζ|ℱ_i]   (tower + self-conditioning)
  --         = 0
  -- The function ζ
  let ζ := fun G : SimpleGraph (Fin n) => (cochromaticNumber G : ℝ)
  -- Step 1: doobDiff n (i+1) =ᵐ[gnHalf n] E[ζ|ℱ_{i+1}] - E[ζ|ℱ_i]
  have hdd : doobDiff n (i + 1) =
      (gnHalf n)[ζ | vertexExposureMSpace n (i + 1)] -
      (gnHalf n)[ζ | vertexExposureMSpace n i] := by
    ext G; simp [doobDiff, ζ]
  -- Step 2: E[doobDiff | ℱ_i] = E[E[ζ|ℱ_{i+1}] - E[ζ|ℱ_i] | ℱ_i]
  --        = E[E[ζ|ℱ_{i+1}]|ℱ_i] - E[E[ζ|ℱ_i]|ℱ_i]  (linearity)
  --        = E[ζ|ℱ_i] - E[ζ|ℱ_i]  (tower + self-conditioning)
  --        = 0
  have h_condExp_zero :
      (gnHalf n)[doobDiff n (i + 1) | vertexExposureFiltration n i] =ᵐ[(gnHalf n)]
      (0 : SimpleGraph (Fin n) → ℝ) := by
    -- Rewrite using hdd
    have hrw : (gnHalf n)[doobDiff n (i + 1) | vertexExposureFiltration n i] =ᵐ[(gnHalf n)]
        (gnHalf n)[(gnHalf n)[ζ | vertexExposureFiltration n (i + 1)] -
            (gnHalf n)[ζ | vertexExposureFiltration n i] |
            vertexExposureFiltration n i] :=
      condExp_congr_ae (Filter.EventuallyEq.of_eq hdd)
    -- Linearity: E[A - B | m] = E[A | m] - E[B | m]
    have hlin : (gnHalf n)[(gnHalf n)[ζ | vertexExposureFiltration n (i + 1)] -
            (gnHalf n)[ζ | vertexExposureFiltration n i] |
            vertexExposureFiltration n i] =ᵐ[(gnHalf n)]
        (gnHalf n)[(gnHalf n)[ζ | vertexExposureFiltration n (i + 1)] |
              vertexExposureFiltration n i] -
          (gnHalf n)[(gnHalf n)[ζ | vertexExposureFiltration n i] |
              vertexExposureFiltration n i] :=
      condExp_sub (m := vertexExposureFiltration n i) Integrable.of_finite Integrable.of_finite
    -- Tower: E[E[ζ|ℱ_{i+1}]|ℱ_i] = E[ζ|ℱ_i]
    have htower : (gnHalf n)[(gnHalf n)[ζ | vertexExposureFiltration n (i + 1)] |
            vertexExposureFiltration n i] =ᵐ[(gnHalf n)]
        (gnHalf n)[ζ | vertexExposureFiltration n i] :=
      condExp_condExp_of_le hii1 hmi1 (f := ζ)
    -- Self-conditioning: E[E[ζ|ℱ_i]|ℱ_i] = E[ζ|ℱ_i]
    have hself : (gnHalf n)[(gnHalf n)[ζ | vertexExposureFiltration n i] |
            vertexExposureFiltration n i] =ᵐ[(gnHalf n)]
        (gnHalf n)[ζ | vertexExposureFiltration n i] :=
      condExp_condExp_of_le le_rfl hmi (f := ζ)
    -- Combine
    filter_upwards [hrw, hlin, htower, hself] with G hrw' hlin' htower' hself'
    simp only [Pi.zero_apply, Pi.sub_apply] at *
    linarith
  -- Step 3: Lift to trim measure and convert to fiberwise integral
  -- Abbreviate the trim measure
  let μtrim := (gnHalf n).trim hmi
  have h_trim_eq : (gnHalf n)[doobDiff n (i + 1) | vertexExposureFiltration n i] =ᵐ[μtrim]
      (fun ω' => ∫ G, doobDiff n (i + 1) G ∂condExpKernel (gnHalf n)
          (vertexExposureFiltration n i) ω') :=
    condExp_ae_eq_trim_integral_condExpKernel hmi Integrable.of_finite
  -- Lift h_condExp_zero to the trimmed measure
  have h_zero_trim : (gnHalf n)[doobDiff n (i + 1) | vertexExposureFiltration n i] =ᵐ[μtrim]
      (0 : SimpleGraph (Fin n) → ℝ) :=
    (StronglyMeasurable.ae_eq_trim_iff hmi stronglyMeasurable_condExp
      stronglyMeasurable_const).mpr h_condExp_zero
  filter_upwards [h_trim_eq.symm.trans h_zero_trim] with ω' hω'
  simpa using hω'

/-- **[B — conditional sub-Gaussianity of Doob differences — PROVED]**
  Each Doob difference `doobDiff n (i+1)` has conditional sub-Gaussian MGF with c = 1
  with respect to `ℱ_i = vertexExposureFiltration n i`.

  Proof: Unfold to `Kernel.HasSubgaussianMGF.of_rat`. The two required conditions are:
  1. Integrability of exp(t * doobDiff): follows from `Integrable.of_finite` (finite space)
     plus `condExpKernel_comp_trim`.
  2. Fiberwise MGF bound: for a.e. ω', apply `mgf_le_of_mem_Icc_of_integral_eq_zero`
     with a = -1, b = 1 to the probability measure `condExpKernel (gnHalf n) ℱ_i ω'`.
     This requires `doobDiff_mem_Icc` (B1) and `doobDiff_condExpKernel_integral_zero` (B2).
-/
private lemma doobDiff_hasCondSubgaussianMGF (n : ℕ) (i : ℕ) (hi : i < n - 1)
    [IsProbabilityMeasure (gnHalf n)] :
    HasCondSubgaussianMGF
      (m := vertexExposureFiltration n i)
      (hm := (vertexExposureFiltration n).le i)
      (doobDiff n (i + 1)) 1 (gnHalf n) := by
  haveI hfin : IsFiniteMeasure (gnHalf n) := inferInstance
  -- Abbreviate the filtration stage and its le-proof
  let hm := (vertexExposureFiltration n).le i
  -- HasCondSubgaussianMGF unfolds directly to Kernel.HasSubgaussianMGF with condExpKernel
  -- (see definition: HasCondSubgaussianMGF X c μ := Kernel.HasSubgaussianMGF X c (condExpKernel μ m) (μ.trim hm))
  -- We apply Kernel.HasSubgaussianMGF.of_rat with the two required conditions.
  apply Kernel.HasSubgaussianMGF.of_rat
  · -- h_int: exp(t * doobDiff) integrable w.r.t. condExpKernel ∘ₘ (gnHalf n).trim hm
    -- Note: condExpKernel_comp_trim gives condExpKernel μ m ∘ₘ μ.trim hm = μ
    intro t
    rw [condExpKernel_comp_trim hm]
    exact Integrable.of_finite
  · -- h_mgf: for a.e. ω', mgf (doobDiff n (i+1)) (condExpKernel ω') q ≤ exp(1 * q²/2)
    -- We use Hoeffding: (‖1 - (-1)‖₊ / 2)^2 = 1, giving c = 1.
    intro q
    -- Get the mean-zero property in each fiber (a.e. under (gnHalf n).trim hm)
    have h_zero : ∀ᵐ ω' ∂(gnHalf n).trim hm,
        ∫ G, doobDiff n (i + 1) G ∂
          (condExpKernel (gnHalf n) (vertexExposureFiltration n i) ω') = 0 :=
      doobDiff_condExpKernel_integral_zero n i hi
    -- Get the [-1,1] bound a.s. under gnHalf n
    have h_icc := doobDiff_mem_Icc n i hi
    -- Transfer the Icc bound to a.e. fiber via Fubini/disintegration
    have h_icc_fiber : ∀ᵐ ω' ∂(gnHalf n).trim hm,
        ∀ᵐ G ∂(condExpKernel (gnHalf n) (vertexExposureFiltration n i) ω'),
        doobDiff n (i + 1) G ∈ Set.Icc (-1 : ℝ) 1 := by
      apply Measure.ae_ae_of_ae_comp
      rw [condExpKernel_comp_trim hm]
      exact h_icc
    filter_upwards [h_zero, h_icc_fiber] with ω' h_zero' h_icc'
    -- In this fiber, condExpKernel ω' is a probability measure (from IsMarkovKernel)
    -- condExpKernel is a Markov kernel, so each fiber is a probability measure
    haveI : IsProbabilityMeasure
        (condExpKernel (gnHalf n) (vertexExposureFiltration n i) ω') :=
      (inferInstance : IsMarkovKernel (condExpKernel (gnHalf n) (vertexExposureFiltration n i)))
        |>.isProbabilityMeasure ω'
    -- Apply Hoeffding's lemma in the fiber to get HasSubgaussianMGF with parameter (‖b-a‖₊/2)^2
    have hsgf := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (AEMeasurable.of_discrete (μ := condExpKernel (gnHalf n) (vertexExposureFiltration n i) ω'))
      h_icc' h_zero'
    -- hsgf has parameter (‖1-(-1)‖₊/2)^2 = (2/2)^2 = 1 : ℝ≥0
    -- so hsgf : HasSubgaussianMGF ... (1 : ℝ≥0) _
    -- and hsgf.mgf_le matches the goal exactly
    convert hsgf.mgf_le (q : ℝ) using 2
    norm_num [NNReal.coe_pow, NNReal.coe_div]

/-- Y 0 = 0 is trivially sub-Gaussian with c = 1 (since the zero function has mgf = 1 ≤ exp(t²/2)). -/
private lemma doobDiff_Y0_subgaussian (n : ℕ) :
    HasSubgaussianMGF (doobDiff n 0) (1 : NNReal) (gnHalf n) := by
  -- doobDiff n 0 = 0 by definition.
  haveI hprob : IsProbabilityMeasure (gnHalf n) := by unfold gnHalf; infer_instance
  haveI : IsZeroOrProbabilityMeasure (gnHalf n) := inferInstance
  -- Use HasSubgaussianMGF.fun_zero (gives c = 0) then upgrade: HasSubgaussianMGF.congr
  -- Actually: doobDiff n 0 = fun _ => 0, so it equals the zero function.
  -- HasSubgaussianMGF.fun_zero : HasSubgaussianMGF (fun _ ↦ 0) 0 μ for [IsZeroOrProbabilityMeasure]
  -- We need c = 1, so we build directly:
  refine ⟨fun t => ?_, fun t => ?_⟩
  · -- exp(t * doobDiff n 0 G) = exp(0) = 1, integrable
    have : doobDiff n 0 = fun _ => (0 : ℝ) := by ext G; simp [doobDiff]
    simp [this]
  · -- mgf (doobDiff n 0) (gnHalf n) t = 1 ≤ exp((1:ℝ) * t^2/2)
    have heq : doobDiff n 0 = fun _ => (0 : ℝ) := by ext G; simp [doobDiff]
    simp only [mgf, heq, mul_zero, Real.exp_zero]
    -- ∫ _ ∂(gnHalf n), (1:ℝ) = 1 in a probability measure
    have : ∫ _ : SimpleGraph (Fin n), (1 : ℝ) ∂(gnHalf n) = 1 := by
      simp [integral_const, measure_univ]
    rw [this]
    -- 1 ≤ exp((1:ℝ≥0) * t^2/2) — NNReal cast is ≥ 0
    exact Real.one_le_exp (by positivity)

/-- **Azuma-Hoeffding tail bound for ζ** (proved from the three sub-sorrys above).

  For any n ≥ 1 and t ≥ 0:
      P_{G ~ G(n,1/2)}[ζ(G) ≥ 𝔼[ζ] + t] ≤ exp(−t² / (2n))

  **SORRY COUNT**: 0. All sub-lemmas proved: `doobDiff_telescope`, `doobDiff_hasCondSubgaussianMGF`.
  The outer wiring is proved: `measure_sum_ge_le_of_hasCondSubgaussianMGF` is applied correctly.
-/
theorem zeta_azuma_tail_bound (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 ≤ t) :
    (gnHalf n).real {G : SimpleGraph (Fin n) |
      ∫ G' : SimpleGraph (Fin n), (cochromaticNumber G' : ℝ) ∂(gnHalf n) + t ≤
        (cochromaticNumber G : ℝ)} ≤
      Real.exp (-(t ^ 2) / (2 * (n : ℝ))) := by
  haveI : IsProbabilityMeasure (gnHalf n) := by unfold gnHalf; infer_instance
  haveI : IsZeroOrProbabilityMeasure (gnHalf n) := inferInstance
  -- StronglyAdapted for doobDiff: doobDiff n i is strongly measurable w.r.t. ℱ_i
  -- (difference of two strongly-measurable functions at stage i and i+1, both ≤ ℱ_i)
  have h_adapted : StronglyAdapted (vertexExposureFiltration n) (doobDiff n) := by
    intro i
    match i with
    | 0 =>
      -- doobDiff n 0 = 0, trivially strongly measurable
      simp only [doobDiff]
      exact stronglyMeasurable_const
    | i + 1 =>
      -- doobDiff n (i+1) = E[ζ|ℱ_{i+1}] - E[ζ|ℱ_i]
      -- Both E[ζ|ℱ_{i+1}] and E[ζ|ℱ_i] are strongly measurable w.r.t. ℱ_{i+1}
      -- (condExp at stage k is StronglyMeasurable[ℱ_k]; ℱ_i ≤ ℱ_{i+1})
      simp only [doobDiff]
      apply StronglyMeasurable.sub
      · -- E[ζ|ℱ_{i+1}] is StronglyMeasurable[ℱ_{i+1}]
        exact stronglyMeasurable_condExp
      · -- E[ζ|ℱ_i] is StronglyMeasurable[ℱ_i] ≤ ℱ_{i+1}
        apply StronglyMeasurable.mono stronglyMeasurable_condExp
        exact (vertexExposureFiltration n).mono (Nat.le_succ i)
  have h_Y0 : HasSubgaussianMGF (doobDiff n 0) (1 : NNReal) (gnHalf n) :=
    doobDiff_Y0_subgaussian n
  haveI : StandardBorelSpace (SimpleGraph (Fin n)) := instStandardBorelSpaceGraph n
  -- Apply Azuma-Hoeffding: get tail bound for the sum process
  -- cY i = 1 for all i; Σ_{i<n} cY i = n
  -- Use a suffices to drive type inference of h_azuma
  suffices h_suffices :
      (gnHalf n).real {G : SimpleGraph (Fin n) |
        t ≤ ∑ i ∈ Finset.range n, doobDiff n i G} ≤
        Real.exp (-(t ^ 2) / (2 * (n : ℝ))) by
    -- Rewrite goal via telescope
    have h_tel := doobDiff_telescope n hn
    have h_set_eq :
        (gnHalf n).real {G : SimpleGraph (Fin n) |
          ∫ G', (cochromaticNumber G' : ℝ) ∂(gnHalf n) + t ≤ (cochromaticNumber G : ℝ)} =
        (gnHalf n).real {G : SimpleGraph (Fin n) |
          t ≤ ∑ i ∈ Finset.range n, doobDiff n i G} := by
      apply measureReal_congr
      rw [Filter.EventuallyEq]
      filter_upwards [h_tel] with G hG
      exact propext ⟨fun (h : ∫ G', (cochromaticNumber G' : ℝ) ∂(gnHalf n) + t ≤
              (cochromaticNumber G : ℝ)) =>
          show t ≤ ∑ i ∈ Finset.range n, doobDiff n i G by linarith [hG],
        fun (h : t ≤ ∑ i ∈ Finset.range n, doobDiff n i G) =>
          show ∫ G', (cochromaticNumber G' : ℝ) ∂(gnHalf n) + t ≤
              (cochromaticNumber G : ℝ) by linarith [hG]⟩
    rwa [h_set_eq]
  -- Now prove the suffices: Azuma gives P[t ≤ Σ doobDiff] ≤ exp(-t²/(2·∑cY))
  -- and ∑cY = n
  have h_cY_sum : Finset.sum (Finset.range n) (fun (_ : ℕ) => (1 : NNReal)) = (n : NNReal) := by
    simp [Finset.card_range]
  calc (gnHalf n).real {G : SimpleGraph (Fin n) | t ≤ ∑ i ∈ Finset.range n, doobDiff n i G}
      ≤ Real.exp (-(t ^ 2) / (2 * ↑(Finset.sum (Finset.range n) (fun (_ : ℕ) => (1 : NNReal))))) := by
        apply measure_sum_ge_le_of_hasCondSubgaussianMGF (ℱ := vertexExposureFiltration n)
          (Y := doobDiff n) (cY := fun _ => (1 : NNReal))
          h_adapted h_Y0 n
          (fun i hi => doobDiff_hasCondSubgaussianMGF n i hi)
          ht
    _ = Real.exp (-(t ^ 2) / (2 * (n : ℝ))) := by
        congr 1
        rw [h_cY_sum]
        simp [NNReal.coe_natCast]

/-- **Azuma-Hoeffding lower tail for ζ** (proved from the sub-lemmas above by negation).

  For any n ≥ 1 and t ≥ 0:
      P_{G ~ G(n,1/2)}[ζ(G) ≤ 𝔼[ζ] − t] ≤ exp(−t² / (2n))

  Proof: apply `measure_sum_ge_le_of_hasCondSubgaussianMGF` to the negated process
  `−doobDiff n i`, which has the same sub-Gaussian parameter c = 1 by `HasSubgaussianMGF.neg`
  and `HasCondSubgaussianMGF.neg`. The telescope gives Σ (−Y_i) = E[ζ] − ζ a.e.,
  so {t ≤ Σ (−Y_i)} = {ζ ≤ E[ζ] − t}.
-/
theorem zeta_azuma_lower_tail_bound :
    ∃ n₀ : ℕ, ∀ n : ℕ, 0 < n → ∀ t : ℝ, 0 ≤ t →
      (gnHalf n).real {G : SimpleGraph (Fin n) |
        (cochromaticNumber G : ℝ) ≤
          ∫ G' : SimpleGraph (Fin n), (cochromaticNumber G' : ℝ) ∂(gnHalf n) - t} ≤
        Real.exp (-(t ^ 2) / (2 * (n : ℝ))) :=
  ⟨0, fun n hn t ht => by
    haveI : IsProbabilityMeasure (gnHalf n) := by unfold gnHalf; infer_instance
    haveI : IsZeroOrProbabilityMeasure (gnHalf n) := inferInstance
    let negDoobDiff : ℕ → SimpleGraph (Fin n) → ℝ := fun i G => -(doobDiff n i G)
    have h_adapted : StronglyAdapted (vertexExposureFiltration n) negDoobDiff := by
      intro i
      show StronglyMeasurable[vertexExposureFiltration n i] (fun G => -(doobDiff n i G))
      apply StronglyMeasurable.neg
      match i with
      | 0 =>
        show StronglyMeasurable[vertexExposureFiltration n 0] (fun _ => (0 : ℝ))
        exact stronglyMeasurable_const
      | i + 1 =>
        show StronglyMeasurable[vertexExposureFiltration n (i + 1)]
          (fun G => (gnHalf n)[(fun G' => (cochromaticNumber G' : ℝ)) | vertexExposureMSpace n (i + 1)] G -
                    (gnHalf n)[(fun G' => (cochromaticNumber G' : ℝ)) | vertexExposureMSpace n i] G)
        exact (stronglyMeasurable_condExp.sub
          (stronglyMeasurable_condExp.mono ((vertexExposureFiltration n).mono (Nat.le_succ i))))
    have h_Y0 : HasSubgaussianMGF (negDoobDiff 0) (1 : NNReal) (gnHalf n) :=
      (doobDiff_Y0_subgaussian n).neg
    haveI : StandardBorelSpace (SimpleGraph (Fin n)) := instStandardBorelSpaceGraph n
    have h_cond : ∀ i, i < n - 1 →
        HasCondSubgaussianMGF
          (m := vertexExposureFiltration n i)
          (hm := (vertexExposureFiltration n).le i)
          (negDoobDiff (i + 1)) 1 (gnHalf n) :=
      fun i hi => (doobDiff_hasCondSubgaussianMGF n i hi).neg
    have h_cY_sum : Finset.sum (Finset.range n) (fun (_ : ℕ) => (1 : NNReal)) = (n : NNReal) := by
      simp [Finset.card_range]
    have h_tel := doobDiff_telescope n hn
    -- Rewrite the LHS set via a.e. equality using the telescope
    have h_ae_eq :
        {G : SimpleGraph (Fin n) | (cochromaticNumber G : ℝ) ≤
          ∫ G', (cochromaticNumber G' : ℝ) ∂(gnHalf n) - t} =ᵐ[(gnHalf n)]
        {G : SimpleGraph (Fin n) | t ≤ ∑ i ∈ Finset.range n, negDoobDiff i G} := by
      filter_upwards [h_tel] with G hG
      -- hG : ∑ doobDiff n i G = ζ(G) - E[ζ]
      -- ∑ negDoobDiff = -(∑ doobDiff) = E[ζ] - ζ(G)
      -- Compute ∑ negDoobDiff directly
      have h_sum_neg : ∑ i ∈ Finset.range n, negDoobDiff i G =
          (∫ G', (cochromaticNumber G' : ℝ) ∂(gnHalf n)) - (cochromaticNumber G : ℝ) := by
        have : ∑ i ∈ Finset.range n, negDoobDiff i G =
            -(∑ i ∈ Finset.range n, doobDiff n i G) := by
          simp only [negDoobDiff, Finset.sum_neg_distrib]
        linarith [this, hG]
      -- Goal is a Prop equality: (ζ ≤ E[ζ]-t) = (t ≤ ∑ negDoobDiff)
      -- Rewrite the RHS of the goal using h_sum_neg:
      change ((cochromaticNumber G : ℝ) ≤ (∫ G', (cochromaticNumber G' : ℝ) ∂(gnHalf n)) - t) =
        (t ≤ ∑ i ∈ Finset.range n, negDoobDiff i G)
      rw [h_sum_neg]
      exact propext ⟨fun h => by linarith, fun h => by linarith⟩
    rw [measureReal_congr h_ae_eq]
    suffices h_suffices :
        (gnHalf n).real {G : SimpleGraph (Fin n) |
          t ≤ ∑ i ∈ Finset.range n, negDoobDiff i G} ≤
          Real.exp (-(t ^ 2) / (2 * (n : ℝ))) by
      exact h_suffices
    calc (gnHalf n).real {G : SimpleGraph (Fin n) | t ≤ ∑ i ∈ Finset.range n, negDoobDiff i G}
        ≤ Real.exp (-(t ^ 2) / (2 * ↑(Finset.sum (Finset.range n) (fun (_ : ℕ) => (1 : NNReal))))) :=
          measure_sum_ge_le_of_hasCondSubgaussianMGF (ℱ := vertexExposureFiltration n)
            (Y := negDoobDiff) (cY := fun _ => (1 : NNReal))
            h_adapted h_Y0 n h_cond ht
      _ = Real.exp (-(t ^ 2) / (2 * (n : ℝ))) := by
          congr 1; rw [h_cY_sum]; simp [NNReal.coe_natCast]⟩

end AzumaConcentration


/-! ## Paley-Zygmund Lower Bound for ζ

  The axiom `heckel_zeta_paley_zygmund` (that P[ζ ≤ k*] > exp(−n^{0.99})) is proved
  from two components:
  1. **Paley-Zygmund inequality** (proved, via `paley_zygmund_sum` in IndepMoments.lean):
     E[X]² ≤ E[X²] · P[X > 0] for any non-negative random variable X.
  2. **Heckel second-moment bound** (axiom, Heckel 2024 Proposition 5(b)):
     E[X^co_{k*}]² > exp(−n^{0.99}) · E[(X^co_{k*})²] under gnHalf n.

  The Paley-Zygmund inequality is a general combinatorial fact (proved in IndepMoments.lean
  as `paley_zygmund_sum`); only the second-moment calculation is Heckel-specific.
-/

section PaleyZygmundLower

open MeasureTheory ProbabilityTheory ENNReal

attribute [local instance] Classical.propDecidable

/-- Count of k-cochromatic colorings of G (as a real number). -/
noncomputable def kCochromaticColoringCount (n k : ℕ) (G : SimpleGraph (Fin n)) : ℝ :=
  (Fintype.card {col : Fin n → Fin k | IsCochromaticColoring G k col} : ℝ)

private lemma kCochromaticColoringCount_nonneg (n k : ℕ) (G : SimpleGraph (Fin n)) :
    0 ≤ kCochromaticColoringCount n k G := Nat.cast_nonneg _

/-- Z(G) > 0 iff ζ(G) ≤ k (a k-cochromatic coloring of G exists). -/
private lemma kCochromaticColoringCount_pos_iff (n k : ℕ) (G : SimpleGraph (Fin n)) :
    0 < kCochromaticColoringCount n k G ↔ cochromaticNumber G ≤ k := by
  simp only [kCochromaticColoringCount, Nat.cast_pos, Fintype.card_pos_iff, nonempty_subtype]
  constructor
  · rintro ⟨col, hcol⟩
    exact Nat.sInf_le ⟨col, hcol⟩
  · intro hle
    have hnonempty := cochromaticColoringExists_card_self (G := G)
    obtain ⟨col₀, hcol₀⟩ := Nat.sInf_mem hnonempty
    refine ⟨fun v => (col₀ v).castLE hle, ?_⟩
    intro i
    by_cases h : ∃ j : Fin (cochromaticNumber G), j.castLE hle = i
    · obtain ⟨j, rfl⟩ := h
      have heq : {v : Fin n | (col₀ v).castLE hle = j.castLE hle} = {v | col₀ v = j} := by
        ext v; constructor
        · intro hv; exact (Fin.castLE_inj (hmn := hle)).mp hv
        · intro hv; exact congrArg (Fin.castLE hle) hv
      rw [heq]; exact hcol₀ j
    · right
      intro v hv w _hw _hvw _hadj
      simp only [Set.mem_setOf_eq] at hv
      exact absurd ⟨col₀ v, hv ▸ rfl⟩ h

/-- **[Sum-swap identity]** Proof step 0 for `heckel_cochromatic_second_moment`.

  The second moment ∑_G Z(G)² equals ∑_{C1} ∑_{C2} |{G | C1,C2 ∈ colorings(G)}|
  via Fubini / sum exchange:
    ∑_G (|{col | P col G}|)² = ∑_{C1} ∑_{C2} |{G | P C1 G ∧ P C2 G}|

  Proof: push casts to ℕ, then use `Finset.sum_comm` to transpose the
  G-sum with (C1, C2) after expanding the square as a double sum via
  `Finset.card_eq_sum_ones` + `Finset.sum_mul` / `Finset.mul_sum`.
-/
private lemma sum_kCochromaticColoringCount_sq_eq (n k : ℕ) :
    ∑ G : SimpleGraph (Fin n), (kCochromaticColoringCount n k G) ^ 2 =
    ∑ C1 : Fin n → Fin k, ∑ C2 : Fin n → Fin k,
      ((Finset.univ (α := SimpleGraph (Fin n))).filter (fun G =>
        IsCochromaticColoring G k C1 ∧ IsCochromaticColoring G k C2) : Finset _).card := by
  -- Standard Fubini double-counting: ∑_G Z(G)² = ∑_{C1,C2} |{G : C1,C2 ∈ colorings(G)}|.
  -- Step 1: for each G, expand (|S_G|)² as a double if-sum over colorings.
  have step1 : ∀ G : SimpleGraph (Fin n),
      ((Finset.univ (α := Fin n → Fin k)).filter (IsCochromaticColoring G k)).card ^ 2 =
      ∑ C1 : Fin n → Fin k, ∑ C2 : Fin n → Fin k,
        if IsCochromaticColoring G k C1 ∧ IsCochromaticColoring G k C2 then 1 else 0 := by
    intro G
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter, sq, Finset.sum_mul, Finset.mul_sum]
    congr 1; ext C1; congr 1; ext C2
    split_ifs <;> simp_all
  -- Step 2: prove the ℕ version, then cast.
  have hℕ : ∑ G : SimpleGraph (Fin n),
      (Fintype.card {col : Fin n → Fin k | IsCochromaticColoring G k col}) ^ 2 =
      ∑ C1 : Fin n → Fin k, ∑ C2 : Fin n → Fin k,
        ((Finset.univ (α := SimpleGraph (Fin n))).filter (fun G =>
          IsCochromaticColoring G k C1 ∧ IsCochromaticColoring G k C2)).card := by
    simp only [Fintype.card_subtype]
    -- Expand (filter...).card^2 pointwise via step1, then swap summation order
    trans ∑ G : SimpleGraph (Fin n), ∑ C1 : Fin n → Fin k, ∑ C2 : Fin n → Fin k,
        if IsCochromaticColoring G k C1 ∧ IsCochromaticColoring G k C2 then (1 : ℕ) else 0
    · apply Finset.sum_congr rfl; intro G _; exact step1 G
    · -- Fubini: swap G ↔ C1, then G ↔ C2
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro C1 _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro C2 _
      -- Goal: ∑ G, if (...) then 1 else 0 = (filter ...).card
      rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
  simp only [kCochromaticColoringCount]
  exact_mod_cast hℕ

/-- The filter `{G | P G ∧ P G}` equals `{G | P G}` via `(P ∧ P) ↔ P`. -/
private lemma sum_cochromatic_filter_and_self_eq (n k : ℕ) (C : Fin n → Fin k) :
    ((Finset.univ (α := SimpleGraph (Fin n))).filter
        (fun G => IsCochromaticColoring G k C ∧ IsCochromaticColoring G k C)).card =
    ((Finset.univ (α := SimpleGraph (Fin n))).filter
        (fun G => IsCochromaticColoring G k C)).card := by
  congr 1
  apply Finset.filter_congr
  intro G _
  exact ⟨And.left, fun h => ⟨h, h⟩⟩

/-- The double coloring sum splits into the diagonal term plus the off-diagonal term (ℕ identity).
    Diagonal: C1 = C2 contribution; off-diagonal: C1 ≠ C2 (via `Finset.univ.erase`). -/
private lemma sum_cochromatic_coloring_diag_split_nat (n k : ℕ) :
    ∑ C1 : Fin n → Fin k, ∑ C2 : Fin n → Fin k,
      ((Finset.univ (α := SimpleGraph (Fin n))).filter (fun G =>
        IsCochromaticColoring G k C1 ∧ IsCochromaticColoring G k C2)).card =
    (∑ C : Fin n → Fin k,
      ((Finset.univ (α := SimpleGraph (Fin n))).filter (fun G =>
        IsCochromaticColoring G k C)).card) +
    (∑ C1 : Fin n → Fin k, ∑ C2 ∈ (Finset.univ : Finset (Fin n → Fin k)).erase C1,
      ((Finset.univ (α := SimpleGraph (Fin n))).filter (fun G =>
        IsCochromaticColoring G k C1 ∧ IsCochromaticColoring G k C2)).card) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro C1 _
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ C1)]
  congr 1
  exact sum_cochromatic_filter_and_self_eq n k C1

/-- **[Diagonal = First Moment]** The diagonal coloring sum equals the first moment.
    Proof: Fubini / `Finset.sum_comm` swaps the order of summation over colorings and graphs. -/
lemma heckel_cochromatic_second_moment_diag_is_first_moment (n k : ℕ) :
    (∑ C ∈ (Finset.univ : Finset (Fin n → Fin k)),
      (Fintype.card {G : SimpleGraph (Fin n) // IsCochromaticColoring G k C} : ℝ)) =
    ∑ G : SimpleGraph (Fin n), kCochromaticColoringCount n k G := by
  have hN : ∑ C ∈ (Finset.univ : Finset (Fin n → Fin k)),
      Fintype.card {G : SimpleGraph (Fin n) // IsCochromaticColoring G k C} =
      ∑ G : SimpleGraph (Fin n),
      Fintype.card {C : Fin n → Fin k // IsCochromaticColoring G k C} := by
    simp only [Fintype.card_subtype]
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
  simp only [kCochromaticColoringCount]
  exact_mod_cast hN

/-- **[Diagonal split]** The cochromatic second-moment double sum splits as:
    `∑_G Z(G)²  =  (∑_G Z(G))  +  off-diagonal term`

  - Diagonal term equals the first moment `∑_G Z(G)` via sum-swap (Fubini);
    proved in `heckel_cochromatic_second_moment_diag_is_first_moment`.
  - Off-diagonal term `∑_{C1 ≠ C2} |{G | C1,C2 ∈ colorings(G)}|` is exactly the content
    bounded by `heckel_cochromatic_second_moment` (Heckel 2024 Prop. 5(b)).
    Next refinement target: tighten to `heckel_cochromatic_second_moment_offdiag_bound`. -/
theorem heckel_cochromatic_second_moment_diag_split (n k : ℕ) :
    ∑ G : SimpleGraph (Fin n), (kCochromaticColoringCount n k G) ^ 2 =
    (∑ G : SimpleGraph (Fin n), kCochromaticColoringCount n k G) +
    (∑ C1 : Fin n → Fin k, ∑ C2 ∈ (Finset.univ : Finset (Fin n → Fin k)).erase C1,
      ((Finset.univ (α := SimpleGraph (Fin n))).filter (fun G =>
        IsCochromaticColoring G k C1 ∧ IsCochromaticColoring G k C2)).card : ℝ) := by
  have h_old : ∑ G : SimpleGraph (Fin n), (kCochromaticColoringCount n k G) ^ 2 =
      (∑ C : Fin n → Fin k,
        ((Finset.univ (α := SimpleGraph (Fin n))).filter (fun G =>
          IsCochromaticColoring G k C)).card : ℝ) +
      (∑ C1 : Fin n → Fin k, ∑ C2 ∈ (Finset.univ : Finset (Fin n → Fin k)).erase C1,
        ((Finset.univ (α := SimpleGraph (Fin n))).filter (fun G =>
          IsCochromaticColoring G k C1 ∧ IsCochromaticColoring G k C2)).card : ℝ) := by
    rw [sum_kCochromaticColoringCount_sq_eq]
    exact_mod_cast sum_cochromatic_coloring_diag_split_nat n k
  rw [h_old]
  congr 1
  rw [← heckel_cochromatic_second_moment_diag_is_first_moment]
  simp only [Fintype.card_subtype]

/-- **[Off-diagonal term]** The named off-diagonal coloring double sum in the cochromatic
    second-moment split.  This is the remainder in `heckel_cochromatic_second_moment_diag_split`:
    `∑_G Z(G)² = ∑_G Z(G) + heckel_cochromatic_second_moment_offdiag_term n k`. -/
noncomputable def heckel_cochromatic_second_moment_offdiag_term (n k : ℕ) : ℝ :=
  ∑ C1 : Fin n → Fin k, ∑ C2 ∈ (Finset.univ : Finset (Fin n → Fin k)).erase C1,
    ((Finset.univ (α := SimpleGraph (Fin n))).filter (fun G =>
      IsCochromaticColoring G k C1 ∧ IsCochromaticColoring G k C2)).card

/-- The off-diagonal term is nonneg (finite sum of cast nonneg terms). -/
lemma heckel_cochromatic_second_moment_offdiag_term_nonneg (n k : ℕ) :
    0 ≤ heckel_cochromatic_second_moment_offdiag_term n k :=
  Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

/-- Diagonal-split restated using the named offdiag term. -/
lemma heckel_cochromatic_second_moment_diag_split_offdiag (n k : ℕ) :
    ∑ G : SimpleGraph (Fin n), (kCochromaticColoringCount n k G) ^ 2 =
    (∑ G : SimpleGraph (Fin n), kCochromaticColoringCount n k G) +
    heckel_cochromatic_second_moment_offdiag_term n k :=
  heckel_cochromatic_second_moment_diag_split n k

/-- **[AXIOM — Heckel off-diagonal bound]** (Heckel 2024, Proposition 5(b), off-diagonal part)

  The off-diagonal contribution to the second moment satisfies:
    exp(−n^{0.99}) · offdiag_term · |Ω| < (∑Z)² − exp(−n^{0.99}) · ∑Z · |Ω|

  This is the targeted crystallization of Heckel Prop 5(b): the off-diagonal coloring-pair
  count is small enough that the second-moment ratio E[Z]²/E[Z²] > exp(−n^{0.99}).

  Together with `heckel_cochromatic_second_moment_diag_split_offdiag` (∑Z² = ∑Z + offdiag),
  this implies `heckel_cochromatic_second_moment` by a purely algebraic bridge.

  Source: Heckel (2024), arXiv:2409.17614, Proposition 5(b).
-/
axiom heckel_offdiag_term_bound (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n → 0 < n →
      let k := ⌊kThresholdWitness n - (n : ℝ)^(1 - ε / 2)⌋₊
      Real.exp (-(n : ℝ)^(99 / 100 : ℝ)) *
        heckel_cochromatic_second_moment_offdiag_term n k *
        (Fintype.card (SimpleGraph (Fin n)) : ℝ) <
        (∑ G : SimpleGraph (Fin n), kCochromaticColoringCount n k G) ^ 2 -
        Real.exp (-(n : ℝ)^(99 / 100 : ℝ)) *
          (∑ G : SimpleGraph (Fin n), kCochromaticColoringCount n k G) *
          (Fintype.card (SimpleGraph (Fin n)) : ℝ)

/-- **[Heckel second-moment bound]** (Heckel 2024, Proposition 5(b))

  Proved from `heckel_offdiag_term_bound` + `heckel_cochromatic_second_moment_diag_split_offdiag`
  via the algebraic bridge:
    exp · (∑Z + offdiag) · |Ω|  =  exp · ∑Z · |Ω|  +  exp · offdiag · |Ω|
                                 <  exp · ∑Z · |Ω|  +  ((∑Z)² − exp · ∑Z · |Ω|)
                                 =  (∑Z)²

  **Axiom count**: 0 (proved theorem; mathematical content in `heckel_offdiag_term_bound`)
  **Sorry count**: 0
-/
theorem heckel_cochromatic_second_moment (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n → 0 < n →
      let k := ⌊kThresholdWitness n - (n : ℝ)^(1 - ε / 2)⌋₊
      Real.exp (-(n : ℝ)^(99 / 100 : ℝ)) *
        (∑ G : SimpleGraph (Fin n), (kCochromaticColoringCount n k G) ^ 2) *
        (Fintype.card (SimpleGraph (Fin n)) : ℝ) <
        (∑ G : SimpleGraph (Fin n), kCochromaticColoringCount n k G) ^ 2 := by
  obtain ⟨n₀, hn₀⟩ := heckel_offdiag_term_bound ε hε_pos hε_lt
  refine ⟨n₀, fun n hn hrange hn_pos => ?_⟩
  specialize hn₀ n hn hrange hn_pos
  simp only at hn₀ ⊢
  -- Rewrite ∑Z² = ∑Z + offdiag_term
  rw [heckel_cochromatic_second_moment_diag_split_offdiag]
  -- Goal: exp * (∑Z + offdiag) * |Ω| < (∑Z)²
  -- hn₀: exp * offdiag * |Ω| < (∑Z)² − exp * ∑Z * |Ω|
  set e := Real.exp (-(n : ℝ) ^ (99 / 100 : ℝ))
  set Z := ∑ G : SimpleGraph (Fin n),
    kCochromaticColoringCount n ⌊kThresholdWitness n - (n : ℝ) ^ (1 - ε / 2)⌋₊ G
  set od := heckel_cochromatic_second_moment_offdiag_term n
    ⌊kThresholdWitness n - (n : ℝ) ^ (1 - ε / 2)⌋₊
  set Ω := (Fintype.card (SimpleGraph (Fin n)) : ℝ)
  have hexpand : e * (Z + od) * Ω = e * Z * Ω + e * od * Ω := by ring
  linarith

/-- **[Offdiag-axiom bridge]** The Heckel second-moment axiom, rewritten in terms of the named
    offdiag term: for large n in the main range, the axiom boundary
    `exp(−n^{0.99}) · (first_moment + offdiag_term) · |Ω| < first_moment²`
    holds. This connects `heckel_cochromatic_second_moment_offdiag_term` to the axiom
    `heckel_cochromatic_second_moment` explicitly. -/
lemma heckel_cochromatic_second_moment_offdiag_bound (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n → 0 < n →
      let k := ⌊kThresholdWitness n - (n : ℝ)^(1 - ε / 2)⌋₊
      Real.exp (-(n : ℝ)^(99 / 100 : ℝ)) *
        ((∑ G : SimpleGraph (Fin n), kCochromaticColoringCount n k G) +
         heckel_cochromatic_second_moment_offdiag_term n k) *
        (Fintype.card (SimpleGraph (Fin n)) : ℝ) <
        (∑ G : SimpleGraph (Fin n), kCochromaticColoringCount n k G) ^ 2 := by
  obtain ⟨n₀, hn₀⟩ := heckel_cochromatic_second_moment ε hε_pos hε_lt
  refine ⟨n₀, fun n hn hrange hn_pos => ?_⟩
  specialize hn₀ n hn hrange hn_pos
  have heq : ∑ G : SimpleGraph (Fin n), (kCochromaticColoringCount n
      ⌊kThresholdWitness n - (n : ℝ) ^ (1 - ε / 2)⌋₊ G) ^ 2 =
      (∑ G : SimpleGraph (Fin n), kCochromaticColoringCount n
        ⌊kThresholdWitness n - (n : ℝ) ^ (1 - ε / 2)⌋₊ G) +
      heckel_cochromatic_second_moment_offdiag_term n
        ⌊kThresholdWitness n - (n : ℝ) ^ (1 - ε / 2)⌋₊ :=
    heckel_cochromatic_second_moment_diag_split_offdiag n _
  simp only []
  rw [← heq]
  exact hn₀

/-- **[THEOREM — ζ Paley-Zygmund lower bound]** (proved from Paley-Zygmund + Heckel second-moment)

  **Proof**:
  Let Z G = kCochromaticColoringCount n k* G (count of k*-cochromatic colorings of G).
  Let Ω = SimpleGraph (Fin n) with |Ω| = Fintype.card (SimpleGraph (Fin n)).
  1. Axiom: exp(−n^{0.99}) · (∑ Z G²) · |Ω| < (∑ Z G)².
  2. Paley-Zygmund (`paley_zygmund_sum`): (∑ Z G)² ≤ (∑ Z G²) · S.card.
  3. gnHalf uniform: P[ζ ≤ k*] = (gnHalf n {G | ζ ≤ k*}).toReal = S.card / |Ω| · (gnHalf n univ).toReal
     Actually: P[ζ ≤ k*] = S.card · singleton_prob = S.card / |Ω| (since total prob = 1).
  4. From (1) + (2): exp(-n^{0.99}) · (∑ Z G²) · |Ω| < (∑ Z G²) · S.card.
  5. Since (∑ Z G²) > 0: exp(-n^{0.99}) · |Ω| < S.card, i.e. S.card > exp(-n^{0.99}) · |Ω|.
  6. P[ζ ≤ k*] = S.card / |Ω| > exp(-n^{0.99}).

  **Axiom count**: 1 (heckel_cochromatic_second_moment)
  **Sorry count**: 0
-/
theorem heckel_zeta_paley_zygmund (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n → 0 < n →
      Real.exp (-(n : ℝ)^(99 / 100 : ℝ)) <
        (gnHalf n {G : SimpleGraph (Fin n) |
          (cochromaticNumber G : ℝ) ≤
            kThresholdWitness n - (n : ℝ)^(1 - ε / 2)}).toReal := by
  obtain ⟨n₀, hn₀⟩ := heckel_cochromatic_second_moment ε hε_pos hε_lt
  refine ⟨n₀, fun n hn hrange hn_pos => ?_⟩
  specialize hn₀ n hn hrange hn_pos
  set k := ⌊kThresholdWitness n - (n : ℝ)^(1 - ε / 2)⌋₊ with hk_def
  set Z := kCochromaticColoringCount n k with hZ_def
  -- hn₀: exp(-n^{0.99}) * (∑ Z G²) * |Ω| < (∑ Z G)²
  have hZ_nonneg : ∀ G, 0 ≤ Z G := kCochromaticColoringCount_nonneg n k
  -- Paley-Zygmund: (∑ Z G)² ≤ (∑ Z G²) · S.card
  have hPZ := paley_zygmund_sum hZ_nonneg
  set S := Finset.univ.filter (fun G : SimpleGraph (Fin n) => 0 < Z G) with hS_def
  -- {G | Z G > 0} = {G | ζ(G) ≤ k} as sets
  have hZpos_eq_zetale : {G : SimpleGraph (Fin n) | 0 < Z G} =
      {G | cochromaticNumber G ≤ k} := by
    ext G; simp only [Set.mem_setOf_eq, hZ_def]
    exact kCochromaticColoringCount_pos_iff n k G
  -- S as a Finset matches the set in hPZ
  have hPZ' : (∑ G : SimpleGraph (Fin n), Z G) ^ 2 ≤
      (∑ G : SimpleGraph (Fin n), Z G ^ 2) * (S.card : ℝ) := hPZ
  -- ∑ Z G² > 0 (from hn₀ + nonnegativity)
  have hsum_sq_nonneg : 0 ≤ ∑ G : SimpleGraph (Fin n), Z G ^ 2 :=
    Finset.sum_nonneg (fun G _ => sq_nonneg _)
  have hOmega_pos : (0 : ℝ) < (Fintype.card (SimpleGraph (Fin n)) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hsum_sq_pos : 0 < ∑ G : SimpleGraph (Fin n), Z G ^ 2 := by
    by_contra h; push_neg at h
    have hzero := le_antisymm h hsum_sq_nonneg
    have hZ_zero : ∀ G : SimpleGraph (Fin n), Z G = 0 := by
      intro G
      have hsq : Z G ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (f := fun G => Z G ^ 2) (by
          intro G _; exact sq_nonneg _) |>.mp hzero) G (Finset.mem_univ G)
      nlinarith [hZ_nonneg G]
    have hsum_zero : (∑ G : SimpleGraph (Fin n), Z G) ^ 2 = 0 :=
      by simp [Finset.sum_eq_zero (fun G _ => hZ_zero G)]
    have hsq_zero : ∑ G : SimpleGraph (Fin n), Z G ^ 2 = 0 := hzero
    have eq1 : ∑ G : SimpleGraph (Fin n), kCochromaticColoringCount n k G ^ 2 = 0 := by
      simp only [← hZ_def]; exact hsq_zero
    have eq2 : (∑ G : SimpleGraph (Fin n), kCochromaticColoringCount n k G) ^ 2 = 0 := by
      simp only [← hZ_def]; exact hsum_zero
    have key := hn₀
    simp only [eq1, eq2, mul_zero, zero_mul, lt_self_iff_false] at key
  -- From (1) + (2): exp(-n^{0.99}) * (∑ Z G²) * |Ω| < (∑ Z G²) * S.card
  have hScard_large : Real.exp (-(n : ℝ)^(99/100:ℝ)) * (Fintype.card (SimpleGraph (Fin n)) : ℝ) <
      (S.card : ℝ) := by
    have hchain : Real.exp (-(n : ℝ)^(99/100:ℝ)) *
        (∑ G : SimpleGraph (Fin n), Z G ^ 2) *
        (Fintype.card (SimpleGraph (Fin n)) : ℝ) <
        (∑ G : SimpleGraph (Fin n), Z G ^ 2) * (S.card : ℝ) := by
      linarith
    have hmul_comm : (∑ G : SimpleGraph (Fin n), Z G ^ 2) * (S.card : ℝ) =
        (S.card : ℝ) * (∑ G : SimpleGraph (Fin n), Z G ^ 2) := mul_comm _ _
    nlinarith [mul_comm (Real.exp (-(n : ℝ)^(99/100:ℝ))) (∑ G : SimpleGraph (Fin n), Z G ^ 2),
      mul_assoc (Real.exp (-(n : ℝ)^(99/100:ℝ))) (∑ G : SimpleGraph (Fin n), Z G ^ 2)
        (Fintype.card (SimpleGraph (Fin n)) : ℝ),
      mul_comm (Fintype.card (SimpleGraph (Fin n)) : ℝ) (∑ G : SimpleGraph (Fin n), Z G ^ 2)]
  -- P[ζ ≤ k*] = S.card / |Ω|
  -- gnHalf n {G | ζ ≤ k*} = gnHalf n ↑S = S.card · (1/2)^{C(n,2)}
  -- and gnHalf n (Set.univ) = 1 = |Ω| · (1/2)^{C(n,2)}
  -- so S.card / |Ω| = gnHalf n {G | ζ ≤ k*}
  -- More precisely: (gnHalf n {G | ζ ≤ k*}).toReal = S.card * p
  -- and 1 = |Ω| * p, so p = 1/|Ω|, giving gnHalf = S.card / |Ω|
  -- Use gnHalf_uniform_finset
  -- gnHalf probability of the set {G | ζ(G) ≤ k}
  set p := (ENNReal.ofNNReal (unitInterval.toNNReal halfProb) ^ n.choose 2).toReal
  have hp_nonneg : 0 ≤ p := ENNReal.toReal_nonneg
  -- The set {G | ζ ≤ k} matches {G | Z G > 0}
  have hS_set : {G : SimpleGraph (Fin n) | cochromaticNumber G ≤ k} = ↑S := by
    ext G; simp [S, hS_def, Finset.mem_filter, hZ_def, kCochromaticColoringCount_pos_iff]
  -- gnHalf n {G | ζ ≤ k} = S.card * p
  have hgnHalf_eq : (gnHalf n {G : SimpleGraph (Fin n) | cochromaticNumber G ≤ k}).toReal =
      (S.card : ℝ) * p := by
    rw [hS_set, gnHalf_uniform_finset, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  -- |Ω| * p = 1 (probability measure)
  have hp_eq : p = (halfProb : ℝ) ^ n.choose 2 := by
    simp only [p, ENNReal.toReal_pow, ENNReal.coe_toReal, unitInterval.coe_toNNReal]
  have hOmega_p : (Fintype.card (SimpleGraph (Fin n)) : ℝ) * p = 1 := by
    rw [hp_eq]
    have huniv : gnHalf n Set.univ = 1 := MeasureTheory.measure_univ
    rw [← Finset.coe_univ, gnHalf_uniform_finset] at huniv
    have hcard : (Finset.univ.card : ℕ) = Fintype.card (SimpleGraph (Fin n)) :=
      Finset.card_univ
    have huniv' : (Fintype.card (SimpleGraph (Fin n)) : ENNReal) *
        ENNReal.ofNNReal (unitInterval.toNNReal halfProb) ^ n.choose 2 = 1 := by
      rw [← hcard]; exact huniv
    have := congr_arg ENNReal.toReal huniv'
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow,
      ENNReal.coe_toReal, unitInterval.coe_toNNReal, ENNReal.toReal_one] at this
    linarith
  -- Now: gnHalf n {G | ζ ≤ k} = S.card * p > exp(-n^{0.99})
  -- The forward inclusion: {G | ζ ≤ k} ⊆ {G | (ζ:ℝ) ≤ threshold}
  have hthresh_sub : {G : SimpleGraph (Fin n) | cochromaticNumber G ≤ k} ⊆
      {G | (cochromaticNumber G : ℝ) ≤ kThresholdWitness n - (n : ℝ)^(1 - ε / 2)} := by
    intro G hG
    simp only [Set.mem_setOf_eq] at hG ⊢
    simp only [hk_def] at hG
    by_cases hnn : 0 ≤ kThresholdWitness n - (n : ℝ)^(1 - ε/2)
    · exact_mod_cast (Nat.cast_le.mpr hG).trans (Nat.floor_le hnn)
    · push_neg at hnn
      have hfl : ⌊kThresholdWitness n - (n : ℝ)^(1 - ε/2)⌋₊ = 0 :=
        Nat.floor_eq_zero.mpr (by linarith)
      rw [hfl] at hG
      have hG0 : cochromaticNumber G = 0 := Nat.le_zero.mp hG
      -- threshold < 0 and ζ(G) ≤ 0 implies ζ(G) = 0, impossible for n ≥ 1
      -- (cochromaticNumber G = 0 iff there is a 0-coloring, which requires n = 0)
      have hG0 : cochromaticNumber G = 0 := Nat.le_zero.mp hG
      -- ζ(G) = 0 means 0 ∈ {k | CochromaticColoringExists G k}, i.e. ∃ π : Fin n → Fin 0
      -- But Fin 0 is empty and Fin n is nonempty (n ≥ 1), contradiction
      have hzero_mem : CochromaticColoringExists G 0 := by
        have hmem := Nat.sInf_mem (cochromaticColoringExists_card_self (G := G))
        have : cochromaticNumber G ∈ {k | CochromaticColoringExists G k} := hmem
        rw [hG0] at this; exact this
      obtain ⟨col, _⟩ := hzero_mem
      exact Fin.elim0 (col ⟨0, hn_pos⟩)
  -- gnHalf is monotone: gnHalf n {ζ ≤ threshold} ≥ gnHalf n {ζ ≤ k}
  have hgnHalf_mono : (gnHalf n {G : SimpleGraph (Fin n) | cochromaticNumber G ≤ k}).toReal ≤
      (gnHalf n {G | (cochromaticNumber G : ℝ) ≤ kThresholdWitness n - (n : ℝ)^(1 - ε / 2)}).toReal :=
    (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr
      (MeasureTheory.measure_mono hthresh_sub)
  -- Since gnHalf n {ζ ≤ k} = S.card * p, goal follows
  have hp_pos : 0 < p := by
    rw [show p = 1 / (Fintype.card (SimpleGraph (Fin n)) : ℝ) from by
      field_simp [hOmega_pos.ne']; linarith]
    positivity
  -- exp(-n^{0.99}) < S.card * p ← exp(-n^{0.99}) * |Ω| < S.card, multiply by p
  have hlt_Scard_p : Real.exp (-(n : ℝ)^(99/100:ℝ)) < (S.card : ℝ) * p := by
    have := mul_lt_mul_of_pos_right hScard_large hp_pos
    rw [mul_assoc, hOmega_p, mul_one] at this; exact this
  -- gnHalf n {ζ ≤ k} = S.card * p
  rw [← hgnHalf_eq] at hlt_Scard_p
  -- gnHalf n {ζ ≤ threshold} ≥ gnHalf n {ζ ≤ k}
  linarith

end PaleyZygmundLower

/-- **[THEOREM — ζ mean estimate]** (proved from Paley-Zygmund + Azuma)
  The expected cochromatic number of G(n,1/2) is at most kThresholdWitness(n) minus
  a power-of-n correction.

  **Proof** (reflexive Azuma argument):
  Let k* = kThresholdWitness n − n^{1−ε/2} and t = n^{0.999}.
  By `heckel_zeta_paley_zygmund`: P[ζ ≤ k*] > exp(−n^{0.99}) > 0 for large n.
  By `zeta_azuma_lower_tail_bound` (Azuma lower tail):
    P[ζ ≤ E[ζ] − t] ≤ exp(−t²/2n) = exp(−n^{0.998}/2).
  If E[ζ] > k* + t, then {ζ ≤ k*} ⊆ {ζ ≤ E[ζ] − t}, so
    exp(−n^{0.99}) < P[ζ ≤ k*] ≤ P[ζ ≤ E[ζ] − t] ≤ exp(−n^{0.998}/2).
  But exp(−n^{0.998}/2) < exp(−n^{0.99}) for large n (since n^{0.998}/2 > n^{0.99}
  for n ≥ n₀), contradiction. So E[ζ] ≤ k* + t = kThresholdWitness n − n^{1−ε/2} + n^{0.999}.

  **Axiom count**: 1 (heckel_zeta_paley_zygmund)
  **Sorry count**: 1 (zeta_azuma_lower_tail_bound)
-/
theorem heckel_zeta_mean_upper_bound (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
      ∫ G : SimpleGraph (Fin n), (cochromaticNumber G : ℝ) ∂(gnHalf n) ≤
        kThresholdWitness n - (n : ℝ)^(1 - ε / 2) + (n : ℝ)^(999 / 1000 : ℝ) := by
  obtain ⟨n₀_pz, h_pz⟩ := heckel_zeta_paley_zygmund ε hε_pos hε_lt
  obtain ⟨n₀_lo, h_lo⟩ := zeta_azuma_lower_tail_bound
  -- exp(-n^{0.998}/2) < exp(-n^{0.99}) for large n: n^{0.998}/2 > n^{0.99}
  -- equivalently n^{0.998-0.99}/2 = n^{0.008}/2 → ∞
  have h_exp_compare : ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n → 0 < n →
      Real.exp (-((n : ℝ)^(998 / 1000 : ℝ)) / 2) < Real.exp (-(n : ℝ)^(99 / 100 : ℝ)) := by
    have : Filter.Tendsto (fun m : ℕ => (m : ℝ)^(8 / 1000 : ℝ) / 2)
        Filter.atTop Filter.atTop := by
      apply Filter.Tendsto.atTop_div_const (by norm_num)
      exact (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
    have hge2 : ∀ᶠ m : ℕ in Filter.atTop, 2 ≤ (m : ℝ)^(8 / 1000 : ℝ) / 2 :=
      (Filter.Tendsto.eventually_ge_atTop this 2)
    rw [Filter.eventually_atTop] at hge2
    obtain ⟨n₁, hn₁⟩ := hge2
    refine ⟨n₁, fun n hn hn_pos => ?_⟩
    apply Real.exp_lt_exp.mpr
    have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
    have h8 : 2 ≤ (n : ℝ)^(8 / 1000 : ℝ) / 2 := hn₁ n hn
    -- Goal: -(n^{998/1000})/2 < -(n^{99/100})
    -- i.e. n^{99/100} < n^{998/1000}/2 = n^{99/100} * n^{8/1000}/2
    rw [show (998 / 1000 : ℝ) = (99 / 100 : ℝ) + (8 / 1000 : ℝ) by norm_num,
        Real.rpow_add hn']
    have hpos99 := Real.rpow_pos_of_pos hn' (99 / 100 : ℝ)
    have hpos8 := Real.rpow_pos_of_pos hn' (8 / 1000 : ℝ)
    nlinarith
  obtain ⟨n₁, h_exp_cmp⟩ := h_exp_compare
  refine ⟨max (max n₀_pz n₀_lo) (max n₁ 1), fun n hn hrange => ?_⟩
  have hn_pz  : n₀_pz ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn_lo  : n₀_lo ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn_exp : n₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn_pos : 0 < n :=
    Nat.lt_of_lt_of_le Nat.one_pos (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn)
  haveI : IsProbabilityMeasure (gnHalf n) := by unfold gnHalf; infer_instance
  set μ_n : ℝ := ∫ G' : SimpleGraph (Fin n), (cochromaticNumber G' : ℝ) ∂(gnHalf n)
  set k_star : ℝ := kThresholdWitness n - (n : ℝ)^(1 - ε / 2)
  set t : ℝ := (n : ℝ)^(999 / 1000 : ℝ)
  -- We want: μ_n ≤ k_star + t
  by_contra h_contra
  push_neg at h_contra
  -- h_contra : k_star + t < μ_n
  have ht_nn : 0 ≤ t := Real.rpow_nonneg (Nat.cast_nonneg n) _
  -- Paley-Zygmund: P[ζ ≤ k_star] > exp(-n^{0.99})
  have h_pz_n := h_pz n hn_pz hrange hn_pos
  -- Azuma lower tail: P[ζ ≤ μ_n - t] ≤ exp(-t²/2n)
  have h_lo_n := h_lo n hn_pos t ht_nn
  -- Since k_star < μ_n - t, we have {ζ ≤ k_star} ⊆ {ζ ≤ μ_n - t}
  have h_sub : {G : SimpleGraph (Fin n) | (cochromaticNumber G : ℝ) ≤ k_star} ⊆
      {G : SimpleGraph (Fin n) |
        (cochromaticNumber G : ℝ) ≤
          μ_n - t} := by
    intro G hG
    simp only [Set.mem_setOf_eq] at hG ⊢
    linarith
  -- P[ζ ≤ k_star] ≤ P[ζ ≤ μ_n - t].toReal
  have h_meas_kstar : MeasurableSet {G : SimpleGraph (Fin n) | (cochromaticNumber G : ℝ) ≤ k_star} :=
    Set.Finite.measurableSet (Set.toFinite _)
  have h_meas_lo : MeasurableSet {G : SimpleGraph (Fin n) | (cochromaticNumber G : ℝ) ≤ μ_n - t} :=
    Set.Finite.measurableSet (Set.toFinite _)
  have h_mono : (gnHalf n {G : SimpleGraph (Fin n) | (cochromaticNumber G : ℝ) ≤ k_star}).toReal ≤
      (gnHalf n {G : SimpleGraph (Fin n) | (cochromaticNumber G : ℝ) ≤ μ_n - t}).toReal :=
    ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _) |>.mpr (measure_mono h_sub)
  -- P[ζ ≤ μ_n - t] = P[ζ ≤ μ_n - t] and the Azuma bound: this .toReal ≤ exp(-t²/2n)
  -- h_lo_n : (gnHalf n).real {ζ ≤ μ_n - t} ≤ exp(-t²/2n)
  -- But (gnHalf n).real = (gnHalf n ·).toReal by definition (Measure.real)
  have h_real_eq : (gnHalf n {G : SimpleGraph (Fin n) | (cochromaticNumber G : ℝ) ≤ μ_n - t}).toReal =
      (gnHalf n).real {G : SimpleGraph (Fin n) | (cochromaticNumber G : ℝ) ≤ μ_n - t} := by
    simp [Measure.real]
  -- Chain: exp(-n^{0.99}) < P[ζ ≤ k_star].toReal ≤ P[ζ ≤ μ_n-t].real ≤ exp(-t²/2n)
  have h_azuma_exp : (gnHalf n).real {G : SimpleGraph (Fin n) |
      (cochromaticNumber G : ℝ) ≤ μ_n - t} ≤
      Real.exp (-((n : ℝ)^(998 / 1000 : ℝ)) / 2) := by
    calc (gnHalf n).real {G | (cochromaticNumber G : ℝ) ≤ μ_n - t}
        ≤ Real.exp (-(t ^ 2) / (2 * (n : ℝ))) := h_lo_n
      _ = Real.exp (-((n : ℝ)^(998 / 1000 : ℝ)) / 2) := by
          congr 1
          have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
          have key : t ^ 2 = (n : ℝ)^(998 / 1000 : ℝ) * (n : ℝ) := by
            simp only [t]
            rw [← Real.rpow_natCast ((n : ℝ)^(999 / 1000 : ℝ)) 2,
                ← Real.rpow_mul (le_of_lt hn')]
            rw [show (999 / 1000 : ℝ) * ↑(2 : ℕ) = (998 / 1000 : ℝ) + 1 by norm_num,
                Real.rpow_add hn', Real.rpow_one]
          linarith [mul_comm ((n : ℝ)^(998 / 1000 : ℝ)) (n : ℝ),
                    show -(t ^ 2) / (2 * (n : ℝ)) = -((n : ℝ)^(998 / 1000 : ℝ)) / 2 by
                      rw [key]; field_simp]
  -- Contradiction: exp(-n^{0.99}) < P[ζ ≤ k_star].toReal ≤ exp(-t²/2n) < exp(-n^{0.99})
  have h_exp_lt := h_exp_cmp n hn_exp hn_pos
  linarith [h_mono, h_real_eq ▸ h_azuma_exp]

/-- The layer decomposition E[ζ] = Σ_{k=0}^{n-1} P[ζ > k] for the cochromatic number
  on the finite probability space (SimpleGraph (Fin n), gnHalf n).

  Proof:
  (1) `integral_fintype`: E[ζ] = ∑_G (gnHalf n).real {G} * ζ(G).
  (2) `ζ(G) ≤ n` (from `cochromatic_le_chromatic` + `chromaticNumber_le_card`), so
      `(ζ(G) : ℝ) = ∑ k ∈ Finset.range n, if k < ζ(G) then 1 else 0`
      (the indicator sum counts exactly ζ(G) ones).
  (3) Substitute into (1), pull out the constant `(gnHalf n).real {G}`:
      E[ζ] = ∑_G ∑_{k<n} (gnHalf n).real {G} * (if k < ζ(G) then 1 else 0).
  (4) `Finset.sum_comm`: swap to ∑_{k<n} ∑_G (gnHalf n).real {G} * (if k < ζ(G) then 1 else 0).
  (5) Inner sum = ∑_{G: k < ζ(G)} (gnHalf n).real {G}
      = (gnHalf n {G | k < ζ(G)}).toReal
      (finite union of singletons + `Measure.real` linearity). -/
private lemma zeta_layer_decomposition (n : ℕ) :
    ∫ G : SimpleGraph (Fin n), (cochromaticNumber G : ℝ) ∂(gnHalf n) =
      ∑ k ∈ Finset.range n,
        (gnHalf n {G : SimpleGraph (Fin n) | k < cochromaticNumber G}).toReal := by
  haveI : IsProbabilityMeasure (gnHalf n) := by unfold gnHalf; infer_instance
  -- Step 1: reduce integral to finite weighted sum via integral_fintype
  rw [MeasureTheory.integral_fintype Integrable.of_finite]
  simp only [smul_eq_mul]
  -- Step 2: for each G, rewrite ζ(G) as a sum of indicators over range n
  -- using ζ(G) ≤ n
  have hle : ∀ G : SimpleGraph (Fin n), cochromaticNumber G ≤ n := fun G => by
    have h1 : cochromaticNumber G ≤ chromaticNumber G := cochromatic_le_chromatic
    have h2 : chromaticNumber G ≤ n := by
      unfold chromaticNumber
      apply Nat.sInf_le
      use fun v => (⟨v.val, v.isLt⟩ : Fin n)
      intro u v hadj heq
      exact G.ne_of_adj hadj (Fin.ext (Fin.mk.inj heq))
    omega
  simp_rw [show ∀ G : SimpleGraph (Fin n), (cochromaticNumber G : ℝ) =
      ∑ k ∈ Finset.range n, if k < cochromaticNumber G then (1 : ℝ) else 0 from fun G => by
    rw [Finset.sum_boole]
    norm_cast
    rw [show (Finset.range n).filter (· < cochromaticNumber G) = Finset.range (cochromaticNumber G)
        from by
          ext k
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_range]
          constructor
          · rintro ⟨_, hk⟩; exact hk
          · intro hk; exact ⟨Nat.lt_of_lt_of_le hk (hle G), hk⟩]
    simp [Finset.card_range]]
  -- Step 3: distribute the constant weight p_G over the indicator sum
  simp_rw [Finset.mul_sum]
  -- Step 4: swap the two finite sums
  rw [Finset.sum_comm]
  -- Step 5: simplify each inner sum to (gnHalf n {G | k < ζ(G)}).toReal
  congr 1; ext k
  simp only [mul_ite, mul_one, mul_zero]
  -- ∑_G (if k < ζ(G) then p_G else 0) = (gnHalf n {G | k < ζ(G)}).toReal
  rw [show (gnHalf n {G : SimpleGraph (Fin n) | k < cochromaticNumber G}).toReal =
      ∑ G : SimpleGraph (Fin n), if k < cochromaticNumber G then
        (gnHalf n {G}).toReal else 0 from by
    have hset : (gnHalf n {G : SimpleGraph (Fin n) | k < cochromaticNumber G}) =
        ∑ G ∈ Finset.univ.filter (fun G => k < cochromaticNumber G), gnHalf n {G} := by
      conv_rhs => rw [show Finset.univ.filter (fun G : SimpleGraph (Fin n) => k < cochromaticNumber G) =
          ({G : SimpleGraph (Fin n) | k < cochromaticNumber G} : Finset _) from by
        simp]
      rw [sum_measure_singleton]
      congr 1
      simp [Set.ext_iff, Finset.mem_coe]
    rw [hset, ENNReal.toReal_sum (fun G _ => measure_ne_top _ _), Finset.sum_filter]]
  simp only [Measure.real_def]



/-! ## Exponential Decay Lemma (proved) -/

section ExpDecay

/-- **Exponential decay** (proved)

  For any ε > 0, eventually exp(−n^{0.998}/2) ≤ ε.

  **Proof**: n^{0.998} → +∞ (by `tendsto_rpow_atTop`), so exp(−n^{0.998}/2) → 0.
  Extracts n₀ via `Metric.tendsto_atTop`.

  **Status**: PROVED (0 sorry).
-/
private lemma zeta_exp_decay_eventually_le (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 0 < n →
      Real.exp (-((n : ℝ) ^ (999 / 1000 : ℝ)) ^ 2 / (2 * (n : ℝ))) ≤ ε := by
  -- Key: exp(-n^(999/1000)^2/(2n)) = exp(-n^(998/1000)/2) → 0 ≤ ε eventually.
  -- Step 1: n^(998/1000) → +∞
  have h_rpow_atTop : Filter.Tendsto
      (fun m : ℕ => (m : ℝ) ^ (998 / 1000 : ℝ)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  -- Step 2: -n^(998/1000)/2 → -∞ (negate + divide by positive constant)
  have h_neg : Filter.Tendsto (fun m : ℕ => -((m : ℝ) ^ (998 / 1000 : ℝ)))
      Filter.atTop Filter.atBot := by
    rw [Filter.tendsto_atBot]
    intro b
    filter_upwards [Filter.tendsto_atTop.mp h_rpow_atTop (-b)] with m hm
    linarith
  have h_atBot : Filter.Tendsto
      (fun m : ℕ => -((m : ℝ) ^ (998 / 1000 : ℝ)) / 2) Filter.atTop Filter.atBot :=
    h_neg.atBot_div_const (by norm_num)
  -- Step 3: exp(-n^(998/1000)/2) → 0
  have h_tendsto_zero : Filter.Tendsto
      (fun m : ℕ => Real.exp (-((m : ℝ) ^ (998 / 1000 : ℝ)) / 2))
      Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp h_atBot
  -- Step 4: extract n₀
  rw [Metric.tendsto_atTop] at h_tendsto_zero
  obtain ⟨n₀, hn₀⟩ := h_tendsto_zero (ε / 2) (by linarith)
  refine ⟨max n₀ 1, fun n hn hn_pos => ?_⟩
  -- Algebraic identity: -((n^a)^2)/(2n) = -n^(998/1000)/2  (a = 999/1000)
  have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  have key : ((n : ℝ) ^ (999 / 1000 : ℝ)) ^ 2 = (n : ℝ) ^ (998 / 1000 : ℝ) * (n : ℝ) := by
    rw [← Real.rpow_natCast ((n : ℝ) ^ (999 / 1000 : ℝ)) 2, ← Real.rpow_mul (le_of_lt hn')]
    rw [show (999 / 1000 : ℝ) * ↑(2 : ℕ) = (998 / 1000 : ℝ) + 1 by norm_num,
        Real.rpow_add hn', Real.rpow_one]
  have h_alg : -((n : ℝ) ^ (999 / 1000 : ℝ)) ^ 2 / (2 * (n : ℝ)) =
      -((n : ℝ) ^ (998 / 1000 : ℝ)) / 2 := by rw [key]; field_simp
  rw [h_alg]
  -- Extract the bound from the tendsto
  have h_dist := hn₀ n (le_trans (le_max_left _ _) hn)
  rw [Real.dist_eq] at h_dist
  linarith [abs_le.mp (le_of_lt h_dist), Real.exp_nonneg (-((n : ℝ) ^ (998 / 1000 : ℝ)) / 2)]

end ExpDecay

/-! ## Main Theorem: heckel_zeta_upper_bound (proved from mean + Azuma) -/

section ZetaUpperBound

/-- **ζ upper bound (proved from mean axiom + Azuma concentration)**

  For ε ∈ (0,1) in the main range, with probability ≥ 1 − ε:
    ζ(G(n,1/2)) ≤ kThresholdWitness(n) − n^{1−ε/2} + 2·n^{0.999}

  **Proof structure**:
  1. Mean bound (proved theorem `heckel_zeta_mean_upper_bound`, 0 sorry):
       𝔼[ζ] ≤ M := kThresholdWitness n − n^{1−ε/2} + n^{0.999}
  2. Azuma tail (`zeta_azuma_tail_bound`, proved):
       P[ζ ≥ 𝔼[ζ] + t] ≤ exp(−t²/2n)   for t = n^{0.999}
  3. Since 𝔼[ζ] ≤ M, we have {ζ > M + t} ⊆ {ζ ≥ 𝔼[ζ] + t}, so
       P[ζ > M + t] ≤ exp(−(n^{0.999})²/2n) = exp(−n^{0.998}/2)
  4. exp decay (`zeta_exp_decay_eventually_le`, proved):
       exp(−n^{0.998}/2) ≤ ε for n ≥ n₀(ε)
  5. Therefore P[ζ ≤ M + t] = P[ζ ≤ kThresholdWitness n − n^{1−ε/2} + 2n^{0.999}] ≥ 1 − ε.

  **Axiom count**: 1 (heckel_cochromatic_second_moment, via heckel_zeta_paley_zygmund → heckel_zeta_mean_upper_bound)
  **Sorry count**: 0 (zeta_azuma_tail_bound and zeta_exp_decay_eventually_le are both proved)
-/
theorem heckel_zeta_upper_bound (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
      1 - ENNReal.ofReal ε ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          (cochromaticNumber G : ℝ) ≤
            kThresholdWitness n - (n : ℝ)^(1 - ε / 2) + 2 * (n : ℝ)^(999 / 1000 : ℝ)} := by
  -- Step 1: obtain the mean bound
  obtain ⟨n₀_mean, h_mean⟩ := heckel_zeta_mean_upper_bound ε hε_pos hε_lt
  -- Step 2: obtain the exp decay bound
  obtain ⟨n₁_exp, h_exp⟩ := zeta_exp_decay_eventually_le ε hε_pos
  -- Need n ≥ 1 for Azuma; take n₂ = 1 as a lower bound
  refine ⟨max (max n₀_mean n₁_exp) 1, fun n hn hrange => ?_⟩
  have hn_mean : n₀_mean ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn_exp  : n₁_exp  ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn_pos  : 0 < n   := Nat.lt_of_lt_of_le Nat.one_pos
                              (le_trans (le_max_right _ _) hn)
  -- IsProbabilityMeasure instance for gnHalf n
  haveI : IsProbabilityMeasure (gnHalf n) := by unfold gnHalf; infer_instance
  -- Let μ_n = E[ζ], M = mean upper bound, t = n^{0.999}
  set μ_n : ℝ := ∫ G' : SimpleGraph (Fin n), (cochromaticNumber G' : ℝ) ∂(gnHalf n)
  set M   : ℝ := kThresholdWitness n - (n : ℝ)^(1 - ε / 2) + (n : ℝ)^(999 / 1000 : ℝ)
  set t   : ℝ := (n : ℝ)^(999 / 1000 : ℝ)
  -- Observe that M + t = the target upper bound
  have h_Mt : M + t =
      kThresholdWitness n - (n : ℝ)^(1 - ε / 2) + 2 * (n : ℝ)^(999 / 1000 : ℝ) := by
    simp only [M, t]; ring
  -- The mean bound: μ_n ≤ M
  have h_mu_le : μ_n ≤ M := h_mean n hn_mean hrange
  -- t ≥ 0 (n^{0.999} ≥ 0)
  have ht_nn : 0 ≤ t := Real.rpow_nonneg (Nat.cast_nonneg n) _
  -- Azuma: P[ζ(G) ≥ μ_n + t] ≤ exp(−t²/2n) ≤ ε
  have h_tail_real :
      (gnHalf n).real {G : SimpleGraph (Fin n) | μ_n + t ≤ (cochromaticNumber G : ℝ)} ≤ ε := by
    have h_az := zeta_azuma_tail_bound n hn_pos t ht_nn
    -- h_exp gives: exp(-t²/2n) ≤ ε (since t = n^{999/1000})
    have h_ed : Real.exp (-(t ^ 2) / (2 * (n : ℝ))) ≤ ε := by
      simp only [t]
      exact h_exp n hn_exp hn_pos
    exact le_trans h_az h_ed
  -- Convert to ENNReal: gnHalf n {ζ ≥ μ_n + t} ≤ ENNReal.ofReal ε
  have hmeas_tail : MeasurableSet
      {G : SimpleGraph (Fin n) | μ_n + t ≤ (cochromaticNumber G : ℝ)} :=
    Set.Finite.measurableSet (Set.toFinite _)
  have h_tail_ennreal :
      gnHalf n {G : SimpleGraph (Fin n) | μ_n + t ≤ (cochromaticNumber G : ℝ)} ≤
        ENNReal.ofReal ε := by
    calc gnHalf n {G | μ_n + t ≤ (cochromaticNumber G : ℝ)}
        = ENNReal.ofReal
            (gnHalf n {G | μ_n + t ≤ (cochromaticNumber G : ℝ)}).toReal := by
              rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
      _ ≤ ENNReal.ofReal ε :=
              ENNReal.ofReal_le_ofReal h_tail_real
  -- Monotonicity: {ζ > M + t} ⊆ {ζ ≥ μ_n + t}  (since μ_n ≤ M → M+t ≥ μ_n+t)
  have h_sub :
      {G : SimpleGraph (Fin n) | M + t < (cochromaticNumber G : ℝ)} ⊆
      {G : SimpleGraph (Fin n) | μ_n + t ≤ (cochromaticNumber G : ℝ)} := by
    intro G hG
    simp only [Set.mem_setOf_eq] at hG ⊢
    linarith
  -- Therefore gnHalf n {ζ > M+t} ≤ ENNReal.ofReal ε
  have hmeas_bad : MeasurableSet
      {G : SimpleGraph (Fin n) | M + t < (cochromaticNumber G : ℝ)} :=
    Set.Finite.measurableSet (Set.toFinite _)
  have h_bad_le :
      gnHalf n {G : SimpleGraph (Fin n) | M + t < (cochromaticNumber G : ℝ)} ≤
        ENNReal.ofReal ε :=
    le_trans (measure_mono h_sub) h_tail_ennreal
  -- Good event: {ζ ≤ M+t}; bad event: {ζ > M+t} = {ζ ≤ M+t}ᶜ
  have hmeas_good : MeasurableSet
      {G : SimpleGraph (Fin n) | (cochromaticNumber G : ℝ) ≤ M + t} :=
    Set.Finite.measurableSet (Set.toFinite _)
  have h_compl_eq :
      {G : SimpleGraph (Fin n) | M + t < (cochromaticNumber G : ℝ)} =
      {G : SimpleGraph (Fin n) | (cochromaticNumber G : ℝ) ≤ M + t}ᶜ := by
    ext G; simp [Set.mem_compl_iff, not_le]
  -- 1 − ENNReal.ofReal ε ≤ gnHalf n {ζ ≤ M+t}
  have h_good_prob :
      1 - ENNReal.ofReal ε ≤
        gnHalf n {G : SimpleGraph (Fin n) | (cochromaticNumber G : ℝ) ≤ M + t} := by
    have hε_le : ENNReal.ofReal ε ≤ 1 :=
      ENNReal.ofReal_le_one.mpr (le_of_lt hε_lt)
    calc 1 - ENNReal.ofReal ε
        ≤ 1 - gnHalf n {G | M + t < (cochromaticNumber G : ℝ)} :=
            tsub_le_tsub_left h_bad_le 1
      _ = gnHalf n {G : SimpleGraph (Fin n) | (cochromaticNumber G : ℝ) ≤ M + t} := by
            rw [h_compl_eq, prob_compl_eq_one_sub hmeas_good]
            exact ENNReal.sub_sub_cancel one_ne_top prob_le_one
  -- Rewrite M + t back to the target formula
  rw [← h_Mt]
  exact h_good_prob

end ZetaUpperBound

end Problem625
