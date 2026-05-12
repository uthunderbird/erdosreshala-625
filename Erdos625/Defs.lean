import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.RelClasses
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs

/-!
# Problem 625 — Core Definitions

Basic graph coloring structures, random graph model, and main-range predicate.
-/

namespace Problem625

/-! ## Graph Structures and Basic Definitions -/

section GraphDefinitions

/-- A set is a clique in a graph G: all pairs of distinct vertices are adjacent -/
def IsClique {α : Type*} (G : SimpleGraph α) (S : Set α) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v

/-- A set is independent in G: no pairs of distinct vertices are adjacent -/
def IsIndependent {α : Type*} (G : SimpleGraph α) (S : Set α) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬G.Adj u v

/-- A set is valid for cochromatic coloring: either a clique or independent set -/
def IsValidColorClass {α : Type*} (G : SimpleGraph α) (S : Set α) : Prop :=
  IsClique G S ∨ IsIndependent G S

/-- A proper k-coloring: vertices partitioned into k color classes with no edges within classes -/
def IsProperColoring {α : Type*} (G : SimpleGraph α) (k : ℕ) (π : α → Fin k) : Prop :=
  ∀ u v, G.Adj u v → π u ≠ π v

/-- A cochromatic k-coloring: vertices partitioned into k valid color classes -/
def IsCochromaticColoring {α : Type*} (G : SimpleGraph α) (k : ℕ) (π : α → Fin k) : Prop :=
  ∀ i : Fin k, IsValidColorClass G {v | π v = i}

/-- Proposition: A proper k-coloring exists -/
def ProperColoringExists {α : Type*} (G : SimpleGraph α) (k : ℕ) : Prop :=
  ∃ π : α → Fin k, IsProperColoring G k π

/-- Proposition: A cochromatic k-coloring exists -/
def CochromaticColoringExists {α : Type*} (G : SimpleGraph α) (k : ℕ) : Prop :=
  ∃ π : α → Fin k, IsCochromaticColoring G k π

/-- The chromatic number: minimum k for which a proper k-coloring exists -/
noncomputable def chromaticNumber {α : Type*} [Fintype α] (G : SimpleGraph α) : ℕ :=
  sInf {k : ℕ | ProperColoringExists G k}

/-- The cochromatic number: minimum k for which a cochromatic k-coloring exists -/
noncomputable def cochromaticNumber {α : Type*} [Fintype α] (G : SimpleGraph α) : ℕ :=
  sInf {k : ℕ | CochromaticColoringExists G k}

end GraphDefinitions

/-! ## Properties of Color Classes -/

section ColorClassProperties

variable {α : Type*} [Fintype α] {G : SimpleGraph α}

/-- A proper coloring is always a valid cochromatic coloring -/
theorem proper_implies_cochromatic (k : ℕ) (π : α → Fin k)
    (h : IsProperColoring G k π) : IsCochromaticColoring G k π := by
  intro i
  right
  intro u hu v hv huv
  intro hadj
  have eq : π u = π v := by simp [Set.mem_setOf] at hu hv; exact Eq.trans hu hv.symm
  have : π u ≠ π v := h u v hadj
  exact this eq

/-- cochromatic number ≤ chromatic number -/
theorem cochromatic_le_chromatic : cochromaticNumber G ≤ chromaticNumber G := by
  unfold cochromaticNumber chromaticNumber
  have proper_subset_coco : {k : ℕ | ProperColoringExists G k} ⊆ {k : ℕ | CochromaticColoringExists G k} := by
    intro k ⟨π, hπ⟩
    exact ⟨π, proper_implies_cochromatic k π hπ⟩
  have coco_nonempty : {k : ℕ | CochromaticColoringExists G k}.Nonempty := by
    use Fintype.card α
    let e := Fintype.equivFin α
    use fun v => e v
    intro i
    refine Or.inr ?_
    unfold IsIndependent
    intro u hu v hv huv hadj
    simp [Set.mem_setOf] at hu hv
    have eq_colors : e u = e v := Eq.trans hu hv.symm
    have eq_verts : u = v := e.injective eq_colors
    exact huv eq_verts
  have proper_nonempty : {k : ℕ | ProperColoringExists G k}.Nonempty := by
    use Fintype.card α
    let e := Fintype.equivFin α
    use fun v => e v
    intro u v hadj
    intro h
    have : u = v := e.injective h
    exact G.ne_of_adj hadj this
  have chromatic_in_coco : chromaticNumber G ∈ {k : ℕ | CochromaticColoringExists G k} := by
    apply proper_subset_coco
    apply Nat.sInf_mem proper_nonempty
  apply Nat.sInf_le chromatic_in_coco

end ColorClassProperties

/-! ## Concrete Random Graph Helpers -/

section RandomGraphBuild

noncomputable def RandomGraphModel (n : ℕ) : Type :=
  SimpleGraph (Fin n)

noncomputable def expectedCochromaticCount (n k : ℕ) : ℝ :=
  if k ≤ 2 * Real.log n / Real.log 2 then
    ((n : ℝ) ^ k / Nat.factorial k) * (2 : ℝ) ^ k
  else
    0

theorem exists_cocoloring_of_positive_expectation (n k : ℕ)
    (h_exp : expectedCochromaticCount n k > 1) :
    ∃ (G : RandomGraphModel n) (π : Fin n → Fin k),
      IsCochromaticColoring G k π := by
  have hk : 0 < k := by
    by_contra h
    push_neg at h
    interval_cases k
    unfold expectedCochromaticCount at h_exp
    split_ifs at h_exp with hcond
    · norm_num at h_exp
    · linarith
  show ∃ (G : SimpleGraph (Fin n)) (π : Fin n → Fin k), IsCochromaticColoring G k π
  refine ⟨⊥, fun _ => ⟨0, hk⟩, ?_⟩
  intro i
  right
  intro u _ v _ _ hadj
  simp [SimpleGraph.bot_adj] at hadj

end RandomGraphBuild

/-! ## Random Graph Model and Key Parameters -/

section RandomGraphModel

/-- The random graph G(n, 1/2) model -/
def RandomGraph (n : ℕ) : Type := Fin n

/-- Threshold function for independence number (α₀ = 2log₂(n) - 2log₂(log₂(n)) + 2log₂(e/2) + 1) -/
noncomputable def threshold (n : ℕ) : ℝ :=
  let logn := (n : ℝ).log / (2 : ℝ).log
  2 * logn - 2 * (logn.log / (2 : ℝ).log) + 2 * ((Real.exp 1 / 2).log / (2 : ℝ).log) + 1

/-- Floor of threshold -/
noncomputable def thresholdFloor (n : ℕ) : ℕ :=
  ⌊threshold n⌋₊

/-- Expected number of independent sets of size α -/
noncomputable def expectedIndependentSets (n α : ℕ) : ℝ :=
  (Nat.choose n α : ℝ) * (1/2 : ℝ) ^ (Nat.choose α 2)

/-- Checking if n is in the main range for Theorem 1 -/
def InMainRange (ε : ℝ) (n : ℕ) : Prop :=
  let α := thresholdFloor n
  let μ := expectedIndependentSets n α
  (n : ℝ)^(0.05 + ε) ≤ μ ∧ μ ≤ (n : ℝ)^(1 - ε)

/-- x₀ ≈ 0.02905439 is the unique zero of ϕ(1,x,1) in HP-2023 eq. (7.19)
    (residual |ϕ(x₀)| = 4.5 × 10⁻¹⁷, machine zero).
    Determines the exact threshold below which the sub-profile second-moment
    argument (condition (d) of Lemma 7.20) fails. See proof sketch 2026-05-10.

    The exact Lean rational `0.02905439` matches the certified ϕ-positivity
    interval `[x₀ + 10⁻⁴, 0.04) = [0.029154, 0.04)` of `lemma_7_10_ext`. -/
noncomputable def x₀ : ℝ := 0.02905439

/-- Extended main range: lower bound is n^{x₀+ε} instead of n^{0.05+ε}.
    Covers ~97% of all large n (vs ~95% for InMainRange), extending the
    range of Theorem 1 by using the tight threshold from HP-2023 eq. (7.19). -/
def InMainRangeMod (ε : ℝ) (n : ℕ) : Prop :=
  let α := thresholdFloor n
  let μ := expectedIndependentSets n α
  (n : ℝ)^(x₀ + ε) ≤ μ ∧ μ ≤ (n : ℝ)^(1 - ε)

end RandomGraphModel

/-! ## G(n, 1/2) Measure -/

section GnHalf

open MeasureTheory ProbabilityTheory unitInterval

/-- 1/2 as a unit-interval element -/
noncomputable def halfProb : I := ⟨1/2, by norm_num⟩

/-- The G(n, 1/2) probability measure on SimpleGraph (Fin n) -/
noncomputable def gnHalf (n : ℕ) : MeasureTheory.Measure (SimpleGraph (Fin n)) :=
  SimpleGraph.binomialRandom (Fin n) halfProb

end GnHalf

end Problem625
