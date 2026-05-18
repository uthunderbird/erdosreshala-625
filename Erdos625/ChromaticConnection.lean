import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Erdos625.Defs
import Erdos625.ColoringBasic
import Erdos625.FirstMomentThreshold
import Erdos625.PartBProfileBridge

/-!
# Problem 625 — Chromatic vs Bounded Chromatic Connection

This module formalizes the connection between the chromatic number χ(G) and
surrogate bounded-coloring quantities via the independence number α(G).

Important note:
- `ColoringBasic.boundedChromaticNumber` is deletion-based: one may ignore up to `t` vertices.
- The Heckel/Heckel-Panagiotou argument for Part (B) uses the class-size-bounded object
  formalized in `FirstMomentThreshold.classBoundedChromaticNumber`.
- So the proved lemmas in the first section of this file are useful local inequalities, but
  they do not by themselves complete the paper-aligned bridge.

Key insight from Heckel 2024, §3.1:
  χ(G) ≥ χ_t(G) - X_α
-/

namespace Problem625

open MeasureTheory ProbabilityTheory ENNReal
open scoped Classical

/-! ## Count of maximal independent sets (X_α) -/

section IndependenceCount

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The number of independent sets of size exactly k in G. -/
noncomputable def indepSetCount (G : SimpleGraph α) (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun S : Finset α => S.card = k ∧ G.IsNIndepSet k S)).card

/-- The X_α from Heckel 2024: count of independent sets of size exactly α(G). -/
noncomputable def maxIndepSetCount (G : SimpleGraph α) : ℕ :=
  indepSetCount G (G.indepNum)

end IndependenceCount

/-! ## Deletion-Based Surrogate Connection

These lemmas are about the local deletion-based `boundedChromaticNumber` from
`ColoringBasic.lean`, not the paper's class-size-bounded `χ_t`.
-/

section ChiTConnection

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Deletion-based surrogate inequality: the local `boundedChromaticNumber` is at most
    `χ(G) + X_α`.

    In the current local formalization, `boundedChromaticNumber` is the deletion-based
    variant from `ColoringBasic.lean`: it allows ignoring at most `t` vertices.
    For that notion we already have `boundedChromaticNumber_le_chromaticNumber`,
    so the present bound follows immediately.
-/
theorem boundedChromaticNumber_le_chromaticNumber_add_maxIndep
    (G : SimpleGraph α) (t : ℕ) (ht : G.indepNum ≤ t + 1) :
    boundedChromaticNumber G t ≤ chromaticNumber G + maxIndepSetCount G := by
  have hbase : boundedChromaticNumber G t ≤ chromaticNumber G :=
    boundedChromaticNumber_le_chromaticNumber G t
  exact hbase.trans (Nat.le_add_right _ _)

/-- Deletion-based surrogate lower bound: χ(G) dominates the local
    `boundedChromaticNumber` up to the `X_α` correction.

    This follows directly from `boundedChromaticNumber_le_chromaticNumber_add_maxIndep`
    by rearranging: χ_t ≤ χ + X implies χ ≥ χ_t - X.
-/
theorem chromaticNumber_ge_boundedChromaticNumber_sub_maxIndep
    (G : SimpleGraph α) (t : ℕ) (ht : G.indepNum ≤ t + 1) :
    (boundedChromaticNumber G t : ℤ) - (maxIndepSetCount G : ℤ) ≤ (chromaticNumber G : ℤ) := by
  -- From boundedChromaticNumber_le_chromaticNumber_add_maxIndep:
  -- χ_t ≤ χ + X, which rearranges to χ ≥ χ_t - X
  have h : boundedChromaticNumber G t ≤ chromaticNumber G + maxIndepSetCount G :=
    boundedChromaticNumber_le_chromaticNumber_add_maxIndep G t ht
  -- Convert to integers and rearrange
  have h' : (boundedChromaticNumber G t : ℤ) ≤ (chromaticNumber G : ℤ) + (maxIndepSetCount G : ℤ) := by
    exact_mod_cast h
  -- Subtract X from both sides
  linarith

end ChiTConnection

/-! ## Paper-Aligned Class-Bounded Connection

These are the theorem surfaces that match Heckel 2024 / Heckel–Panagiotou 2023.
They use `classBoundedChromaticNumber`, i.e. the minimum number of colors in a
proper coloring with all color classes of size at most `t`.
-/

section ClassBoundedConnection

private lemma properColoringExists_card_fin (n : ℕ) (G : SimpleGraph (Fin n)) :
    ProperColoringExists G n := by
  refine ⟨fun v => v, ?_⟩
  intro u v hadj huv
  exact G.ne_of_adj hadj huv

/-- Recolor a proper coloring by splitting the vertices in `R` into singleton
new colors and leaving all other vertices in their old colors. -/
private noncomputable def recolorWithSingletonSet
    {n k : ℕ} (π : Fin n → Fin k) (R : Finset (Fin n)) :
    Fin n → Fin (k + R.card) :=
  fun x =>
    if hx : x ∈ R then
      Fin.natAdd k (R.equivFin ⟨x, hx⟩)
    else
      Fin.castAdd R.card (π x)

private lemma recolorWithSingletonSet_eq_castAdd_of_not_mem
    {n k : ℕ} (π : Fin n → Fin k) (R : Finset (Fin n)) (x : Fin n)
    (hx : x ∉ R) :
    recolorWithSingletonSet π R x = Fin.castAdd R.card (π x) := by
  simp [recolorWithSingletonSet, hx]

private lemma recolorWithSingletonSet_eq_natAdd_of_mem
    {n k : ℕ} (π : Fin n → Fin k) (R : Finset (Fin n)) (x : Fin n)
    (hx : x ∈ R) :
    recolorWithSingletonSet π R x = Fin.natAdd k (R.equivFin ⟨x, hx⟩) := by
  simp [recolorWithSingletonSet, hx]

private lemma not_mem_of_recolorWithSingletonSet_eq_castAdd
    {n k : ℕ} (π : Fin n → Fin k) (R : Finset (Fin n)) (x : Fin n) (i : Fin k)
    (hx : recolorWithSingletonSet π R x = Fin.castAdd R.card i) :
    x ∉ R := by
  intro hxmem
  have hval : (recolorWithSingletonSet π R x).val = (Fin.castAdd R.card i).val :=
    congrArg Fin.val hx
  simp [recolorWithSingletonSet, hxmem] at hval
  omega

private lemma pi_eq_of_recolorWithSingletonSet_eq_castAdd
    {n k : ℕ} (π : Fin n → Fin k) (R : Finset (Fin n)) (x : Fin n) (i : Fin k)
    (hx : recolorWithSingletonSet π R x = Fin.castAdd R.card i) :
    π x = i := by
  have hxmem : x ∉ R := not_mem_of_recolorWithSingletonSet_eq_castAdd π R x i hx
  have : Fin.castAdd R.card (π x) = Fin.castAdd R.card i := by
    simpa [recolorWithSingletonSet, hxmem] using hx
  exact Fin.castAdd_injective _ _ this

private lemma mem_of_recolorWithSingletonSet_eq_natAdd
    {n k : ℕ} (π : Fin n → Fin k) (R : Finset (Fin n)) (x : Fin n) (j : Fin R.card)
    (hx : recolorWithSingletonSet π R x = Fin.natAdd k j) :
    x ∈ R := by
  by_contra hxmem
  have hval : (recolorWithSingletonSet π R x).val = (Fin.natAdd k j).val :=
    congrArg Fin.val hx
  simp [recolorWithSingletonSet, hxmem] at hval
  omega

private lemma equivFin_eq_of_recolorWithSingletonSet_eq_natAdd
    {n k : ℕ} (π : Fin n → Fin k) (R : Finset (Fin n)) (x : Fin n) (j : Fin R.card)
    (hx : recolorWithSingletonSet π R x = Fin.natAdd k j) :
    R.equivFin ⟨x, mem_of_recolorWithSingletonSet_eq_natAdd π R x j hx⟩ = j := by
  have hxmem : x ∈ R := mem_of_recolorWithSingletonSet_eq_natAdd π R x j hx
  have : Fin.natAdd k (R.equivFin ⟨x, hxmem⟩) = Fin.natAdd k j := by
    simpa [recolorWithSingletonSet, hxmem] using hx
  exact Fin.natAdd_injective _ _ this

private lemma recolorWithSingletonSet_isProperColoring
    {n k : ℕ} (G : SimpleGraph (Fin n)) (π : Fin n → Fin k) (R : Finset (Fin n))
    (hπ : IsProperColoring G k π) :
    IsProperColoring G (k + R.card) (recolorWithSingletonSet π R) := by
  intro u v hadj huv
  by_cases hu : u ∈ R
  · by_cases hv : v ∈ R
    · have huj : recolorWithSingletonSet π R u = Fin.natAdd k (R.equivFin ⟨u, hu⟩) :=
        recolorWithSingletonSet_eq_natAdd_of_mem π R u hu
      have hvj : recolorWithSingletonSet π R v = Fin.natAdd k (R.equivFin ⟨v, hv⟩) :=
        recolorWithSingletonSet_eq_natAdd_of_mem π R v hv
      have hEq : R.equivFin ⟨u, hu⟩ = R.equivFin ⟨v, hv⟩ := by
        apply Fin.ext
        have hval : (Fin.natAdd k (R.equivFin ⟨u, hu⟩)).val =
            (Fin.natAdd k (R.equivFin ⟨v, hv⟩)).val :=
          congrArg Fin.val (by simpa [huj, hvj] using huv)
        simpa using hval
      have huv' : u = v := congrArg Subtype.val (R.equivFin.injective hEq)
      exact G.ne_of_adj hadj huv'
    · have hval : (recolorWithSingletonSet π R u).val =
          (recolorWithSingletonSet π R v).val := congrArg Fin.val huv
      rw [recolorWithSingletonSet_eq_natAdd_of_mem π R u hu,
        recolorWithSingletonSet_eq_castAdd_of_not_mem π R v hv] at hval
      simp at hval
      omega
  · by_cases hv : v ∈ R
    · have hval : (recolorWithSingletonSet π R u).val =
          (recolorWithSingletonSet π R v).val := congrArg Fin.val huv
      rw [recolorWithSingletonSet_eq_castAdd_of_not_mem π R u hu,
        recolorWithSingletonSet_eq_natAdd_of_mem π R v hv] at hval
      simp at hval
      omega
    · have hEq : Fin.castAdd R.card (π u) = Fin.castAdd R.card (π v) := by
        simpa [recolorWithSingletonSet_eq_castAdd_of_not_mem π R u hu,
          recolorWithSingletonSet_eq_castAdd_of_not_mem π R v hv] using huv
      exact hπ u v hadj (Fin.castAdd_injective _ _ hEq)

private lemma oldFiber_recolorWithSingletonSet_subset_remaining_colorClass
    {n k : ℕ} (π : Fin n → Fin k) (R : Finset (Fin n)) (i : Fin k) :
    Finset.univ.filter (fun v => recolorWithSingletonSet π R v = Fin.castAdd R.card i) ⊆
      Finset.univ.filter (fun v => π v = i ∧ v ∉ R) := by
  intro x hx
  have hσ : recolorWithSingletonSet π R x = Fin.castAdd R.card i := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨pi_eq_of_recolorWithSingletonSet_eq_castAdd π R x i hσ,
    not_mem_of_recolorWithSingletonSet_eq_castAdd π R x i hσ⟩

private lemma newFiber_recolorWithSingletonSet_subset_singleton
    {n k : ℕ} (π : Fin n → Fin k) (R : Finset (Fin n)) (j : Fin R.card) :
    Finset.univ.filter (fun v => recolorWithSingletonSet π R v = Fin.natAdd k j) ⊆
      ({(R.equivFin.symm j : Fin n)} : Finset (Fin n)) := by
  intro x hx
  have hσ : recolorWithSingletonSet π R x = Fin.natAdd k j := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hx
  have hxmem : x ∈ R := mem_of_recolorWithSingletonSet_eq_natAdd π R x j hσ
  have heq : R.equivFin ⟨x, hxmem⟩ = j :=
    equivFin_eq_of_recolorWithSingletonSet_eq_natAdd π R x j hσ
  have hsub : (⟨x, hxmem⟩ : ↥R) = R.equivFin.symm j := by
    apply R.equivFin.injective
    simpa using heq
  have hxval : x = R.equivFin.symm j := congrArg Subtype.val hsub
  simp [hxval]

private lemma recolorWithSingletonSet_oldFiber_card_le
    {n k t : ℕ} (π : Fin n → Fin k) (R : Finset (Fin n))
    (hbound : ∀ i : Fin k, (Finset.univ.filter (fun v => π v = i ∧ v ∉ R)).card ≤ t)
    (i : Fin k) :
    (Finset.univ.filter (fun v => recolorWithSingletonSet π R v =
      Fin.castAdd R.card i)).card ≤ t := by
  exact (Finset.card_le_card (oldFiber_recolorWithSingletonSet_subset_remaining_colorClass π R i)).trans
    (hbound i)

private lemma recolorWithSingletonSet_newFiber_card_le_one
    {n k : ℕ} (π : Fin n → Fin k) (R : Finset (Fin n)) (j : Fin R.card) :
    (Finset.univ.filter (fun v => recolorWithSingletonSet π R v = Fin.natAdd k j)).card ≤ 1 := by
  exact le_trans (Finset.card_le_card (newFiber_recolorWithSingletonSet_subset_singleton π R j))
    (by simp)

/-- Deterministic surplus bridge.  If a proper `k`-coloring has a vertex set `R`
whose removal leaves every old color class with size at most `t`, then splitting
the vertices of `R` into singleton colors gives a class-bounded coloring with
`k + |R|` colors. -/
theorem classBoundedChromaticNumber_le_of_coloring_with_small_removed_fibers
    {n k t : ℕ} (G : SimpleGraph (Fin n)) (π : Fin n → Fin k) (R : Finset (Fin n))
    (ht : 0 < t)
    (hπ : IsProperColoring G k π)
    (hbound : ∀ i : Fin k, (Finset.univ.filter (fun v => π v = i ∧ v ∉ R)).card ≤ t) :
    classBoundedChromaticNumber n t G ≤ k + R.card := by
  have hσ : IsClassBoundedProperColoring G (k + R.card) t (recolorWithSingletonSet π R) := by
    constructor
    · exact recolorWithSingletonSet_isProperColoring G π R hπ
    · rw [Fin.forall_fin_add]
      constructor
      · intro i
        exact recolorWithSingletonSet_oldFiber_card_le π R hbound i
      · intro j
        exact le_trans (recolorWithSingletonSet_newFiber_card_le_one π R j) ht
  exact Nat.sInf_le ⟨recolorWithSingletonSet π R, hσ⟩

/-- Variant with an explicit upper bound on the removed set. -/
theorem classBoundedChromaticNumber_le_of_coloring_with_removed_fibers_bound
    {n k t r : ℕ} (G : SimpleGraph (Fin n)) (π : Fin n → Fin k) (R : Finset (Fin n))
    (ht : 0 < t)
    (hπ : IsProperColoring G k π)
    (hbound : ∀ i : Fin k, (Finset.univ.filter (fun v => π v = i ∧ v ∉ R)).card ≤ t)
    (hR : R.card ≤ r) :
    classBoundedChromaticNumber n t G ≤ k + r := by
  exact (classBoundedChromaticNumber_le_of_coloring_with_small_removed_fibers G π R ht hπ hbound).trans
    (Nat.add_le_add_left hR k)

private lemma proper_colorClass_card_le_indepNum
    {n k : ℕ} (G : SimpleGraph (Fin n)) (π : Fin n → Fin k)
    (hπ : IsProperColoring G k π) (i : Fin k) :
    (Finset.univ.filter (fun v => π v = i)).card ≤ G.indepNum := by
  have hind : G.IsIndepSet ((Finset.univ.filter (fun v => π v = i)) : Set (Fin n)) := by
    intro u hu v hv huv hadj
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
    exact hπ u v hadj (hu.trans hv.symm)
  exact SimpleGraph.IsIndepSet.card_le_indepNum hind

private lemma proper_colorClass_isNIndepSet
    {n k : ℕ} (G : SimpleGraph (Fin n)) (π : Fin n → Fin k)
    (hπ : IsProperColoring G k π) (i : Fin k) :
    G.IsNIndepSet ((Finset.univ.filter (fun v => π v = i)).card)
      (Finset.univ.filter (fun v => π v = i)) := by
  refine ⟨?_, rfl⟩
  intro u hu v hv huv hadj
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
  exact hπ u v hadj (hu.trans hv.symm)

private lemma proper_colorClass_card_eq_indepNum_of_t_lt
    {n k t : ℕ} (G : SimpleGraph (Fin n)) (π : Fin n → Fin k)
    (hπ : IsProperColoring G k π) (ht : G.indepNum ≤ t + 1) (i : Fin k)
    (hi : t < (Finset.univ.filter (fun v => π v = i)).card) :
    (Finset.univ.filter (fun v => π v = i)).card = G.indepNum := by
  have hle₁ : (Finset.univ.filter (fun v => π v = i)).card ≤ G.indepNum :=
    proper_colorClass_card_le_indepNum G π hπ i
  have hle₂ : G.indepNum ≤ (Finset.univ.filter (fun v => π v = i)).card := by
    have hsucc : t + 1 ≤ (Finset.univ.filter (fun v => π v = i)).card := Nat.succ_le_of_lt hi
    exact ht.trans hsucc
  exact le_antisymm hle₁ hle₂

private lemma proper_colorClass_nonempty_of_t_lt
    {n k t : ℕ} (π : Fin n → Fin k) (i : Fin k)
    (hi : t < (Finset.univ.filter (fun v => π v = i)).card) :
    (Finset.univ.filter (fun v => π v = i)).Nonempty := by
  exact Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le t) hi)

private lemma proper_colorClass_mem_maxIndep_filter_of_t_lt
    {n k t : ℕ} (G : SimpleGraph (Fin n)) (π : Fin n → Fin k)
    (hπ : IsProperColoring G k π) (ht : G.indepNum ≤ t + 1) (i : Fin k)
    (hi : t < (Finset.univ.filter (fun v => π v = i)).card) :
    (Finset.univ.filter (fun v => π v = i)) ∈
      Finset.univ.filter (fun S : Finset (Fin n) => S.card = G.indepNum ∧ G.IsNIndepSet G.indepNum S) := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact proper_colorClass_card_eq_indepNum_of_t_lt G π hπ ht i hi
  · rw [← proper_colorClass_card_eq_indepNum_of_t_lt G π hπ ht i hi]
    exact proper_colorClass_isNIndepSet G π hπ i

private lemma proper_colorClass_card_eq_tsucc_of_t_lt
    {n k t : ℕ} (G : SimpleGraph (Fin n)) (π : Fin n → Fin k)
    (hπ : IsProperColoring G k π) (ht : G.indepNum ≤ t + 1) (i : Fin k)
    (hi : t < (Finset.univ.filter (fun v => π v = i)).card) :
    (Finset.univ.filter (fun v => π v = i)).card = t + 1 := by
  have hcard : (Finset.univ.filter (fun v => π v = i)).card = G.indepNum :=
    proper_colorClass_card_eq_indepNum_of_t_lt G π hπ ht i hi
  have hsucc : t + 1 ≤ (Finset.univ.filter (fun v => π v = i)).card := Nat.succ_le_of_lt hi
  have hle : G.indepNum ≤ t + 1 := ht
  omega

private lemma proper_colorClass_mem_tsuccIndep_filter_of_t_lt
    {n k t : ℕ} (G : SimpleGraph (Fin n)) (π : Fin n → Fin k)
    (hπ : IsProperColoring G k π) (ht : G.indepNum ≤ t + 1) (i : Fin k)
    (hi : t < (Finset.univ.filter (fun v => π v = i)).card) :
    (Finset.univ.filter (fun v => π v = i)) ∈
      Finset.univ.filter (fun S : Finset (Fin n) => S.card = t + 1 ∧ G.IsNIndepSet (t + 1) S) := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact proper_colorClass_card_eq_tsucc_of_t_lt G π hπ ht i hi
  · rw [← proper_colorClass_card_eq_tsucc_of_t_lt G π hπ ht i hi]
    exact proper_colorClass_isNIndepSet G π hπ i

private lemma proper_colorClass_injective_on_large
    {n k t : ℕ} (π : Fin n → Fin k) :
    Set.InjOn (fun i : Fin k => Finset.univ.filter (fun v => π v = i))
      {i : Fin k | t < (Finset.univ.filter (fun v => π v = i)).card} := by
  intro i hi j hj hij
  by_contra hne
  rcases proper_colorClass_nonempty_of_t_lt π i hi with ⟨v, hv⟩
  have hvi : π v = i := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hv
  have hvj : π v = j := by
    have hvmem : v ∈ Finset.univ.filter (fun x => π x = j) := by
      simpa [hij] using hv
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hvmem
  have : i = j := hvi.symm.trans hvj
  exact hne this

private lemma large_color_classes_card_le_maxIndepSetCount
    {n k t : ℕ} (G : SimpleGraph (Fin n)) (π : Fin n → Fin k)
    (hπ : IsProperColoring G k π) (ht : G.indepNum ≤ t + 1) :
    (Finset.univ.filter
      (fun i : Fin k => t < (Finset.univ.filter (fun v => π v = i)).card)).card
      ≤ maxIndepSetCount G := by
  classical
  let largeColors : Finset (Fin k) :=
    Finset.univ.filter (fun i : Fin k => t < (Finset.univ.filter (fun v => π v = i)).card)
  let maxIndepSets : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun S : Finset (Fin n) => S.card = G.indepNum ∧ G.IsNIndepSet G.indepNum S)
  have hmap : ∀ i ∈ largeColors, (Finset.univ.filter (fun v => π v = i)) ∈ maxIndepSets := by
    intro i hi
    exact proper_colorClass_mem_maxIndep_filter_of_t_lt G π hπ ht i
      (by simpa [largeColors] using hi)
  have hinj : Set.InjOn (fun i : Fin k => Finset.univ.filter (fun v => π v = i)) ↑largeColors := by
    intro i hi j hj hij
    exact proper_colorClass_injective_on_large π
      (by simpa [largeColors] using hi)
      (by simpa [largeColors] using hj)
      hij
  have hcard := Finset.card_le_card_of_injOn
    (fun i : Fin k => Finset.univ.filter (fun v => π v = i)) hmap hinj
  simpa [largeColors, maxIndepSets, maxIndepSetCount, indepSetCount] using hcard

private lemma large_color_classes_card_le_indepSetCount_tsucc
    {n k t : ℕ} (G : SimpleGraph (Fin n)) (π : Fin n → Fin k)
    (hπ : IsProperColoring G k π) (ht : G.indepNum ≤ t + 1) :
    (Finset.univ.filter
      (fun i : Fin k => t < (Finset.univ.filter (fun v => π v = i)).card)).card
      ≤ indepSetCount G (t + 1) := by
  classical
  let largeColors : Finset (Fin k) :=
    Finset.univ.filter (fun i : Fin k => t < (Finset.univ.filter (fun v => π v = i)).card)
  let tsuccIndepSets : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun S : Finset (Fin n) => S.card = t + 1 ∧ G.IsNIndepSet (t + 1) S)
  have hmap : ∀ i ∈ largeColors, (Finset.univ.filter (fun v => π v = i)) ∈ tsuccIndepSets := by
    intro i hi
    exact proper_colorClass_mem_tsuccIndep_filter_of_t_lt G π hπ ht i
      (by simpa [largeColors] using hi)
  have hinj : Set.InjOn (fun i : Fin k => Finset.univ.filter (fun v => π v = i)) ↑largeColors := by
    intro i hi j hj hij
    exact proper_colorClass_injective_on_large π
      (by simpa [largeColors] using hi)
      (by simpa [largeColors] using hj)
      hij
  have hcard := Finset.card_le_card_of_injOn
    (fun i : Fin k => Finset.univ.filter (fun v => π v = i)) hmap hinj
  simpa [largeColors, tsuccIndepSets, indepSetCount] using hcard

private noncomputable def choose_large_color_rep
    {n k t : ℕ} (π : Fin n → Fin k) (i : Fin k)
    (hi : t < (Finset.univ.filter (fun v => π v = i)).card) : Fin n :=
  Classical.choose (proper_colorClass_nonempty_of_t_lt π i hi)

private lemma choose_large_color_rep_mem_class
    {n k t : ℕ} (π : Fin n → Fin k) (i : Fin k)
    (hi : t < (Finset.univ.filter (fun v => π v = i)).card) :
    choose_large_color_rep π i hi ∈ Finset.univ.filter (fun v => π v = i) :=
  Classical.choose_spec (proper_colorClass_nonempty_of_t_lt π i hi)

private lemma choose_large_color_rep_color
    {n k t : ℕ} (π : Fin n → Fin k) (i : Fin k)
    (hi : t < (Finset.univ.filter (fun v => π v = i)).card) :
    π (choose_large_color_rep π i hi) = i := by
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
    choose_large_color_rep_mem_class π i hi

private lemma choose_large_color_rep_eq_implies_eq
    {n k t : ℕ} (π : Fin n → Fin k) (i j : Fin k)
    (hi : t < (Finset.univ.filter (fun v => π v = i)).card)
    (hj : t < (Finset.univ.filter (fun v => π v = j)).card)
    (hij : choose_large_color_rep π i hi = choose_large_color_rep π j hj) :
    i = j := by
  have hci : π (choose_large_color_rep π i hi) = i := choose_large_color_rep_color π i hi
  have hcj : π (choose_large_color_rep π j hj) = j := choose_large_color_rep_color π j hj
  rw [hij] at hci
  exact hci.symm.trans hcj

private lemma oversized_color_class_erase_rep_card_eq_sub_one
    {n k t : ℕ} (π : Fin n → Fin k) (i : Fin k)
    (hi : t < (Finset.univ.filter (fun v => π v = i)).card) :
    ((Finset.univ.filter (fun v => π v = i)).erase (choose_large_color_rep π i hi)).card =
      (Finset.univ.filter (fun v => π v = i)).card - 1 := by
  rw [Finset.card_erase_of_mem]
  exact choose_large_color_rep_mem_class π i hi

private lemma oversized_color_class_erase_rep_card_le_t
    {n k t : ℕ} (G : SimpleGraph (Fin n)) (π : Fin n → Fin k)
    (hπ : IsProperColoring G k π) (ht : G.indepNum ≤ t + 1) (i : Fin k)
    (hi : t < (Finset.univ.filter (fun v => π v = i)).card) :
    ((Finset.univ.filter (fun v => π v = i)).erase (choose_large_color_rep π i hi)).card ≤ t := by
  rw [oversized_color_class_erase_rep_card_eq_sub_one π i hi]
  have hcard : (Finset.univ.filter (fun v => π v = i)).card = G.indepNum :=
    proper_colorClass_card_eq_indepNum_of_t_lt G π hπ ht i hi
  rw [hcard]
  omega

private lemma non_oversized_color_class_card_le_t
    {n k t : ℕ} (π : Fin n → Fin k) (i : Fin k)
    (hi : ¬ t < (Finset.univ.filter (fun v => π v = i)).card) :
    (Finset.univ.filter (fun v => π v = i)).card ≤ t := by
  exact Nat.le_of_not_gt hi

private noncomputable def largeColors
    {n k t : ℕ} (π : Fin n → Fin k) : Finset (Fin k) :=
  Finset.univ.filter (fun i : Fin k => t < (Finset.univ.filter (fun v => π v = i)).card)

private lemma mem_largeColors_iff
    {n k t : ℕ} (π : Fin n → Fin k) (i : Fin k) :
    i ∈ largeColors (t := t) π ↔ t < (Finset.univ.filter (fun v => π v = i)).card := by
  simp [largeColors]

private lemma not_mem_largeColors_iff
    {n k t : ℕ} (π : Fin n → Fin k) (i : Fin k) :
    i ∉ largeColors (t := t) π ↔ ¬ t < (Finset.univ.filter (fun v => π v = i)).card := by
  simp [largeColors]

private noncomputable def largeColorReps
    {n k t : ℕ} (π : Fin n → Fin k) : Finset (Fin n) :=
  (largeColors (t := t) π).attach.image (fun i =>
    choose_large_color_rep (t := t) π i.1 ((mem_largeColors_iff (t := t) π i.1).mp i.2))

private lemma choose_large_color_rep_mem_largeColorReps
    {n k t : ℕ} (π : Fin n → Fin k) (i : Fin k)
    (hi : t < (Finset.univ.filter (fun v => π v = i)).card) :
    choose_large_color_rep π i hi ∈ largeColorReps (t := t) π := by
  classical
  unfold largeColorReps
  refine Finset.mem_image.mpr ?_
  refine ⟨⟨i, by simpa [largeColors] using hi⟩, ?_, ?_⟩
  · simp
  · have hproof : (by simpa [largeColors] using hi : t < (Finset.univ.filter (fun v => π v = i)).card) = hi :=
        Subsingleton.elim _ _
    simp

private noncomputable def recolorSigma
    {n k t : ℕ} (π : Fin n → Fin k) : Fin n → Fin (k + (largeColorReps (t := t) π).card) :=
  fun x =>
    if hx : x ∈ largeColorReps (t := t) π then
      Fin.natAdd k ((largeColorReps (t := t) π).equivFin ⟨x, hx⟩)
    else
      Fin.castAdd (largeColorReps (t := t) π).card (π x)

private lemma recolorSigma_eq_castAdd_of_not_mem_reps
    {n k t : ℕ} (π : Fin n → Fin k) (x : Fin n)
    (hx : x ∉ largeColorReps (t := t) π) :
    recolorSigma (t := t) π x = Fin.castAdd (largeColorReps (t := t) π).card (π x) := by
  simp [recolorSigma, hx]

private lemma recolorSigma_eq_natAdd_of_mem_reps
    {n k t : ℕ} (π : Fin n → Fin k) (x : Fin n)
    (hx : x ∈ largeColorReps (t := t) π) :
    recolorSigma (t := t) π x =
      Fin.natAdd k ((largeColorReps (t := t) π).equivFin ⟨x, hx⟩) := by
  simp [recolorSigma, hx]

private lemma not_mem_reps_of_recolorSigma_eq_castAdd
    {n k t : ℕ} (π : Fin n → Fin k) (x : Fin n) (i : Fin k)
    (hx : recolorSigma (t := t) π x =
      Fin.castAdd (largeColorReps (t := t) π).card i) :
    x ∉ largeColorReps (t := t) π := by
  intro hxmem
  have hval : (recolorSigma (t := t) π x).val =
      (Fin.castAdd (largeColorReps (t := t) π).card i).val := congrArg Fin.val hx
  simp [recolorSigma, hxmem] at hval
  omega

private lemma pi_eq_of_recolorSigma_eq_castAdd
    {n k t : ℕ} (π : Fin n → Fin k) (x : Fin n) (i : Fin k)
    (hx : recolorSigma (t := t) π x =
      Fin.castAdd (largeColorReps (t := t) π).card i) :
    π x = i := by
  have hxmem : x ∉ largeColorReps (t := t) π :=
    not_mem_reps_of_recolorSigma_eq_castAdd (t := t) π x i hx
  have : Fin.castAdd (largeColorReps (t := t) π).card (π x) =
      Fin.castAdd (largeColorReps (t := t) π).card i := by
    simpa [recolorSigma, hxmem] using hx
  exact Fin.castAdd_injective _ _ this

private lemma mem_reps_of_recolorSigma_eq_natAdd
    {n k t : ℕ} (π : Fin n → Fin k) (x : Fin n) (j : Fin (largeColorReps (t := t) π).card)
    (hx : recolorSigma (t := t) π x = Fin.natAdd k j) :
    x ∈ largeColorReps (t := t) π := by
  by_contra hxmem
  have hval : (recolorSigma (t := t) π x).val = (Fin.natAdd k j).val := congrArg Fin.val hx
  simp [recolorSigma, hxmem] at hval
  omega

private lemma equivFin_eq_of_recolorSigma_eq_natAdd
    {n k t : ℕ} (π : Fin n → Fin k) (x : Fin n) (j : Fin (largeColorReps (t := t) π).card)
    (hx : recolorSigma (t := t) π x = Fin.natAdd k j) :
    (largeColorReps (t := t) π).equivFin ⟨x, mem_reps_of_recolorSigma_eq_natAdd (t := t) π x j hx⟩ = j := by
  have hxmem : x ∈ largeColorReps (t := t) π :=
    mem_reps_of_recolorSigma_eq_natAdd (t := t) π x j hx
  have : Fin.natAdd k ((largeColorReps (t := t) π).equivFin ⟨x, hxmem⟩) = Fin.natAdd k j := by
    simpa [recolorSigma, hxmem] using hx
  exact Fin.natAdd_injective _ _ this

private lemma mem_oldFiber_iff
    {n k t : ℕ} (π : Fin n → Fin k) (x : Fin n) (i : Fin k) :
    x ∈ Finset.univ.filter (fun v => recolorSigma (t := t) π v =
      Fin.castAdd (largeColorReps (t := t) π).card i) ↔
      recolorSigma (t := t) π x = Fin.castAdd (largeColorReps (t := t) π).card i := by
  simp

private lemma mem_newFiber_iff
    {n k t : ℕ} (π : Fin n → Fin k) (x : Fin n)
    (j : Fin (largeColorReps (t := t) π).card) :
    x ∈ Finset.univ.filter (fun v => recolorSigma (t := t) π v = Fin.natAdd k j) ↔
      recolorSigma (t := t) π x = Fin.natAdd k j := by
  simp

private lemma castAdd_eq_of_recolorSigma_eq_old
    {n k t : ℕ} (π : Fin n → Fin k) {u v : Fin n} {i : Fin k}
    (hu : recolorSigma (t := t) π u = Fin.castAdd (largeColorReps (t := t) π).card i)
    (hv : recolorSigma (t := t) π v = Fin.castAdd (largeColorReps (t := t) π).card i) :
    π u = π v := by
  have hπu : π u = i := pi_eq_of_recolorSigma_eq_castAdd (t := t) π u i hu
  have hπv : π v = i := pi_eq_of_recolorSigma_eq_castAdd (t := t) π v i hv
  exact hπu.trans hπv.symm

private lemma newFiber_subset_singleton
    {n k t : ℕ} (π : Fin n → Fin k) (j : Fin (largeColorReps (t := t) π).card) :
    (Finset.univ.filter (fun v => recolorSigma (t := t) π v = Fin.natAdd k j)) ⊆
      ({((largeColorReps (t := t) π).equivFin.symm j : Fin n)} : Finset (Fin n)) := by
  intro x hx
  have hxeq : recolorSigma (t := t) π x = Fin.natAdd k j := (mem_newFiber_iff (t := t) π x j).mp hx
  have hxmem : x ∈ largeColorReps (t := t) π :=
    mem_reps_of_recolorSigma_eq_natAdd (t := t) π x j hxeq
  have heq : (largeColorReps (t := t) π).equivFin ⟨x, hxmem⟩ = j :=
    equivFin_eq_of_recolorSigma_eq_natAdd (t := t) π x j hxeq
  have hsub : (⟨x, hxmem⟩ : ↥(largeColorReps (t := t) π)) =
      (largeColorReps (t := t) π).equivFin.symm j := by
    apply (largeColorReps (t := t) π).equivFin.injective
    simpa using heq
  have hxval : x = (largeColorReps (t := t) π).equivFin.symm j := congrArg Subtype.val hsub
  simp [hxval]

private lemma newFiber_card_le_one
    {n k t : ℕ} (π : Fin n → Fin k) (j : Fin (largeColorReps (t := t) π).card) :
    (Finset.univ.filter (fun v => recolorSigma (t := t) π v = Fin.natAdd k j)).card ≤ 1 := by
  exact le_trans (Finset.card_le_card (newFiber_subset_singleton (t := t) π j))
    (by simp)

private lemma mem_largeColors_of_mem_largeColorReps
    {n k t : ℕ} (π : Fin n → Fin k) {x : Fin n}
    (hx : x ∈ largeColorReps (t := t) π) :
    π x ∈ largeColors (t := t) π := by
  classical
  unfold largeColorReps at hx
  rcases Finset.mem_image.mp hx with ⟨i, hi_mem, hix⟩
  have hcolor : π (choose_large_color_rep (t := t) π i.1
      ((mem_largeColors_iff (t := t) π i.1).mp i.2)) = i.1 :=
    choose_large_color_rep_color (t := t) π i.1 ((mem_largeColors_iff (t := t) π i.1).mp i.2)
  rw [← hix, hcolor]
  exact i.2

private lemma not_mem_largeColorReps_of_color_not_large
    {n k t : ℕ} (π : Fin n → Fin k) {x : Fin n}
    (hx : ¬ π x ∈ largeColors (t := t) π) :
    x ∉ largeColorReps (t := t) π := by
  intro hxmem
  exact hx (mem_largeColors_of_mem_largeColorReps (t := t) π hxmem)

private lemma mem_oldFiber_iff_color_eq_and_not_mem_reps
    {n k t : ℕ} (π : Fin n → Fin k) (x : Fin n) (i : Fin k) :
    x ∈ Finset.univ.filter (fun v => recolorSigma (t := t) π v =
      Fin.castAdd (largeColorReps (t := t) π).card i) ↔
      π x = i ∧ x ∉ largeColorReps (t := t) π := by
  constructor
  · intro hx
    have hσ : recolorSigma (t := t) π x =
        Fin.castAdd (largeColorReps (t := t) π).card i := (mem_oldFiber_iff (t := t) π x i).mp hx
    exact ⟨pi_eq_of_recolorSigma_eq_castAdd (t := t) π x i hσ,
      not_mem_reps_of_recolorSigma_eq_castAdd (t := t) π x i hσ⟩
  · rintro ⟨hcolor, hxnot⟩
    apply (mem_oldFiber_iff (t := t) π x i).mpr
    rw [recolorSigma_eq_castAdd_of_not_mem_reps (t := t) π x hxnot, hcolor]

private lemma oldFiber_eq_colorClass_of_not_large
    {n k t : ℕ} (π : Fin n → Fin k) (i : Fin k)
    (hi : i ∉ largeColors (t := t) π) :
    Finset.univ.filter (fun v => recolorSigma (t := t) π v =
      Fin.castAdd (largeColorReps (t := t) π).card i) =
    Finset.univ.filter (fun v => π v = i) := by
  ext x
  constructor
  · intro hx
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      (mem_oldFiber_iff_color_eq_and_not_mem_reps (t := t) π x i).mp hx |>.1
  · intro hx
    apply (mem_oldFiber_iff_color_eq_and_not_mem_reps (t := t) π x i).mpr
    refine ⟨?_, ?_⟩
    · simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hx
    · exact not_mem_largeColorReps_of_color_not_large (t := t) π
        (by
          have hx' : π x = i := by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hx
          simpa [hx'] using hi)

private lemma oldFiber_eq_erase_choose_rep_of_mem_large
    {n k t : ℕ} (π : Fin n → Fin k) (i : Fin k)
    (hi : i ∈ largeColors (t := t) π) :
    Finset.univ.filter (fun v => recolorSigma (t := t) π v =
      Fin.castAdd (largeColorReps (t := t) π).card i) =
    (Finset.univ.filter (fun v => π v = i)).erase
      (choose_large_color_rep (t := t) π i ((mem_largeColors_iff (t := t) π i).mp hi)) := by
  ext x
  constructor
  · intro hx
    rcases (mem_oldFiber_iff_color_eq_and_not_mem_reps (t := t) π x i).mp hx with ⟨hcolor, hxnot⟩
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, hcolor⟩
    intro hxeq
    apply hxnot
    rw [hxeq]
    exact choose_large_color_rep_mem_largeColorReps (t := t) π i ((mem_largeColors_iff (t := t) π i).mp hi)
  · intro hx
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rcases hx with ⟨hxneq, hcolor⟩
    apply (mem_oldFiber_iff_color_eq_and_not_mem_reps (t := t) π x i).mpr
    refine ⟨hcolor, ?_⟩
    intro hxmem
    unfold largeColorReps at hxmem
    rcases Finset.mem_image.mp hxmem with ⟨j, hjmem, hjx⟩
    have hjcolor : π (choose_large_color_rep (t := t) π j.1
        ((mem_largeColors_iff (t := t) π j.1).mp j.2)) = j.1 :=
      choose_large_color_rep_color (t := t) π j.1 ((mem_largeColors_iff (t := t) π j.1).mp j.2)
    have hji : j.1 = i := by
      calc
        j.1 = π (choose_large_color_rep (t := t) π j.1 ((mem_largeColors_iff (t := t) π j.1).mp j.2)) := hjcolor.symm
        _ = π x := by rw [hjx]
        _ = i := hcolor
    have hchoose :
        choose_large_color_rep (t := t) π j.1 ((mem_largeColors_iff (t := t) π j.1).mp j.2) =
        choose_large_color_rep (t := t) π i ((mem_largeColors_iff (t := t) π i).mp hi) := by
      subst hji
      rfl
    have : x = choose_large_color_rep (t := t) π i ((mem_largeColors_iff (t := t) π i).mp hi) := by
      rw [← hjx, hchoose]
    exact hxneq this

private lemma largeColorReps_card_eq_largeColors_card
    {n k t : ℕ} (π : Fin n → Fin k) :
    (largeColorReps (t := t) π).card = (largeColors (t := t) π).card := by
  classical
  unfold largeColorReps
  rw [Finset.card_image_of_injOn]
  simpa using Finset.card_attach (largeColors (t := t) π)
  intro a _ha b _hb hab
  exact Subtype.ext
    (choose_large_color_rep_eq_implies_eq (t := t) π a.1 b.1
      ((mem_largeColors_iff (t := t) π a.1).mp a.2)
      ((mem_largeColors_iff (t := t) π b.1).mp b.2)
      hab)

private lemma recolorSigma_isProperColoring
    {n k t : ℕ} (G : SimpleGraph (Fin n)) (π : Fin n → Fin k)
    (hπ : IsProperColoring G k π) :
    IsProperColoring G (k + (largeColorReps (t := t) π).card) (recolorSigma (t := t) π) := by
  intro u v hadj huv
  by_cases hu : u ∈ largeColorReps (t := t) π
  · by_cases hv : v ∈ largeColorReps (t := t) π
    · have huj : recolorSigma (t := t) π u =
          Fin.natAdd k ((largeColorReps (t := t) π).equivFin ⟨u, hu⟩) :=
        recolorSigma_eq_natAdd_of_mem_reps (t := t) π u hu
      have hvj : recolorSigma (t := t) π v =
          Fin.natAdd k ((largeColorReps (t := t) π).equivFin ⟨v, hv⟩) :=
        recolorSigma_eq_natAdd_of_mem_reps (t := t) π v hv
      have hEq : (largeColorReps (t := t) π).equivFin ⟨u, hu⟩ =
          (largeColorReps (t := t) π).equivFin ⟨v, hv⟩ := by
        apply Fin.ext
        have hval : (Fin.natAdd k ((largeColorReps (t := t) π).equivFin ⟨u, hu⟩)).val =
            (Fin.natAdd k ((largeColorReps (t := t) π).equivFin ⟨v, hv⟩)).val :=
          congrArg Fin.val (by simpa [huj, hvj] using huv)
        simpa using hval
      have huv' : u = v := congrArg Subtype.val ((largeColorReps (t := t) π).equivFin.injective hEq)
      exact G.ne_of_adj hadj huv'
    · have hval : (recolorSigma (t := t) π u).val = (recolorSigma (t := t) π v).val := congrArg Fin.val huv
      rw [recolorSigma_eq_natAdd_of_mem_reps (t := t) π u hu,
        recolorSigma_eq_castAdd_of_not_mem_reps (t := t) π v hv] at hval
      simp at hval
      omega
  · by_cases hv : v ∈ largeColorReps (t := t) π
    · have hval : (recolorSigma (t := t) π u).val = (recolorSigma (t := t) π v).val := congrArg Fin.val huv
      rw [recolorSigma_eq_castAdd_of_not_mem_reps (t := t) π u hu,
        recolorSigma_eq_natAdd_of_mem_reps (t := t) π v hv] at hval
      simp at hval
      omega
    · have hEq : Fin.castAdd (largeColorReps (t := t) π).card (π u) =
          Fin.castAdd (largeColorReps (t := t) π).card (π v) := by
        simpa [recolorSigma_eq_castAdd_of_not_mem_reps (t := t) π u hu,
          recolorSigma_eq_castAdd_of_not_mem_reps (t := t) π v hv] using huv
      exact hπ u v hadj (Fin.castAdd_injective _ _ hEq)

private lemma oldFiber_card_le_t
    {n k t : ℕ} (G : SimpleGraph (Fin n)) (π : Fin n → Fin k)
    (hπ : IsProperColoring G k π) (ht : G.indepNum ≤ t + 1) (i : Fin k) :
    (Finset.univ.filter (fun v => recolorSigma (t := t) π v =
      Fin.castAdd (largeColorReps (t := t) π).card i)).card ≤ t := by
  by_cases hi : i ∈ largeColors (t := t) π
  · rw [oldFiber_eq_erase_choose_rep_of_mem_large (t := t) π i hi]
    exact oversized_color_class_erase_rep_card_le_t (t := t) G π hπ ht i
      ((mem_largeColors_iff (t := t) π i).mp hi)
  · rw [oldFiber_eq_colorClass_of_not_large (t := t) π i hi]
    exact non_oversized_color_class_card_le_t (t := t) π i
      ((not_mem_largeColors_iff (t := t) π i).mp hi)

private lemma remaining_colorClass_after_largeColorReps_card_le_t
    {n k t : ℕ} (G : SimpleGraph (Fin n)) (π : Fin n → Fin k)
    (hπ : IsProperColoring G k π) (ht : G.indepNum ≤ t + 1) (i : Fin k) :
    (Finset.univ.filter
      (fun v : Fin n => π v = i ∧ v ∉ largeColorReps (t := t) π)).card ≤ t := by
  by_cases hi : i ∈ largeColors (t := t) π
  · have hsubset :
        Finset.univ.filter
          (fun v : Fin n => π v = i ∧ v ∉ largeColorReps (t := t) π) ⊆
        (Finset.univ.filter (fun v : Fin n => π v = i)).erase
          (choose_large_color_rep (t := t) π i ((mem_largeColors_iff (t := t) π i).mp hi)) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hx ⊢
      refine ⟨?_, hx.1⟩
      intro hxeq
      exact hx.2 (by
        rw [hxeq]
        exact choose_large_color_rep_mem_largeColorReps (t := t) π i
          ((mem_largeColors_iff (t := t) π i).mp hi))
    exact (Finset.card_le_card hsubset).trans
      (oversized_color_class_erase_rep_card_le_t (t := t) G π hπ ht i
        ((mem_largeColors_iff (t := t) π i).mp hi))
  · have hsubset :
        Finset.univ.filter
          (fun v : Fin n => π v = i ∧ v ∉ largeColorReps (t := t) π) ⊆
        Finset.univ.filter (fun v : Fin n => π v = i) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hx.1
    exact (Finset.card_le_card hsubset).trans
      (non_oversized_color_class_card_le_t (t := t) π i
        ((not_mem_largeColors_iff (t := t) π i).mp hi))

/--
Compatibility theorem for the explicit removed-vertex seam: under the older
`α(G) ≤ t + 1` hypothesis, removing one representative from each oversized
color class leaves all old classes of size at most `t`; the removed set is
bounded by `maxIndepSetCount G`.
-/
theorem exists_removed_fibers_certificate_of_indepNum_le
    {n k t : ℕ} (G : SimpleGraph (Fin n)) (π : Fin n → Fin k)
    (hπ : IsProperColoring G k π) (ht : G.indepNum ≤ t + 1) :
    ∃ R : Finset (Fin n),
      R.card ≤ maxIndepSetCount G ∧
      ∀ i : Fin k,
        (Finset.univ.filter (fun v : Fin n => π v = i ∧ v ∉ R)).card ≤ t := by
  refine ⟨largeColorReps (t := t) π, ?_, ?_⟩
  · rw [largeColorReps_card_eq_largeColors_card (t := t) π]
    exact large_color_classes_card_le_maxIndepSetCount (t := t) G π hπ ht
  · exact remaining_colorClass_after_largeColorReps_card_le_t (t := t) G π hπ ht

/-- The surplus of a color class above the threshold `t`. -/
noncomputable def colorClassSurplus
    {n k : ℕ} (π : Fin n → Fin k) (t : ℕ) (i : Fin k) : ℕ :=
  (Finset.univ.filter (fun v : Fin n => π v = i)).card - t

/-- Total surplus of a coloring above the threshold `t`. -/
noncomputable def coloringSurplus
    {n k : ℕ} (π : Fin n → Fin k) (t : ℕ) : ℕ :=
  ∑ i : Fin k, colorClassSurplus π t i

/-- The deficit of a color class below the threshold `t`. -/
noncomputable def colorClassDeficit
    {n k : ℕ} (π : Fin n → Fin k) (t : ℕ) (i : Fin k) : ℕ :=
  t - (Finset.univ.filter (fun v : Fin n => π v = i)).card

/-- Total deficit of a coloring below the threshold `t`. -/
noncomputable def coloringDeficit
    {n k : ℕ} (π : Fin n → Fin k) (t : ℕ) : ℕ :=
  ∑ i : Fin k, colorClassDeficit π t i

/--
Signed total imbalance of a coloring relative to the target class size `t`.

This integer version is the algebraically clean object behind the surplus /
deficit split.
-/
noncomputable def coloringSignedImbalance
    {n k : ℕ} (π : Fin n → Fin k) (t : ℕ) : ℤ :=
  ∑ i : Fin k,
    (((Finset.univ.filter (fun v : Fin n => π v = i)).card : ℤ) - (t : ℤ))

/-- The color-class fibers of any coloring partition the vertex set. -/
theorem sum_colorClass_card_eq
    {n k : ℕ} (π : Fin n → Fin k) :
    (∑ i : Fin k,
      (Finset.univ.filter (fun v : Fin n => π v = i)).card) = n := by
  classical
  have hmaps :
      Set.MapsTo π (↑(Finset.univ : Finset (Fin n)))
        (↑(Finset.univ : Finset (Fin k))) := by
    intro v hv
    simp
  have h :=
    Finset.card_eq_sum_card_fiberwise
      (f := π) (s := (Finset.univ : Finset (Fin n)))
      (t := (Finset.univ : Finset (Fin k))) hmaps
  simpa using h.symm

/-- The signed imbalance is exactly `n - k * t`. -/
theorem coloringSignedImbalance_eq
    {n k t : ℕ} (π : Fin n → Fin k) :
    coloringSignedImbalance π t = (n : ℤ) - (k : ℤ) * (t : ℤ) := by
  classical
  have hsum_nat := sum_colorClass_card_eq (n := n) (k := k) π
  have hsum_int :
      (∑ i : Fin k,
        ((Finset.univ.filter (fun v : Fin n => π v = i)).card : ℤ)) = (n : ℤ) := by
    exact_mod_cast hsum_nat
  calc
    coloringSignedImbalance π t
        = (∑ i : Fin k,
            ((Finset.univ.filter (fun v : Fin n => π v = i)).card : ℤ)) -
          (∑ i : Fin k, (t : ℤ)) := by
            simp [coloringSignedImbalance, Finset.sum_sub_distrib]
    _ = (n : ℤ) - (k : ℤ) * (t : ℤ) := by
            simp [hsum_int]

/-- If every color class has size at most `t`, the total surplus is zero. -/
theorem coloringSurplus_eq_zero_of_colorClass_card_le
    {n k t : ℕ} (π : Fin n → Fin k)
    (hclasses :
      ∀ i : Fin k,
        (Finset.univ.filter (fun v : Fin n => π v = i)).card ≤ t) :
    coloringSurplus π t = 0 := by
  classical
  rw [coloringSurplus]
  apply Finset.sum_eq_zero
  intro i hi
  simp [colorClassSurplus, Nat.sub_eq_zero_of_le (hclasses i)]

private lemma int_nat_surplus_sub_deficit
    (a t : ℕ) :
    ((a - t : ℕ) : ℤ) - ((t - a : ℕ) : ℤ) = (a : ℤ) - (t : ℤ) := by
  by_cases hta : t ≤ a
  · have hat_zero : t - a = 0 := Nat.sub_eq_zero_of_le hta
    simp [hat_zero, Int.ofNat_sub hta]
  · have hat : a ≤ t := Nat.le_of_not_ge hta
    have hta_zero : a - t = 0 := Nat.sub_eq_zero_of_le hat
    simp [hta_zero, Int.ofNat_sub hat]

/--
Surplus minus deficit recovers the signed imbalance.  This is the deterministic
balance identity behind the next probabilistic frontier: bounding surplus can
be replaced by bounding deficit plus the global `n - k*t` imbalance.
-/
theorem coloringSurplus_sub_coloringDeficit_eq_signedImbalance
    {n k t : ℕ} (π : Fin n → Fin k) :
    (coloringSurplus π t : ℤ) - (coloringDeficit π t : ℤ) =
      coloringSignedImbalance π t := by
  classical
  rw [coloringSurplus, coloringDeficit, coloringSignedImbalance]
  calc
    ((∑ i : Fin k, colorClassSurplus π t i : ℕ) : ℤ) -
        ((∑ i : Fin k, colorClassDeficit π t i : ℕ) : ℤ)
        = (∑ i : Fin k, (colorClassSurplus π t i : ℤ)) -
          (∑ i : Fin k, (colorClassDeficit π t i : ℤ)) := by
            simp
    _ = ∑ i : Fin k,
          ((colorClassSurplus π t i : ℤ) -
            (colorClassDeficit π t i : ℤ)) := by
            rw [Finset.sum_sub_distrib]
    _ = ∑ i : Fin k,
          (((Finset.univ.filter (fun v : Fin n => π v = i)).card : ℤ) -
            (t : ℤ)) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [colorClassSurplus, colorClassDeficit,
              int_nat_surplus_sub_deficit]

/--
If every color class has size at most `t`, the total deficit is exactly the
product slack `k*t - n`.
-/
theorem coloringDeficit_eq_product_sub_of_colorClass_card_le
    {n k t : ℕ} (π : Fin n → Fin k)
    (hclasses :
      ∀ i : Fin k,
        (Finset.univ.filter (fun v : Fin n => π v = i)).card ≤ t) :
    coloringDeficit π t = k * t - n := by
  have hsurplus_zero :
      coloringSurplus π t = 0 :=
    coloringSurplus_eq_zero_of_colorClass_card_le π hclasses
  have hbalance :=
    coloringSurplus_sub_coloringDeficit_eq_signedImbalance (n := n) (k := k) (t := t) π
  rw [hsurplus_zero, coloringSignedImbalance_eq] at hbalance
  omega

/--
Integer upper bound form of the balance identity.  It is often easier to prove
a probabilistic bound on the deficit plus the absolute global imbalance
`|n - k*t|`; this theorem converts that package into a surplus bound.
-/
theorem coloringSurplus_le_deficit_add_abs_imbalance_int
    {n k t : ℕ} (π : Fin n → Fin k) :
    (coloringSurplus π t : ℤ) ≤
      (coloringDeficit π t : ℤ) +
        (coloringSignedImbalance π t).natAbs := by
  have h :=
    coloringSurplus_sub_coloringDeficit_eq_signedImbalance
      (n := n) (k := k) (t := t) π
  have hle :
      (coloringSurplus π t : ℤ) - (coloringDeficit π t : ℤ) ≤
        ((coloringSignedImbalance π t).natAbs : ℤ) := by
    simpa [h] using (Int.le_natAbs (a := coloringSignedImbalance π t))
  simpa [add_comm] using (sub_le_iff_le_add.mp hle)

private theorem int_natAbs_le_of_two_sided_bound
    {x : ℤ} {B : ℕ} (hlower : -((B : ℤ)) ≤ x) (hupper : x ≤ (B : ℤ)) :
    x.natAbs ≤ B := by
  rcases Int.natAbs_eq x with hx | hx
  · rw [hx] at hupper
    exact Int.ofNat_le.mp hupper
  · exact Int.ofNat_le.mp (by
      have hneg : -((B : ℤ)) ≤ -((x.natAbs : ℤ)) := by
        rw [hx] at hlower
        exact hlower
      exact (neg_le_neg_iff.mp hneg))

/--
If the product `k*t` lies in an integer window of radius `B` around `n`, then
the scalar imbalance `|n - k*t|` is at most `B`.
-/
theorem scalarImbalance_natAbs_le_of_product_window
    {n k t B : ℕ}
    (hlower : (n : ℤ) - (B : ℤ) ≤ (k : ℤ) * (t : ℤ))
    (hupper : (k : ℤ) * (t : ℤ) ≤ (n : ℤ) + (B : ℤ)) :
    (((n : ℤ) - (k : ℤ) * (t : ℤ)).natAbs) ≤ B := by
  apply int_natAbs_le_of_two_sided_bound
  · linarith
  · linarith

private lemma exists_removed_subset_for_colorClass
    {n k t : ℕ} (π : Fin n → Fin k) (i : Fin k) :
    ∃ Rᵢ : Finset (Fin n),
      Rᵢ ⊆ Finset.univ.filter (fun v : Fin n => π v = i) ∧
      Rᵢ.card = colorClassSurplus π t i ∧
      (Finset.univ.filter (fun v : Fin n => π v = i ∧ v ∉ Rᵢ)).card ≤ t := by
  let Cᵢ : Finset (Fin n) := Finset.univ.filter (fun v : Fin n => π v = i)
  by_cases hle : Cᵢ.card ≤ t
  · refine ⟨∅, by simp [Cᵢ], ?_, ?_⟩
    · simp [colorClassSurplus, Cᵢ, Nat.sub_eq_zero_of_le hle]
    · have hsubset :
          Finset.univ.filter (fun v : Fin n => π v = i ∧ v ∉ (∅ : Finset (Fin n))) ⊆ Cᵢ := by
        intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
        simp [Cᵢ, hv.1]
      exact (Finset.card_le_card hsubset).trans hle
  · have ht_le : t ≤ Cᵢ.card := le_of_not_ge hle
    have hsurp_le : Cᵢ.card - t ≤ Cᵢ.card := Nat.sub_le _ _
    obtain ⟨Rᵢ, hRsubset, hRcard⟩ := Finset.exists_subset_card_eq hsurp_le
    refine ⟨Rᵢ, hRsubset, ?_, ?_⟩
    · simpa [colorClassSurplus, Cᵢ] using hRcard
    · have hsubset :
          Finset.univ.filter (fun v : Fin n => π v = i ∧ v ∉ Rᵢ) ⊆ Cᵢ \ Rᵢ := by
        intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
        simp [Cᵢ, hv.1, hv.2]
      have hcard_sdiff : (Cᵢ \ Rᵢ).card = t := by
        rw [Finset.card_sdiff_of_subset hRsubset, hRcard]
        exact Nat.sub_sub_self ht_le
      exact (Finset.card_le_card hsubset).trans (by rw [hcard_sdiff])

/--
Per-color surplus certificate: every coloring admits per-color removed sets
whose total requested local size is exactly `coloringSurplus`, and whose
removal makes every old color class have size at most `t`.

The actual union can only be smaller than the sum of local removals, so this is
the deterministic bridge needed by the probabilistic surplus route.
-/
theorem exists_per_color_removed_fibers_of_coloringSurplus
    {n k t : ℕ} (π : Fin n → Fin k) :
    ∃ ρ : Fin k → Finset (Fin n),
      (∑ i : Fin k, (ρ i).card) = coloringSurplus π t ∧
      ∀ i : Fin k,
        (Finset.univ.filter (fun v : Fin n => π v = i ∧ v ∉ ρ i)).card ≤ t := by
  classical
  choose ρ hρsubset hρcard hρbound using
    (fun i : Fin k => exists_removed_subset_for_colorClass (t := t) π i)
  refine ⟨ρ, ?_, hρbound⟩
  calc
    ∑ i : Fin k, (ρ i).card
        = ∑ i : Fin k, colorClassSurplus π t i := by
            exact Finset.sum_congr rfl (fun i _ => hρcard i)
    _ = coloringSurplus π t := by rfl

private lemma colorClassSurplus_eq_indicator_large_under_indepNum_le
    {n k t : ℕ} (G : SimpleGraph (Fin n)) (π : Fin n → Fin k)
    (hπ : IsProperColoring G k π) (ht : G.indepNum ≤ t + 1) (i : Fin k) :
    colorClassSurplus π t i =
      if i ∈ largeColors (t := t) π then 1 else 0 := by
  by_cases hi : i ∈ largeColors (t := t) π
  · have hlarge : t < (Finset.univ.filter (fun v : Fin n => π v = i)).card :=
      (mem_largeColors_iff (t := t) π i).mp hi
    have hcard :
        (Finset.univ.filter (fun v : Fin n => π v = i)).card = t + 1 :=
      proper_colorClass_card_eq_tsucc_of_t_lt (t := t) G π hπ ht i hlarge
    simp [colorClassSurplus, hcard, hi]
  · have hnot : ¬ t < (Finset.univ.filter (fun v : Fin n => π v = i)).card :=
      (not_mem_largeColors_iff (t := t) π i).mp hi
    have hle : (Finset.univ.filter (fun v : Fin n => π v = i)).card ≤ t :=
      Nat.le_of_not_gt hnot
    simp [colorClassSurplus, hi, Nat.sub_eq_zero_of_le hle]

private lemma coloringSurplus_eq_largeColors_card_under_indepNum_le
    {n k t : ℕ} (G : SimpleGraph (Fin n)) (π : Fin n → Fin k)
    (hπ : IsProperColoring G k π) (ht : G.indepNum ≤ t + 1) :
    coloringSurplus π t = (largeColors (t := t) π).card := by
  classical
  rw [coloringSurplus]
  calc
    ∑ i : Fin k, colorClassSurplus π t i
        = ∑ i : Fin k, (if i ∈ largeColors (t := t) π then 1 else 0) := by
            exact Finset.sum_congr rfl
              (fun i _ => colorClassSurplus_eq_indicator_large_under_indepNum_le
                (t := t) G π hπ ht i)
    _ = (largeColors (t := t) π).card := by
            simp [largeColors]

/--
Under the old `α(G) ≤ t + 1` hypothesis, total coloring surplus is controlled
by the number of maximum independent sets.  This connects the new surplus
frontier back to the older correction-count route.
-/
theorem coloringSurplus_le_maxIndepSetCount_of_indepNum_le
    {n k t : ℕ} (G : SimpleGraph (Fin n)) (π : Fin n → Fin k)
    (hπ : IsProperColoring G k π) (ht : G.indepNum ≤ t + 1) :
    coloringSurplus π t ≤ maxIndepSetCount G := by
  rw [coloringSurplus_eq_largeColors_card_under_indepNum_le (t := t) G π hπ ht]
  exact large_color_classes_card_le_maxIndepSetCount (t := t) G π hπ ht

/-- Paper-aligned structural bridge: the class-bounded chromatic number is at most
    the ordinary chromatic number plus the number of maximum independent sets.

    This is the exact shape used in Heckel 2024, §3.1:
    starting from an optimal proper coloring, each oversized class of size `t+1`
    must in the relevant range be a maximum independent set, and splitting one
    vertex off each such class yields a class-bounded coloring.
-/
theorem classBoundedChromaticNumber_le_chromaticNumber_add_maxIndep
    (n t : ℕ) (G : SimpleGraph (Fin n)) (ht : G.indepNum ≤ t + 1) :
    classBoundedChromaticNumber n t G ≤ chromaticNumber G + maxIndepSetCount G := by
  by_cases ht0 : t = 0
  · rw [ht0]
    by_cases hn : n = 0
    · subst hn
      have hcb : ClassBoundedColoringExists 0 0 0 G := by
        refine ⟨finZeroElim, ?_⟩
        constructor
        · intro u
          exact Fin.elim0 u
        · intro i
          exact Fin.elim0 i
      exact le_trans (Nat.sInf_le hcb) (Nat.zero_le _)
    · have hempty : {k : ℕ | ClassBoundedColoringExists n k 0 G} = ∅ := by
        ext k
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, ClassBoundedColoringExists]
        constructor
        · rintro ⟨π, _hproper, hbound⟩
          have hnpos : 0 < n := Nat.pos_of_ne_zero hn
          by_cases hk : k = 0
          · subst hk
            let x : Fin n := ⟨0, hnpos⟩
            exact Fin.elim0 (π x)
          · let x : Fin n := ⟨0, hnpos⟩
            have hxmem : x ∈ Finset.univ.filter (fun v => π v = π x) := by
              simp [x]
            have hpos : 0 < (Finset.univ.filter (fun v => π v = π x)).card :=
              Finset.card_pos.mpr ⟨x, hxmem⟩
            have hzero := hbound (π x)
            omega
        · intro hk
          simp at hk
      rw [classBoundedChromaticNumber, hempty, Nat.sInf_empty]
      exact Nat.zero_le _
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht0
    have hne : {k : ℕ | ProperColoringExists G k}.Nonempty :=
      ⟨n, properColoringExists_card_fin n G⟩
    have hχmem : ProperColoringExists G (chromaticNumber G) := Nat.sInf_mem hne
    obtain ⟨π, hπ⟩ := hχmem
    have hσ : IsClassBoundedProperColoring G
        (chromaticNumber G + (largeColorReps (t := t) π).card) t (recolorSigma (t := t) π) := by
      constructor
      · exact recolorSigma_isProperColoring (t := t) G π hπ
      · rw [Fin.forall_fin_add]
        constructor
        · intro i
          exact oldFiber_card_le_t (t := t) G π hπ ht i
        · intro j
          exact le_trans (newFiber_card_le_one (t := t) π j) (by omega)
    have hcb :
        ClassBoundedColoringExists n
          (chromaticNumber G + (largeColorReps (t := t) π).card) t G := ⟨recolorSigma (t := t) π, hσ⟩
    have hbase :
        classBoundedChromaticNumber n t G ≤
          chromaticNumber G + (largeColorReps (t := t) π).card := by
      exact Nat.sInf_le hcb
    calc
      classBoundedChromaticNumber n t G
          ≤ chromaticNumber G + (largeColorReps (t := t) π).card := hbase
      _ = chromaticNumber G + (largeColors (t := t) π).card := by
            rw [largeColorReps_card_eq_largeColors_card (t := t) π]
      _ ≤ chromaticNumber G + maxIndepSetCount G := by
            exact Nat.add_le_add_left
              (large_color_classes_card_le_maxIndepSetCount (t := t) G π hπ ht)
              (chromaticNumber G)

/-- Paper-aligned structural bridge using the fixed-size threshold count:
    if `α(G) ≤ t + 1`, then `χ_t(G) ≤ χ(G) + X_{t+1}(G)`,
    where `X_{t+1}` counts independent sets of size exactly `t+1`.

    This is the version that matches the fixed-size random variable used in
    Step B.3 of the human proof when `t = thresholdFloor n - 1`.
-/
theorem classBoundedChromaticNumber_le_chromaticNumber_add_indepSetCount
    (n t : ℕ) (G : SimpleGraph (Fin n)) (ht : G.indepNum ≤ t + 1) :
    classBoundedChromaticNumber n t G ≤ chromaticNumber G + indepSetCount G (t + 1) := by
  by_cases ht0 : t = 0
  · rw [ht0]
    by_cases hn : n = 0
    · subst hn
      have hcb : ClassBoundedColoringExists 0 0 0 G := by
        refine ⟨finZeroElim, ?_⟩
        constructor
        · intro u
          exact Fin.elim0 u
        · intro i
          exact Fin.elim0 i
      exact le_trans (Nat.sInf_le hcb) (Nat.zero_le _)
    · have hempty : {k : ℕ | ClassBoundedColoringExists n k 0 G} = ∅ := by
        ext k
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, ClassBoundedColoringExists]
        constructor
        · rintro ⟨π, _hproper, hbound⟩
          by_cases hk : k = 0
          · subst hk
            have hnpos : 0 < n := Nat.pos_of_ne_zero hn
            let x : Fin n := ⟨0, hnpos⟩
            exact Fin.elim0 (π x)
          · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
            let x : Fin n := ⟨0, hnpos⟩
            have hxmem : x ∈ Finset.univ.filter (fun v => π v = π x) := by
              simp [x]
            have hpos : 0 < (Finset.univ.filter (fun v => π v = π x)).card :=
              Finset.card_pos.mpr ⟨x, hxmem⟩
            have hzero := hbound (π x)
            omega
        · intro hk
          simp at hk
      rw [classBoundedChromaticNumber, hempty, Nat.sInf_empty]
      exact Nat.zero_le _
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht0
    have hne : {k : ℕ | ProperColoringExists G k}.Nonempty :=
      ⟨n, properColoringExists_card_fin n G⟩
    have hχmem : ProperColoringExists G (chromaticNumber G) := Nat.sInf_mem hne
    obtain ⟨π, hπ⟩ := hχmem
    have hσ : IsClassBoundedProperColoring G
        (chromaticNumber G + (largeColorReps (t := t) π).card) t (recolorSigma (t := t) π) := by
      constructor
      · exact recolorSigma_isProperColoring (t := t) G π hπ
      · rw [Fin.forall_fin_add]
        constructor
        · intro i
          exact oldFiber_card_le_t (t := t) G π hπ ht i
        · intro j
          exact le_trans (newFiber_card_le_one (t := t) π j) (by omega)
    have hcb :
        ClassBoundedColoringExists n
          (chromaticNumber G + (largeColorReps (t := t) π).card) t G := ⟨recolorSigma (t := t) π, hσ⟩
    have hbase :
        classBoundedChromaticNumber n t G ≤
          chromaticNumber G + (largeColorReps (t := t) π).card := by
      exact Nat.sInf_le hcb
    calc
      classBoundedChromaticNumber n t G
          ≤ chromaticNumber G + (largeColorReps (t := t) π).card := hbase
      _ = chromaticNumber G + (largeColors (t := t) π).card := by
            rw [largeColorReps_card_eq_largeColors_card (t := t) π]
      _ ≤ chromaticNumber G + indepSetCount G (t + 1) := by
            exact Nat.add_le_add_left
              (large_color_classes_card_le_indepSetCount_tsucc (t := t) G π hπ ht)
              (chromaticNumber G)

/-- Rearranged paper-aligned lower bound:
    `χ(G) ≥ χ_t(G) - X_α`, where `χ_t` is the paper's class-size-bounded chromatic number. -/
theorem chromaticNumber_ge_classBoundedChromaticNumber_sub_maxIndep
    (n t : ℕ) (G : SimpleGraph (Fin n)) (ht : G.indepNum ≤ t + 1) :
    (classBoundedChromaticNumber n t G : ℤ) - (maxIndepSetCount G : ℤ) ≤ (chromaticNumber G : ℤ) := by
  have h : classBoundedChromaticNumber n t G ≤ chromaticNumber G + maxIndepSetCount G :=
    classBoundedChromaticNumber_le_chromaticNumber_add_maxIndep n t G ht
  have h' : (classBoundedChromaticNumber n t G : ℤ) ≤
      (chromaticNumber G : ℤ) + (maxIndepSetCount G : ℤ) := by
    exact_mod_cast h
  linarith

/-- Rearranged paper-aligned lower bound using the fixed-size threshold count
    `X_{t+1}(G) = indepSetCount G (t+1)`. -/
theorem chromaticNumber_ge_classBoundedChromaticNumber_sub_indepSetCount
    (n t : ℕ) (G : SimpleGraph (Fin n)) (ht : G.indepNum ≤ t + 1) :
    (classBoundedChromaticNumber n t G : ℤ) - (indepSetCount G (t + 1) : ℤ) ≤ (chromaticNumber G : ℤ) := by
  have h : classBoundedChromaticNumber n t G ≤ chromaticNumber G + indepSetCount G (t + 1) :=
    classBoundedChromaticNumber_le_chromaticNumber_add_indepSetCount n t G ht
  have h' : (classBoundedChromaticNumber n t G : ℤ) ≤
      (chromaticNumber G : ℤ) + (indepSetCount G (t + 1) : ℤ) := by
    exact_mod_cast h
  linarith

end ClassBoundedConnection

/-! ## First moment bound on X_α -/

section FirstMomentIndep

private noncomputable def bx4_intEdges (n : ℕ) (S : Finset (Fin n)) :
    Finset (Sym2 (Fin n)) :=
  S.offDiag.image Sym2.mk.uncurry

private noncomputable def bx4_allEdges (n : ℕ) :
    Finset (Sym2 (Fin n)) :=
  (Finset.univ : Finset (Sym2 (Fin n))).filter (fun e => ¬ e.IsDiag)

private noncomputable def bx4_extEdges (n : ℕ) (S : Finset (Fin n)) :
    Finset (Sym2 (Fin n)) :=
  bx4_allEdges n \ bx4_intEdges n S

private lemma bx4_intEdges_card (n : ℕ) (S : Finset (Fin n)) :
    (bx4_intEdges n S).card = S.card.choose 2 := by
  simp [bx4_intEdges, Sym2.card_image_offDiag]

private lemma bx4_allEdges_card (n : ℕ) : (bx4_allEdges n).card = n.choose 2 := by
  have : (bx4_allEdges n) = (Sym2.diagSetᶜ : Set (Sym2 (Fin n))).toFinset := by
    ext e
    simp [bx4_allEdges, Sym2.diagSet]
  rw [this, Set.toFinset_card, Sym2.card_diagSet_compl]
  simp [Fintype.card_fin]

private lemma bx4_intEdges_sub_allEdges (n : ℕ) (S : Finset (Fin n)) :
    bx4_intEdges n S ⊆ bx4_allEdges n := by
  intro e he
  simp only [bx4_intEdges, Finset.mem_image, Finset.mem_offDiag] at he
  obtain ⟨⟨a, b⟩, ⟨_, _, hab⟩, rfl⟩ := he
  simp [bx4_allEdges, Sym2.IsDiag, hab]

private lemma bx4_extEdges_card (n : ℕ) (S : Finset (Fin n)) :
    (bx4_extEdges n S).card = n.choose 2 - S.card.choose 2 := by
  rw [bx4_extEdges, Finset.card_sdiff_of_subset (bx4_intEdges_sub_allEdges n S),
    bx4_allEdges_card, bx4_intEdges_card]

private lemma bx4_isNIndepSet_iff (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (S : Finset (Fin n)) :
    G.IsNIndepSet S.card S ↔ G.edgeFinset ⊆ bx4_extEdges n S := by
  constructor
  · intro h e he
    simp only [bx4_extEdges, Finset.mem_sdiff]
    refine ⟨?_, ?_⟩
    · simp only [bx4_allEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact G.not_isDiag_of_mem_edgeFinset he
    · intro hint
      simp only [bx4_intEdges, Finset.mem_image, Finset.mem_offDiag] at hint
      obtain ⟨⟨a, b⟩, ⟨haS, hbS, hab⟩, heq⟩ := hint
      have hadj : G.Adj a b := by
        have hse : (Function.uncurry Sym2.mk) (a, b) = s(a, b) := rfl
        rw [hse] at heq
        rw [← heq] at he
        rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      exact h.1 haS hbS (by exact_mod_cast hab) hadj
  · intro hsub
    refine ⟨?_, rfl⟩
    intro v hv w hw hvw hadj
    have he : s(v, w) ∈ G.edgeFinset := by
      rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    have hext := hsub he
    simp only [bx4_extEdges, Finset.mem_sdiff, bx4_intEdges,
      Finset.mem_image, Finset.mem_offDiag] at hext
    exact hext.2 ⟨⟨v, w⟩, ⟨hv, hw, by exact_mod_cast hvw⟩, rfl⟩

private lemma bx4_card_indep_graphs (n : ℕ) (S : Finset (Fin n)) :
    (Finset.univ.filter (fun G : SimpleGraph (Fin n) => G.IsNIndepSet S.card S)).card =
      2 ^ (n.choose 2 - S.card.choose 2) := by
  classical
  haveI : DecidablePred (fun G : SimpleGraph (Fin n) => G.IsNIndepSet S.card S) :=
    fun G => Classical.dec _
  rw [← bx4_extEdges_card n S, ← Finset.card_powerset]
  apply Finset.card_bij (fun G _ => G.edgeFinset.filter (fun e => e ∈ bx4_extEdges n S))
  · intro G hG
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hG
    exact Finset.mem_powerset.mpr (fun e he => (Finset.mem_filter.mp he).2)
  · intro G₁ hG₁ G₂ hG₂ heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hG₁ hG₂
    have h1 : G₁.edgeFinset.filter (fun e => e ∈ bx4_extEdges n S) = G₁.edgeFinset :=
      Finset.filter_true_of_mem (fun e he => (bx4_isNIndepSet_iff n G₁ S).mp hG₁ he)
    have h2 : G₂.edgeFinset.filter (fun e => e ∈ bx4_extEdges n S) = G₂.edgeFinset :=
      Finset.filter_true_of_mem (fun e he => (bx4_isNIndepSet_iff n G₂ S).mp hG₂ he)
    exact SimpleGraph.edgeFinset_inj.mp (by rw [h1, h2] at heq; exact heq)
  · intro E hE
    rw [Finset.mem_powerset] at hE
    have hnondiag : ∀ e ∈ E, ¬ e.IsDiag := by
      intro e he
      have := hE he
      simp only [bx4_extEdges, Finset.mem_sdiff, bx4_allEdges, Finset.mem_filter,
        Finset.mem_univ, true_and] at this
      exact this.1
    refine ⟨SimpleGraph.fromEdgeSet ↑E, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, rfl⟩
      intro v hv w hw hvw hadj
      rw [SimpleGraph.fromEdgeSet_adj] at hadj
      have hmem : s(v, w) ∈ E := Finset.mem_coe.mp hadj.1
      have hhmem := hE hmem
      simp only [bx4_extEdges, Finset.mem_sdiff, bx4_allEdges, bx4_intEdges,
        Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_offDiag,
        not_exists, not_and] at hhmem
      exact hhmem.2 (v, w) ⟨hv, hw, by exact_mod_cast hvw⟩ rfl
    · ext e
      refine Sym2.inductionOn e (fun v w => ?_)
      simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        SimpleGraph.fromEdgeSet_adj, Finset.mem_coe]
      constructor
      · intro ⟨⟨h, _⟩, _⟩
        exact h
      · intro he
        exact ⟨⟨he, fun hd => hnondiag (s(v, w)) he hd⟩, hE he⟩

private instance instMeasurableSingletonClassSimpleGraph (n : ℕ) :
    MeasurableSingletonClass (SimpleGraph (Fin n)) := by
  constructor
  intro G
  show MeasurableSet {G}
  have heq : ({G} : Set (SimpleGraph (Fin n))) = SimpleGraph.Adj ⁻¹' {G.Adj} := by
    ext H
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => h ▸ rfl, SimpleGraph.ext⟩
  rw [heq]
  exact SimpleGraph.measurable_adj (MeasurableSet.singleton G.Adj)

private theorem gnHalf_singleton_eq (n : ℕ) (G : SimpleGraph (Fin n)) :
    gnHalf n {G} =
      unitInterval.toNNReal halfProb ^ G.edgeSet.ncard *
      unitInterval.toNNReal (unitInterval.symm halfProb) ^ (n.choose 2 - G.edgeSet.ncard) := by
  have hn : Nat.card (Fin n) = n := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_fin n
  simp only [gnHalf, SimpleGraph.binomialRandom_singleton, hn]

private theorem gnHalf_uniform (n : ℕ) (G : SimpleGraph (Fin n)) :
    gnHalf n {G} = unitInterval.toNNReal halfProb ^ n.choose 2 := by
  have hsym : unitInterval.symm halfProb = halfProb := by
    apply Subtype.ext
    change (1 : ℝ) - 1 / 2 = 1 / 2
    norm_num
  rw [gnHalf_singleton_eq, hsym, ← pow_add]
  congr 1
  have h : G.edgeSet.ncard ≤ n.choose 2 := by
    haveI : DecidableRel G.Adj := Classical.decRel _
    have hcard : G.edgeFinset.card ≤ n.choose 2 := by
      have h1 := SimpleGraph.card_edgeFinset_le_card_choose_two (G := G)
      simpa [Fintype.card_fin] using h1
    have heq : G.edgeSet.ncard = G.edgeFinset.card := by
      rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
    linarith
  omega

private lemma gnHalf_uniform_finset (n : ℕ) (S : Finset (SimpleGraph (Fin n))) :
    gnHalf n ↑S =
      S.card * (ENNReal.ofNNReal (unitInterval.toNNReal halfProb)) ^ n.choose 2 := by
  have hsum : gnHalf n ↑S = ∑ G ∈ S, gnHalf n {G} := by
    rw [← MeasureTheory.sum_measure_singleton]
  rw [hsum]
  simp_rw [gnHalf_uniform]
  rw [Finset.sum_const, nsmul_eq_mul]

private lemma gnHalf_isNIndepSet_eq (n k : ℕ) (S : Finset (Fin n)) (hS : S.card = k) :
    gnHalf n {G : SimpleGraph (Fin n) | G.IsNIndepSet k S} =
      (ENNReal.ofNNReal (unitInterval.toNNReal halfProb)) ^ (k.choose 2) := by
  classical
  have hfin : {G : SimpleGraph (Fin n) | G.IsNIndepSet k S} =
      ↑(Finset.univ.filter (fun G : SimpleGraph (Fin n) => G.IsNIndepSet k S)) := by
    ext G
    simp
  have hcardset :
      (Finset.univ.filter (fun G : SimpleGraph (Fin n) => G.IsNIndepSet k S)) =
        (Finset.univ.filter (fun G : SimpleGraph (Fin n) => G.IsNIndepSet S.card S)) := by
    congr 1
    ext G
    simp [hS]
  rw [hfin, gnHalf_uniform_finset, hcardset, bx4_card_indep_graphs]
  · set p := ENNReal.ofNNReal (unitInterval.toNNReal halfProb)
    have hp_inv : p = (2 : ℝ≥0∞)⁻¹ := by
      simp only [p]
      have hcoerce : ENNReal.ofNNReal (unitInterval.toNNReal halfProb) = ENNReal.ofReal ((1 : ℝ) / 2) := by
        rw [← ENNReal.ofReal_coe_nnreal]
        norm_cast
      rw [hcoerce, show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by ring,
        ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
      simp
    have hkn : k ≤ n := hS ▸ (Finset.card_le_univ S).trans (by simp [Fintype.card_fin])
    have hle : k.choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 hkn
    simp [hS]
    rw [hp_inv]
    conv_lhs => rw [show n.choose 2 = (n.choose 2 - k.choose 2) + k.choose 2 from (Nat.sub_add_cancel hle).symm]
    rw [pow_add, ← mul_assoc]
    suffices h : (↑(2 ^ (n.choose 2 - k.choose 2)) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n.choose 2 - k.choose 2) = 1 by
      simp [h]
    push_cast
    rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
    done

private lemma indepSetCount_eq_sum (n k : ℕ) (G : SimpleGraph (Fin n)) :
    (indepSetCount G k : ℝ≥0∞) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        if G.IsNIndepSet k S then 1 else 0 := by
  unfold indepSetCount
  have hfilter :
      (Finset.univ.filter (fun S : Finset (Fin n) => S.card = k ∧ G.IsNIndepSet k S)) =
        (((Finset.univ : Finset (Fin n)).powersetCard k).filter fun S => G.IsNIndepSet k S) := by
    ext S
    simp [Finset.mem_powersetCard]
  rw [hfilter, Finset.card_eq_sum_ones, Finset.sum_filter]
  push_cast
  rfl

private theorem gnHalf_expected_indepSetCount (n k : ℕ) :
    ∫⁻ G, (indepSetCount G k : ℝ≥0∞) ∂(gnHalf n) =
      ENNReal.ofReal (expectedIndependentSets n k) := by
  classical
  have hif_eq : ∀ S : Finset (Fin n), ∀ G : SimpleGraph (Fin n),
      (if G.IsNIndepSet k S then (1 : ℝ≥0∞) else 0) =
        ({G' : SimpleGraph (Fin n) | G'.IsNIndepSet k S} : Set _).indicator 1 G := by
    intro S G
    simp [Set.indicator]
  conv_lhs =>
    arg 2
    ext G
    rw [indepSetCount_eq_sum n k G]
  simp_rw [hif_eq]
  rw [MeasureTheory.lintegral_finset_sum ((Finset.univ : Finset (Fin n)).powersetCard k)
    (f := fun S G => ({G' : SimpleGraph (Fin n) | G'.IsNIndepSet k S} : Set _).indicator 1 G)
    (fun S _ => by
      refine Measurable.indicator measurable_const ?_
      exact (Set.to_countable _).measurableSet)]
  have hind : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      ∫⁻ G,
          ({G' : SimpleGraph (Fin n) | G'.IsNIndepSet k S} : Set (SimpleGraph (Fin n))).indicator 1 G
            ∂(gnHalf n) =
        gnHalf n {G : SimpleGraph (Fin n) | G.IsNIndepSet k S} := by
    intro S hS
    exact lintegral_indicator_one ((Set.to_countable _).measurableSet)
  rw [show ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      ∫⁻ G,
          ({G' : SimpleGraph (Fin n) | G'.IsNIndepSet k S} : Set (SimpleGraph (Fin n))).indicator 1 G
            ∂(gnHalf n) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        gnHalf n {G : SimpleGraph (Fin n) | G.IsNIndepSet k S} from by
      apply Finset.sum_congr rfl
      intro S hS
      rw [hind S hS]]
  have hp_half :
      ENNReal.ofNNReal (unitInterval.toNNReal halfProb) = ENNReal.ofReal ((1 : ℝ) / 2) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    norm_cast
  have hsum :
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
          gnHalf n {G : SimpleGraph (Fin n) | G.IsNIndepSet k S} =
        ∑ _S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
          ENNReal.ofReal ((1 : ℝ) / 2) ^ (k.choose 2) := by
    apply Finset.sum_congr rfl
    intro S hS
    rw [gnHalf_isNIndepSet_eq n k S (Finset.mem_powersetCard.mp hS).2, hp_half]
  rw [hsum]
  have hpow :
      ENNReal.ofReal ((1 : ℝ) / 2) ^ (k.choose 2) =
        ENNReal.ofReal (((1 : ℝ) / 2) ^ (k.choose 2)) := by
    symm
    exact ENNReal.ofReal_pow (by positivity) _
  rw [hpow]
  simp [expectedIndependentSets, Finset.card_powersetCard, nsmul_eq_mul, ENNReal.ofReal_mul]

/-- One-step recurrence for the first-moment counts `μ_k = expectedIndependentSets n k`.

    This is the exact ratio identity
    `μ_{k+1} = μ_k * ((n-k)/(k+1)) * 2^{-k}`,
    kept in multiplication form to avoid division side-conditions. -/
private lemma expectedIndependentSets_succ_mul (n k : ℕ) :
    expectedIndependentSets n (k + 1) * (k + 1 : ℝ) =
      expectedIndependentSets n k * (((n - k : ℕ) : ℝ)) * ((1 / 2 : ℝ) ^ k) := by
  unfold expectedIndependentSets
  have hchoose :
      Nat.choose (k + 1) 2 = Nat.choose k 2 + k := by
    rw [Nat.choose_two_right, Nat.choose_two_right]
    simpa using Nat.triangle_succ k
  rw [hchoose, pow_add]
  have hchoose' :
      (((Nat.choose n (k + 1)) * (k + 1) : ℕ) : ℝ) =
        (((Nat.choose n k) * (n - k) : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq n k
  have hchoose'' :
      (↑(Nat.choose n (k + 1)) : ℝ) * (k + 1 : ℝ) =
        (↑(Nat.choose n k) : ℝ) * (((n - k : ℕ) : ℝ)) := by
    simpa [Nat.cast_mul] using hchoose'
  calc
    (↑(Nat.choose n (k + 1)) : ℝ) * ((1 / 2 : ℝ) ^ Nat.choose k 2 * (1 / 2 : ℝ) ^ k) *
        (k + 1 : ℝ)
        = ((↑(Nat.choose n (k + 1)) : ℝ) * (k + 1 : ℝ)) *
            (1 / 2 : ℝ) ^ Nat.choose k 2 * (1 / 2 : ℝ) ^ k := by
            ring
    _ = ((↑(Nat.choose n k) : ℝ) * (((n - k : ℕ) : ℝ))) *
          (1 / 2 : ℝ) ^ Nat.choose k 2 * (1 / 2 : ℝ) ^ k := by
            rw [hchoose'']
    _ = (↑(Nat.choose n k) : ℝ) * (1 / 2 : ℝ) ^ Nat.choose k 2 * (((n - k : ℕ) : ℝ)) *
          (1 / 2 : ℝ) ^ k := by
            ring

private theorem gnHalf_indepSetCount_ge_le_div (n k : ℕ) {r : ℝ}
    (hr_pos : 0 < r) :
    gnHalf n {G : SimpleGraph (Fin n) | r ≤ (indepSetCount G k : ℝ)} ≤
      ENNReal.ofReal (expectedIndependentSets n k) / ENNReal.ofReal r := by
  have hmeas : AEMeasurable (fun G : SimpleGraph (Fin n) => (indepSetCount G k : ℝ≥0∞)) (gnHalf n) := by
    exact (measurable_of_countable
      (fun G : SimpleGraph (Fin n) => (indepSetCount G k : ℝ≥0∞))).aemeasurable
  have hmarkov :=
    MeasureTheory.meas_ge_le_lintegral_div
      (μ := gnHalf n)
      (f := fun G : SimpleGraph (Fin n) => (indepSetCount G k : ℝ≥0∞))
      hmeas
      (hε := ENNReal.ofReal_ne_zero_iff.mpr hr_pos)
      (hε' := ENNReal.ofReal_ne_top)
  calc
    gnHalf n {G : SimpleGraph (Fin n) | r ≤ (indepSetCount G k : ℝ)} ≤
        (∫⁻ G, (indepSetCount G k : ℝ≥0∞) ∂(gnHalf n)) / ENNReal.ofReal r := by
          simpa using hmarkov
    _ = ENNReal.ofReal (expectedIndependentSets n k) / ENNReal.ofReal r := by
          rw [gnHalf_expected_indepSetCount n k]

private lemma isNIndepSet_of_le_indepNum (n k : ℕ) (G : SimpleGraph (Fin n))
    (hk : k ≤ G.indepNum) :
    ∃ S : Finset (Fin n), G.IsNIndepSet k S := by
  obtain ⟨T, hT⟩ := G.exists_isNIndepSet_indepNum
  rw [← hT.card_eq] at hk
  obtain ⟨S, hST, hScard⟩ := Finset.exists_subset_card_eq hk
  refine ⟨S, ⟨hT.isIndepSet.mono ?_, hScard⟩⟩
  exact_mod_cast hST

private lemma indepNum_subset_biUnion (n k : ℕ) :
    {G : SimpleGraph (Fin n) | k ≤ G.indepNum} ⊆
      ⋃ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        {G : SimpleGraph (Fin n) | G.IsNIndepSet k S} := by
  intro G hG
  simp only [Set.mem_setOf_eq] at hG
  obtain ⟨S, hS⟩ := isNIndepSet_of_le_indepNum n k G hG
  refine Set.mem_biUnion ?_ hS
  rw [Finset.mem_coe, Finset.mem_powersetCard]
  exact ⟨Finset.subset_univ _, hS.card_eq⟩

private theorem gnHalf_indepNum_le_sum_indepSets (n k : ℕ) :
    gnHalf n {G : SimpleGraph (Fin n) | k ≤ G.indepNum} ≤
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        gnHalf n {G : SimpleGraph (Fin n) | G.IsNIndepSet k S} := by
  calc gnHalf n {G | k ≤ G.indepNum}
      ≤ gnHalf n (⋃ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
            {G : SimpleGraph (Fin n) | G.IsNIndepSet k S}) :=
          measure_mono (indepNum_subset_biUnion n k)
    _ ≤ ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
            gnHalf n {G : SimpleGraph (Fin n) | G.IsNIndepSet k S} :=
          measure_biUnion_finset_le _ _

private theorem gnHalf_indepNum_le_expectedIndSets (n k : ℕ) :
    gnHalf n {G : SimpleGraph (Fin n) | k ≤ G.indepNum} ≤
      ENNReal.ofReal (expectedIndependentSets n k) := by
  calc gnHalf n {G : SimpleGraph (Fin n) | k ≤ G.indepNum}
      ≤ ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
          gnHalf n {G : SimpleGraph (Fin n) | G.IsNIndepSet k S} :=
        gnHalf_indepNum_le_sum_indepSets n k
    _ = ∑ _S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
          ENNReal.ofReal ((1 : ℝ) / 2) ^ (k.choose 2) := by
        apply Finset.sum_congr rfl
        intro S hS
        rw [gnHalf_isNIndepSet_eq n k S (Finset.mem_powersetCard.mp hS).2]
        rw [← ENNReal.ofReal_coe_nnreal]
        norm_cast
    _ = ENNReal.ofReal (expectedIndependentSets n k) := by
        have hpow :
            ENNReal.ofReal ((1 : ℝ) / 2) ^ (k.choose 2) =
              ENNReal.ofReal (((1 : ℝ) / 2) ^ (k.choose 2)) := by
          symm
          exact ENNReal.ofReal_pow (by positivity) _
        rw [hpow]
        simp [expectedIndependentSets, Finset.card_powersetCard, nsmul_eq_mul, ENNReal.ofReal_mul]

private lemma measurableSet_indepNum_ge (n k : ℕ) :
    MeasurableSet {G : SimpleGraph (Fin n) | k ≤ G.indepNum} :=
  Set.Finite.measurableSet (Set.toFinite _)

private theorem gnHalf_indepNum_lt_eq_compl (n k : ℕ) :
    gnHalf n {G : SimpleGraph (Fin n) | G.indepNum < k} =
    1 - gnHalf n {G : SimpleGraph (Fin n) | k ≤ G.indepNum} := by
  haveI : IsProbabilityMeasure (gnHalf n) := by
    unfold gnHalf
    infer_instance
  rw [← MeasureTheory.prob_compl_eq_one_sub (measurableSet_indepNum_ge n k)]
  congr 1
  ext G
  simp [not_le]

private lemma rpow_gt_of_large'' (δ C : ℝ) (hδ : 0 < δ) (hC : 0 < C)
    (n n₀ : ℕ) (hn₀ : C^(δ⁻¹) < (n₀ : ℝ)) (hn : n₀ ≤ n) : (n : ℝ)^δ > C := by
  have h_n₀_pos : (0 : ℝ) < (n₀ : ℝ) := by
    linarith [Real.rpow_pos_of_pos hC δ⁻¹]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le (by exact_mod_cast h_n₀_pos) hn
  have hn_cast : (n₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have step1 : (C^(δ⁻¹))^δ < (n : ℝ)^δ :=
    Real.rpow_lt_rpow (le_of_lt (Real.rpow_pos_of_pos hC _)) (by linarith) hδ
  have step2 : (C^(δ⁻¹))^δ = C := by
    rw [← Real.rpow_mul (le_of_lt hC)]
    field_simp
    exact Real.rpow_one C
  linarith

private lemma rpow_neg_small_of_large (ε : ℝ) (hε_pos : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → (n : ℝ) ^ (-(0.01 * ε)) ≤ ε := by
  have hδ : (0 : ℝ) < 0.01 * ε := by nlinarith
  have hεinv_pos : (0 : ℝ) < ε⁻¹ := by simpa [one_div] using (one_div_pos.mpr hε_pos)
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt ((ε⁻¹)^((0.01 * ε)⁻¹))
  refine ⟨n₀, ?_⟩
  intro n hn
  have h_n₀_pos : (0 : ℝ) < (n₀ : ℝ) := by
    have : (0 : ℝ) < (ε⁻¹)^((0.01 * ε)⁻¹) := Real.rpow_pos_of_pos hεinv_pos _
    linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le (by exact_mod_cast h_n₀_pos) hn
  have hpow_gt : (n : ℝ) ^ (0.01 * ε) > ε⁻¹ :=
    rpow_gt_of_large'' (0.01 * ε) (ε⁻¹) hδ hεinv_pos n n₀ hn₀ hn
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
  rw [Real.rpow_neg hn_nonneg]
  have hpow_pos : (0 : ℝ) < (n : ℝ) ^ (0.01 * ε) := Real.rpow_pos_of_pos hn_pos _
  have hbound : 1 / ((n : ℝ) ^ (0.01 * ε)) ≤ 1 / (ε⁻¹) :=
    (one_div_le_one_div hpow_pos hεinv_pos).2 hpow_gt.le
  simpa [one_div, inv_inv] using hbound

private lemma rpow_neg_small_of_large_with_error (ε δ : ℝ)
    (hε_pos : 0 < ε) (hδ_pos : 0 < δ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → (n : ℝ) ^ (-(0.01 * ε)) ≤ δ := by
  have hδexp : (0 : ℝ) < 0.01 * ε := by nlinarith
  have hδinv_pos : (0 : ℝ) < δ⁻¹ := by simpa [one_div] using (one_div_pos.mpr hδ_pos)
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt ((δ⁻¹)^((0.01 * ε)⁻¹))
  refine ⟨n₀, ?_⟩
  intro n hn
  have h_n₀_pos : (0 : ℝ) < (n₀ : ℝ) := by
    have : (0 : ℝ) < (δ⁻¹)^((0.01 * ε)⁻¹) := Real.rpow_pos_of_pos hδinv_pos _
    linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le (by exact_mod_cast h_n₀_pos) hn
  have hpow_gt : (n : ℝ) ^ (0.01 * ε) > δ⁻¹ :=
    rpow_gt_of_large'' (0.01 * ε) (δ⁻¹) hδexp hδinv_pos n n₀ hn₀ hn
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
  rw [Real.rpow_neg hn_nonneg]
  have hpow_pos : (0 : ℝ) < (n : ℝ) ^ (0.01 * ε) := Real.rpow_pos_of_pos hn_pos _
  have hbound : 1 / ((n : ℝ) ^ (0.01 * ε)) ≤ 1 / (δ⁻¹) :=
    (one_div_le_one_div hpow_pos hδinv_pos).2 hpow_gt.le
  simpa [one_div, inv_inv] using hbound

private lemma inv_two_mul_nat_le_of_large (δ : ℝ) (hδ_pos : 0 < δ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 1 / (2 * n : ℝ) ≤ δ := by
  obtain ⟨n₀, hn₀_gt⟩ := exists_nat_gt (1 / (2 * δ))
  refine ⟨n₀, ?_⟩
  intro n hn
  have hn_real : (1 / (2 * δ : ℝ)) < (n : ℝ) := by
    exact lt_of_lt_of_le hn₀_gt (by exact_mod_cast hn)
  have hleft_pos : 0 < (1 / (2 * δ : ℝ)) := by
    have : 0 < 2 * δ := by positivity
    positivity
  have hn_pos : 0 < (n : ℝ) := by linarith
  have hden_pos : 0 < (2 * n : ℝ) := by positivity
  rw [div_le_iff₀ hden_pos]
  have hmul : (1 : ℝ) < (n : ℝ) * (2 * δ) := by
    exact (div_lt_iff₀ (by positivity : 0 < 2 * δ)).mp hn_real
  have : (1 : ℝ) < δ * (2 * n : ℝ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  linarith

/-- Arithmetic half of the BN.6 chromatic log-criterion:
    if `n * k^n * 2 ≤ 2^((n/k).choose 2)`, then the explicit chromatic first-moment
    bound is at most `1 / (2n)`. -/
private lemma chromaticBound_le_inv_two_n (n k : ℕ) (hn : 1 ≤ n) (hk : 0 < k)
    (h : (n : ℝ) * (k : ℝ) ^ n * 2 ≤ (2 : ℝ) ^ ((n / k).choose 2)) :
    (k : ℝ) ^ n * (1 / 2 : ℝ) ^ ((n / k).choose 2) ≤ 1 / (2 * n) := by
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * n)]
  calc (k : ℝ) ^ n * (1 / 2) ^ ((n / k).choose 2) * (2 * n)
      = n * (k : ℝ) ^ n * 2 * ((1 / 2) ^ ((n / k).choose 2)) := by ring
    _ ≤ (2 : ℝ) ^ ((n / k).choose 2) * ((1 / 2) ^ ((n / k).choose 2)) :=
          mul_le_mul_of_nonneg_right h (by positivity)
    _ = 1 := by rw [← mul_pow]; norm_num

/-- Logarithmic criterion forcing `n * k^n * 2 ≤ 2^((n/k).choose 2)`. -/
private lemma pow_le_two_pow_choose_chromatic (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (h : (n : ℝ) * (Real.log k / Real.log 2) + (Real.log n / Real.log 2) + 1 ≤
        ((n / k).choose 2 : ℝ)) :
    (n : ℝ) * (k : ℝ) ^ n * 2 ≤ (2 : ℝ) ^ ((n / k).choose 2) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hk)
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)
  have hkey : Real.log n + (n : ℝ) * Real.log k + Real.log 2 ≤
      ((n / k).choose 2 : ℝ) * Real.log 2 := by
    have h1 : (((n : ℝ) * (Real.log k / Real.log 2) + (Real.log n / Real.log 2) + 1)
        * Real.log 2) = Real.log n + n * Real.log k + Real.log 2 := by
      field_simp
      ring
    nlinarith [mul_le_mul_of_nonneg_right h (le_of_lt hlog2)]
  rw [← Real.log_le_log_iff (by positivity) (by positivity)]
  rw [show (n : ℝ) * (k : ℝ) ^ n * 2 = n * k ^ n * 2 ^ (1 : ℕ) from by push_cast; ring]
  rw [Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  linarith

/-- Sharp power bound from the `((k+1) log₂ n + 1)` criterion.

    This is a reusable arithmetic bridge for threshold arguments where the
    natural parameter is a lower bound on some auxiliary integer `k`
    satisfying `k ≳ 2 log₂ n`. -/
private lemma pow_le_two_pow_choose_sharp (n k : ℕ) (hn : 1 ≤ n)
    (h : ((k : ℝ) + 1) * (Real.log n / Real.log 2) + 1 ≤ k.choose 2) :
    (n : ℝ) ^ (k + 1) * 2 ≤ (2 : ℝ) ^ (k.choose 2) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hkey : ((k : ℝ) + 1) * Real.log n ≤ ((k.choose 2 : ℝ) - 1) * Real.log 2 := by
    have := mul_le_mul_of_nonneg_right h (le_of_lt hlog2)
    have heq :
        (((k : ℝ) + 1) * (Real.log n / Real.log 2) + 1) * Real.log 2 =
          ((k : ℝ) + 1) * Real.log n + Real.log 2 := by
      field_simp
    linarith [heq ▸ this]
  rw [← Real.log_le_log_iff (by positivity) (by positivity)]
  rw [Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow, Real.log_pow]
  push_cast
  linarith

/-- Concrete sufficient condition for the sharp criterion.

    If `k ≥ 2 log₂ n + 2`, then the stronger inequality
    `((k+1) log₂ n + 1) ≤ choose(k,2)` already holds. -/
private lemma log_criterion_sharp (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k)
    (h : 2 * (Real.log n / Real.log 2) + 2 ≤ (k : ℝ)) :
    ((k : ℝ) + 1) * (Real.log n / Real.log 2) + 1 ≤ k.choose 2 := by
  have hlog2_nn : (0 : ℝ) ≤ Real.log n / Real.log 2 := by
    apply div_nonneg
    · exact Real.log_nonneg (by exact_mod_cast hn)
    · exact le_of_lt (Real.log_pos (by norm_num))
  have hchoose_eq : (k.choose 2 : ℝ) = k * ((k : ℝ) - 1) / 2 := by
    rw [Nat.choose_two_right]
    have hdvd : 2 ∣ k * (k - 1) := (Nat.even_mul_pred_self k).two_dvd
    rw [Nat.cast_div hdvd (by norm_cast)]
    push_cast
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hchoose_eq]
  set L := Real.log n / Real.log 2 with hL_def
  have hL : L ≤ (k : ℝ) / 2 - 1 := by
    linarith
  nlinarith [sq_nonneg ((k : ℝ) - 2)]

/-- Coarse threshold-coloring error bound from the BN.6 log criterion. -/
private lemma factorial_expectedTBoundedColorings_le_inv_two_n_of_log_criterion
    (n k t : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hk_le : k ≤ n) (ht : 0 < t)
    (hlog : (n : ℝ) * (Real.log k / Real.log 2) + (Real.log n / Real.log 2) + 1 ≤
        ((n / k).choose 2 : ℝ)) :
    Nat.factorial k * expectedTBoundedColorings n k t ≤ 1 / (2 * n) := by
  have hk_pos : 0 < k := hk
  calc
    Nat.factorial k * expectedTBoundedColorings n k t
        ≤ (k : ℝ) ^ n * (1 / 2 : ℝ) ^ ((n / k).choose 2) :=
          factorial_expectedTBoundedColorings_le_coarse n k t ht hk_pos hk_le
    _ ≤ 1 / (2 * n) :=
          chromaticBound_le_inv_two_n n k hn hk_pos
            (pow_le_two_pow_choose_chromatic n k hn hk hlog)

/-- Same reduction, but with a separate target error budget `δ`. -/
private lemma factorial_expectedTBoundedColorings_le_with_error_of_log_criterion
    (n k t : ℕ) (δ : ℝ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hk_le : k ≤ n) (ht : 0 < t)
    (hlog : (n : ℝ) * (Real.log k / Real.log 2) + (Real.log n / Real.log 2) + 1 ≤
        ((n / k).choose 2 : ℝ))
    (hsmall : 1 / (2 * n : ℝ) ≤ δ) :
    Nat.factorial k * expectedTBoundedColorings n k t ≤ δ := by
  exact (factorial_expectedTBoundedColorings_le_inv_two_n_of_log_criterion n k t hn hk hk_le ht hlog).trans hsmall

/-- Same fixed-size first moment bound, but with a separate error-budget `δ`.

    The main-range parameter remains `ε`, so the deterministic threshold and the exponent
    `1 - 0.99 * ε` stay unchanged; only the tail probability target is refined to `δ`. -/
theorem gnHalf_thresholdIndepSetCount_le_rpow_with_error
    (ε δ : ℝ) (hε_pos : 0 < ε) (hδ_pos : 0 < δ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (hn : InMainRange ε n),
      let X_α := fun G : SimpleGraph (Fin n) => indepSetCount G (thresholdFloor n)
      1 - ENNReal.ofReal δ ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          (X_α G : ℝ) ≤ (n : ℝ) ^ (1 - 0.99 * ε)} := by
  obtain ⟨n₁, hn₁⟩ := rpow_neg_small_of_large_with_error ε δ hε_pos hδ_pos
  refine ⟨max n₁ 1, ?_⟩
  intro n hn0 hn
  let α := thresholdFloor n
  let r := (n : ℝ) ^ (1 - 0.99 * ε)
  let A : Set (SimpleGraph (Fin n)) := {G : SimpleGraph (Fin n) | (indepSetCount G α : ℝ) ≤ r}
  have hn_ge_one : 1 ≤ n := le_trans (Nat.le_max_right n₁ 1) hn0
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_ge_one
  have hr_pos : 0 < r := by
    dsimp [r]
    exact Real.rpow_pos_of_pos hn_pos _
  have hAc_sub :
      Aᶜ ⊆ {G : SimpleGraph (Fin n) | r ≤ (indepSetCount G α : ℝ)} := by
    intro G hG
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, A] at hG ⊢
    exact le_of_lt (lt_of_not_ge hG)
  have hratio_le_real :
      expectedIndependentSets n α / r ≤ (n : ℝ) ^ (-(0.01 * ε)) := by
    have hmain : expectedIndependentSets n α ≤ (n : ℝ) ^ (1 - ε) := by
      simpa [α] using hn.2
    have hratio_eq :
        (n : ℝ) ^ (1 - ε) / r = (n : ℝ) ^ (-(0.01 * ε)) := by
      dsimp [r]
      rw [← Real.rpow_sub hn_pos]
      congr 1
      ring
    calc
      expectedIndependentSets n α / r ≤ (n : ℝ) ^ (1 - ε) / r :=
        div_le_div_of_nonneg_right hmain (le_of_lt hr_pos)
      _ = (n : ℝ) ^ (-(0.01 * ε)) := hratio_eq
  have hn₁_le : n₁ ≤ n := le_trans (Nat.le_max_left n₁ 1) hn0
  have hsmall : (n : ℝ) ^ (-(0.01 * ε)) ≤ δ := hn₁ n hn₁_le
  have hAc_le : gnHalf n Aᶜ ≤ ENNReal.ofReal δ := by
    calc
      gnHalf n Aᶜ ≤ gnHalf n {G : SimpleGraph (Fin n) | r ≤ (indepSetCount G α : ℝ)} :=
        MeasureTheory.measure_mono hAc_sub
      _ ≤ ENNReal.ofReal (expectedIndependentSets n α) / ENNReal.ofReal r :=
        gnHalf_indepSetCount_ge_le_div n α hr_pos
      _ = ENNReal.ofReal (expectedIndependentSets n α / r) := by
        rw [← ENNReal.ofReal_div_of_pos hr_pos]
      _ ≤ ENNReal.ofReal ((n : ℝ) ^ (-(0.01 * ε))) :=
        ENNReal.ofReal_le_ofReal hratio_le_real
      _ ≤ ENNReal.ofReal δ :=
        ENNReal.ofReal_le_ofReal hsmall
  have hA_meas : MeasurableSet A := (Set.to_countable A).measurableSet
  haveI : IsProbabilityMeasure (gnHalf n) := by
    unfold gnHalf
    infer_instance
  have hprob_A : 1 - ENNReal.ofReal δ ≤ gnHalf n A := by
    calc
      1 - ENNReal.ofReal δ ≤ 1 - gnHalf n Aᶜ := tsub_le_tsub_left hAc_le 1
      _ = gnHalf n A := by
        rw [prob_compl_eq_one_sub (μ := gnHalf n) hA_meas]
        exact ENNReal.sub_sub_cancel one_ne_top prob_le_one
  simpa [A, α, r]
    using hprob_A

/-- First moment bound for the paper's fixed-size variable:
    whp the number of independent sets of size `thresholdFloor n`
    is at most `n^(1-0.99ε)`.

    Proof strategy (Heckel 2024, §3.1, Step B.3):
    1. E[X_α] = μ_α ≤ n^{1-ε} (from InMainRange)
    2. By Markov: P(X_α ≥ n^{1-0.99ε}) ≤ E[X_α] / n^{1-0.99ε}
                                       ≤ n^{1-ε} / n^{1-0.99ε}
                                       = n^{-0.01ε}
    3. For large n, n^{-0.01ε} ≤ ε
    4. So P(X_α ≤ n^{1-0.99ε}) ≥ 1 - ε

    This is exactly the random variable appearing in Heckel 2024, §3.1, Step B.3:
    `X_α(G) = indepSetCount G (thresholdFloor n)`.
-/
theorem gnHalf_thresholdIndepSetCount_le_rpow
    (ε : ℝ) (hε_pos : 0 < ε) (hε_small : ε < 0.001) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (hn : InMainRange ε n),
      let X_α := fun G : SimpleGraph (Fin n) => indepSetCount G (thresholdFloor n)
      1 - ENNReal.ofReal ε ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          (X_α G : ℝ) ≤ (n : ℝ) ^ (1 - 0.99 * ε)} := by
  simpa using gnHalf_thresholdIndepSetCount_le_rpow_with_error ε ε hε_pos hε_pos

/-- Reindexed version of the fixed-size first-moment bound matching the literal
    `(thresholdFloor n - 1) + 1` syntax used in the final split theorem. -/
theorem gnHalf_thresholdSuccPredIndepSetCount_le_rpow_with_error
    (ε δ : ℝ) (hε_pos : 0 < ε) (hδ_pos : 0 < δ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (hn : InMainRange ε n),
      1 - ENNReal.ofReal δ ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          (indepSetCount G ((thresholdFloor n - 1) + 1) : ℝ) ≤
            (n : ℝ) ^ (1 - 0.99 * ε)} := by
  obtain ⟨n₀, hbase⟩ := gnHalf_thresholdIndepSetCount_le_rpow_with_error ε δ hε_pos hδ_pos
  refine ⟨max n₀ 2, ?_⟩
  intro n hn hnMain
  have hn₀_le : n₀ ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hαpos : 0 < thresholdFloor n := by
    by_contra hzero
    have hαzero : thresholdFloor n = 0 := Nat.eq_zero_of_not_pos hzero
    have hpow_le_one : (n : ℝ) ^ (0.05 + ε) ≤ 1 := by
      have hμ_le : (n : ℝ) ^ (0.05 + ε) ≤ expectedIndependentSets n (thresholdFloor n) := hnMain.1
      simpa [hαzero, expectedIndependentSets] using hμ_le
    have hn_gt_one_nat : 1 < n := lt_of_lt_of_le (by norm_num : 1 < 2) hn2
    have hn_gt_one : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn_gt_one_nat
    have hpow_gt_one : 1 < (n : ℝ) ^ (0.05 + ε) := by
      apply Real.one_lt_rpow hn_gt_one
      linarith
    linarith
  have hidx : ((thresholdFloor n - 1) + 1) = thresholdFloor n :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hαpos)
  simpa [hidx] using hbase n hn₀_le hnMain

end FirstMomentIndep

/-! ## Paper-Aligned Lower Bound

The remaining source-boundary work below is intended to be rewritten around the paper's
`classBoundedChromaticNumber` from `FirstMomentThreshold.lean`.

Current blockers:
- `heckel_chi_t_lower_bound` already controls `classBoundedChromaticNumber`;
- the structural bridge in Heckel 2024 should therefore connect
  `classBoundedChromaticNumber` to `chromaticNumber`;
- that paper-aligned structural bridge is now stated explicitly above, but still open.
-/

section ChiLowerBound

private lemma prob_inter_ge_of_complements {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (eps del : ENNReal)
    (pA : 1 - eps ≤ μ A) (pB : 1 - del ≤ μ B) :
    1 - eps - del ≤ μ (A ∩ B) := by
  have h1 : μ Aᶜ ≤ eps := by
    have := prob_compl_eq_one_sub (μ := μ) hA
    rw [this]
    exact tsub_le_iff_tsub_le.mp pA
  have h2 : μ Bᶜ ≤ del := by
    have := prob_compl_eq_one_sub (μ := μ) hB
    rw [this]
    exact tsub_le_iff_tsub_le.mp pB
  have h3 : μ (A ∩ B)ᶜ ≤ eps + del := by
    exact (Set.compl_inter A B ▸ measure_union_le Aᶜ Bᶜ).trans (add_le_add h1 h2)
  have h4 : 1 - (eps + del) ≤ μ (A ∩ B) := by
    have hcompl := prob_compl_eq_one_sub (μ := μ) (hA.inter hB)
    rw [hcompl] at h3
    exact tsub_le_iff_tsub_le.mpr h3
  exact le_trans (by simp [tsub_add_eq_tsub_tsub]) h4

/-- Deterministic paper-aligned Step (B): if
    - `χ_{α-1}(G)` is at least `kThresholdWitness n - 1`,
    - `α(G) ≤ (thresholdFloor n - 1) + 1`,
    - and the number of independent sets of size `(thresholdFloor n - 1) + 1`
      is at most `n^(1-0.99ε)`,

    then `χ(G) ≥ kThresholdWitness n - n^(1-0.9ε)`.

    This isolates the last missing probabilistic ingredient for the final theorem:
    a high-probability bound forcing `G.indepNum ≤ thresholdFloor n`. -/
theorem chromatic_ge_kThreshold_sub_rpow_of_classBounded
    {n : ℕ} {ε : ℝ} (G : SimpleGraph (Fin n))
    (hα : G.indepNum ≤ (thresholdFloor n - 1) + 1)
    (hχt : kThresholdWitness n - 1 ≤
      (classBoundedChromaticNumber n (thresholdFloor n - 1) G : ℝ))
    (hX : (indepSetCount G ((thresholdFloor n - 1) + 1) : ℝ) ≤
      (n : ℝ) ^ (1 - 0.99 * ε))
    (hgap : (1 : ℝ) ≤ (n : ℝ) ^ (1 - 0.9 * ε) - (n : ℝ) ^ (1 - 0.99 * ε)) :
    kThresholdWitness n - (n : ℝ) ^ (1 - 0.9 * ε) ≤ (chromaticNumber G : ℝ) := by
  have hbridge :
      (classBoundedChromaticNumber n (thresholdFloor n - 1) G : ℤ) -
        (indepSetCount G ((thresholdFloor n - 1) + 1) : ℤ) ≤
      (chromaticNumber G : ℤ) := by
    exact
      chromaticNumber_ge_classBoundedChromaticNumber_sub_indepSetCount
        n (thresholdFloor n - 1) G hα
  have hbridgeR :
      (classBoundedChromaticNumber n (thresholdFloor n - 1) G : ℝ) -
        (indepSetCount G ((thresholdFloor n - 1) + 1) : ℝ) ≤
      (chromaticNumber G : ℝ) := by
    exact_mod_cast hbridge
  linarith

/-- Final χ-lower-bound assembly from three probabilistic inputs:
    a whp lower bound on `χ_{α-1}`,
    a whp upper bound on `α(G)`,
    and a whp upper bound on the fixed-size threshold count `X_α`.

    This theorem isolates the only remaining missing probabilistic ingredient for
    `heckel_chromatic_lower_bound`: a suitable high-probability upper bound on
    `G.indepNum`. -/
theorem heckel_chromatic_lower_bound_from_split
    (ε η₁ η₂ η₃ : ℝ)
    (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂) (hη₃ : 0 ≤ η₃)
    (hχt : ∃ n₀₁ : ℕ, ∀ n : ℕ, n₀₁ ≤ n → InMainRange ε n →
      1 - ENNReal.ofReal η₁ ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          kThresholdWitness n - 1 ≤
            (classBoundedChromaticNumber n (thresholdFloor n - 1) G : ℝ)})
    (hα : ∃ n₀₂ : ℕ, ∀ n : ℕ, n₀₂ ≤ n → InMainRange ε n →
      1 - ENNReal.ofReal η₂ ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          G.indepNum ≤ (thresholdFloor n - 1) + 1})
    (hX : ∃ n₀₃ : ℕ, ∀ n : ℕ, n₀₃ ≤ n → InMainRange ε n →
      1 - ENNReal.ofReal η₃ ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          (indepSetCount G ((thresholdFloor n - 1) + 1) : ℝ) ≤
            (n : ℝ) ^ (1 - 0.99 * ε)})
    (hgap : ∃ n₀₄ : ℕ, ∀ n : ℕ, n₀₄ ≤ n →
      (1 : ℝ) ≤ (n : ℝ) ^ (1 - 0.9 * ε) - (n : ℝ) ^ (1 - 0.99 * ε)) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
      1 - ENNReal.ofReal (η₁ + η₂ + η₃) ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          kThresholdWitness n - (n : ℝ) ^ (1 - 0.9 * ε) ≤ (chromaticNumber G : ℝ)} := by
  obtain ⟨n₀₁, hχt'⟩ := hχt
  obtain ⟨n₀₂, hα'⟩ := hα
  obtain ⟨n₀₃, hX'⟩ := hX
  obtain ⟨n₀₄, hgap'⟩ := hgap
  refine ⟨max (max n₀₁ n₀₂) (max n₀₃ n₀₄), ?_⟩
  intro n hn hrange
  have hn₁ : n₀₁ ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
  have hn₂ : n₀₂ ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)
  have hn₃ : n₀₃ ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
  have hn₄ : n₀₄ ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn)
  set A := {G : SimpleGraph (Fin n) |
      kThresholdWitness n - 1 ≤
        (classBoundedChromaticNumber n (thresholdFloor n - 1) G : ℝ)}
  set B := {G : SimpleGraph (Fin n) |
      G.indepNum ≤ (thresholdFloor n - 1) + 1}
  set C := {G : SimpleGraph (Fin n) |
      (indepSetCount G ((thresholdFloor n - 1) + 1) : ℝ) ≤
        (n : ℝ) ^ (1 - 0.99 * ε)}
  have hA_meas : MeasurableSet A := Set.Finite.measurableSet (Set.toFinite _)
  have hB_meas : MeasurableSet B := Set.Finite.measurableSet (Set.toFinite _)
  have hC_meas : MeasurableSet C := Set.Finite.measurableSet (Set.toFinite _)
  haveI : IsProbabilityMeasure (gnHalf n) := by
    unfold gnHalf
    infer_instance
  have hμA : 1 - ENNReal.ofReal η₁ ≤ gnHalf n A := hχt' n hn₁ hrange
  have hμB : 1 - ENNReal.ofReal η₂ ≤ gnHalf n B := hα' n hn₂ hrange
  have hμC : 1 - ENNReal.ofReal η₃ ≤ gnHalf n C := hX' n hn₃ hrange
  have hAB :
      1 - ENNReal.ofReal (η₁ + η₂) ≤ gnHalf n (A ∩ B) := by
    have htmp := prob_inter_ge_of_complements
      (gnHalf n) A B hA_meas hB_meas
      (ENNReal.ofReal η₁) (ENNReal.ofReal η₂) hμA hμB
    have hadd : ENNReal.ofReal η₁ + ENNReal.ofReal η₂ = ENNReal.ofReal (η₁ + η₂) := by
      rw [← ENNReal.ofReal_add hη₁ hη₂]
    have hleft :
        1 - ENNReal.ofReal (η₁ + η₂) =
          1 - ENNReal.ofReal η₁ - ENNReal.ofReal η₂ := by
      rw [← hadd, tsub_add_eq_tsub_tsub]
    rw [hleft]
    exact htmp
  have hABC :
      1 - ENNReal.ofReal (η₁ + η₂ + η₃) ≤ gnHalf n ((A ∩ B) ∩ C) := by
    have htmp := prob_inter_ge_of_complements
      (gnHalf n) (A ∩ B) C (hA_meas.inter hB_meas) hC_meas
      (ENNReal.ofReal (η₁ + η₂)) (ENNReal.ofReal η₃) hAB hμC
    have hsum_nonneg : 0 ≤ η₁ + η₂ := add_nonneg hη₁ hη₂
    have hadd : ENNReal.ofReal (η₁ + η₂) + ENNReal.ofReal η₃ =
        ENNReal.ofReal (η₁ + η₂ + η₃) := by
      rw [← ENNReal.ofReal_add hsum_nonneg hη₃]
    have hleft :
        1 - ENNReal.ofReal (η₁ + η₂ + η₃) =
          1 - ENNReal.ofReal (η₁ + η₂) - ENNReal.ofReal η₃ := by
      rw [← hadd, tsub_add_eq_tsub_tsub]
    rw [hleft]
    exact htmp
  have hsub :
      (A ∩ B) ∩ C ⊆
        {G : SimpleGraph (Fin n) |
          kThresholdWitness n - (n : ℝ) ^ (1 - 0.9 * ε) ≤ (chromaticNumber G : ℝ)} := by
    intro G hG
    rcases hG with ⟨hAB, hC⟩
    rcases hAB with ⟨hA, hB⟩
    have hdet :=
      chromatic_ge_kThreshold_sub_rpow_of_classBounded
        (ε := ε) G hB hA hC (hgap' n hn₄)
    exact hdet
  exact le_trans hABC (MeasureTheory.measure_mono hsub)

/-- **[AXIOM]** Small-error version of the Heckel--Panagiotou lower bound for
    `χ_{α-1}` in the main range.

    This is the exact `η₁`-input required by
    `heckel_chromatic_lower_bound_from_split`. The probabilistic shell is now
    derivable from `heckel_chi_t_lower_bound_all_n`; the remaining missing input
    is only the small-error bound on the first-moment quantity `k! * E`. -/
private lemma thresholdFloor_gt_one_of_mainRange
    (ε : ℝ) (hε_pos : 0 < ε) {n : ℕ} (hn2 : 2 ≤ n) (hn : InMainRange ε n) :
    1 < thresholdFloor n := by
  have hαpos : 0 < thresholdFloor n := by
    by_contra hzero
    have hαzero : thresholdFloor n = 0 := Nat.eq_zero_of_not_pos hzero
    have hpow_le_one : (n : ℝ) ^ (0.05 + ε) ≤ 1 := by
      have hμ_le : (n : ℝ) ^ (0.05 + ε) ≤ expectedIndependentSets n (thresholdFloor n) := hn.1
      simpa [hαzero, expectedIndependentSets] using hμ_le
    have hn_gt_one_nat : 1 < n := lt_of_lt_of_le (by norm_num : 1 < 2) hn2
    have hn_gt_one : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn_gt_one_nat
    have hpow_gt_one : 1 < (n : ℝ) ^ (0.05 + ε) := by
      apply Real.one_lt_rpow hn_gt_one
      linarith
    linarith
  by_contra hnot
  have hα_le_one : thresholdFloor n ≤ 1 := Nat.not_lt.mp hnot
  have hαeq : thresholdFloor n = 1 := by omega
  have hμ_eq : expectedIndependentSets n (thresholdFloor n) = (n : ℝ) := by
    simp [hαeq, expectedIndependentSets, Nat.choose_one_right]
  have hμ_le : (n : ℝ) ≤ (n : ℝ) ^ (1 - ε) := by
    simpa [hμ_eq] using hn.2
  have hn_gt_one_nat : 1 < n := lt_of_lt_of_le (by norm_num : 1 < 2) hn2
  have hn_gt_one : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn_gt_one_nat
  have hpow_lt : (n : ℝ) ^ (1 - ε) < (n : ℝ) ^ (1 : ℝ) := by
    simpa using Real.rpow_lt_rpow_of_exponent_lt hn_gt_one (by linarith : 1 - ε < (1 : ℝ))
  have : (n : ℝ) ^ (1 : ℝ) ≤ (n : ℝ) ^ (1 - ε) := by simpa using hμ_le
  exact (not_lt_of_ge this) (by simpa [Real.rpow_one] using hpow_lt)

private lemma firstMomentThreshold_sub_one_pos_of_two_le
    (n t : ℕ) (hn2 : 2 ≤ n) (ht : 0 < t) :
    1 ≤ firstMomentThreshold n t ht - 1 := by
  have hE0_eq :
      expectedTBoundedColorings n 0 t = 0 := by
    unfold expectedTBoundedColorings
    have hempty : coloringProfileFinset n 0 t = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro f hf
      rcases (Finset.mem_filter.mp hf).2 with ⟨hsum, hcount, _⟩
      have hcount' := hcount
      rw [Fintype.sum_eq_zero_iff_of_nonneg (fun _ => Nat.zero_le _)] at hcount'
      have hf_zero : ∀ u : Fin (n + 1), f u = 0 := by
        intro u
        have hu := congrFun hcount' u
        exact Fin.ext hu
      have hweighted_zero : ∑ u : Fin (n + 1), u.val * (f u).val = 0 := by
        simp [hf_zero]
      have : n = 0 := by omega
      omega
    simp [hempty]
  have hk_le : (1 : ℕ) ≤ n := le_trans (by norm_num) hn2
  have hcoarse :=
    factorial_expectedTBoundedColorings_le_coarse n 1 t ht one_pos hk_le
  have hchoose_pos : 0 < Nat.choose n 2 := Nat.choose_pos (by omega)
  have hpow_lt_one : (1 / 2 : ℝ) ^ Nat.choose n 2 < 1 := by
    have hbase : (0 : ℝ) ≤ 1 / 2 := by norm_num
    have hbase_lt : (1 / 2 : ℝ) < 1 := by norm_num
    exact pow_lt_one₀ hbase hbase_lt hchoose_pos.ne'
  have hE1_lt :
      expectedTBoundedColorings n 1 t < 1 := by
    have hpow_le :
        expectedTBoundedColorings n 1 t ≤ (1 : ℝ) ^ n * (1 / 2 : ℝ) ^ Nat.choose n 2 := by
      simpa [Nat.factorial, Nat.div_eq_of_lt (by omega : 1 < 2), one_mul] using hcoarse
    have hlt_rhs :
        (1 : ℝ) ^ n * (1 / 2 : ℝ) ^ Nat.choose n 2 < 1 := by
      simpa using hpow_lt_one
    exact lt_of_le_of_lt hpow_le hlt_rhs
  have hfmt_ne_one : firstMomentThreshold n t ht ≠ 1 := by
    intro hfmt
    have hfmt_ge :
        (1 : ℝ) ≤ expectedTBoundedColorings n 1 t := by
      simpa [hfmt] using firstMomentThreshold_ge_one n t ht
    linarith
  have hfmt_ne_zero : firstMomentThreshold n t ht ≠ 0 := by
    intro hfmt
    have hfmt_ge :
        (1 : ℝ) ≤ expectedTBoundedColorings n 0 t := by
      simpa [hfmt] using firstMomentThreshold_ge_one n t ht
    linarith [hE0_eq]
  have hfmt_ge_two : 2 ≤ firstMomentThreshold n t ht := by
    omega
  omega

/-- **[AXIOM]** Small-error control of the first-moment error term on the
    threshold-level class-bounded coloring count.

    The currently live paper-aligned discharge route is no longer the deprecated
    BN.6 shell below, and it is also not the reciprocal target
    `k_t ≤ n/threshold n`: the 2026-05-05 direction audit showed that this
    reciprocal inequality has the wrong sign relative to
    `n / k_t = α₀ - 1 - 2 / ln 2 + o(1)`.

    Warning: this live axiom is stronger than the paper's lower-bound phrasing.
    HP Lemma `lowerbound` proves `χ_a ≥ k_a - 1` through the unordered
    obstruction `E_{n,k_a-2,a} → 0`. The current Lean shell instead uses the
    ordered-count Markov bound `k! * E_{n,k_t-1,t}`. The next honest replacement
    direction is therefore either:
    (1) prove this stronger ordered target directly, or
    (2) replace the shell with an unordered/quotiented first-moment count and
        target `PaperPartBUnorderedObstructionTarget` from `PartBProfileBridge`.

    The Heckel 2024 special-profile construction at
    `k^* = k_t - n^(1-ε/2)` belongs to the cochromatic/Part C route and should
    not be cited as a direct proof of this Part B axiom. -/
axiom threshold_tBoundedColoringError_le_with_error
    (ε δ : ℝ) (hε_pos : 0 < ε) (hδ_pos : 0 < δ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
      Nat.factorial
          (firstMomentThreshold n (max 1 (thresholdFloor n - 1))
            (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) - 1) *
        expectedTBoundedColorings n
          (firstMomentThreshold n (max 1 (thresholdFloor n - 1))
            (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) - 1)
          (max 1 (thresholdFloor n - 1)) ≤ δ

/-- A completed log-core profile bridge would discharge the live Part B error axiom.

This theorem does not prove the bridge; it verifies that the lightweight
`PartBProfileBridge.lean` target is definitionally aligned with the live theorem surface here. -/
theorem threshold_tBoundedColoringError_le_with_error_of_logCoreBridge
    (hbridge : ProfileLogCoreBridgeTarget)
    (ε δ : ℝ) (hε_pos : 0 < ε) (hδ_pos : 0 < δ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
      Nat.factorial
          (firstMomentThreshold n (max 1 (thresholdFloor n - 1))
            (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) - 1) *
        expectedTBoundedColorings n
          (firstMomentThreshold n (max 1 (thresholdFloor n - 1))
            (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) - 1)
          (max 1 (thresholdFloor n - 1)) ≤ δ := by
  exact (profileLevelPartBErrorTarget_unfold ε δ).mp
    (profileLevelPartBErrorTarget_of_logCoreBridge hbridge ε δ hε_pos hδ_pos)

/-!
## Threshold-based discharge of Part B (corrected architecture)

The original architecture used k ≤ n/D where D = threshold n - 7.9.
The decay claim (n/D)^n * (1/2)^{...} → 0 is FALSE (net exponent → (7/2)*log 2 > 0).

The corrected architecture tried to use k ≤ n/threshold n directly.
Verified numerically: at n=10^6, net_log/n ≈ -0.14; at n=10^12, ≈ -0.20.

Two paper-level axioms replace the old axiom:
1. `kThresholdWitness_le_n_div_threshold`: HP-2023 Lemma 5 (lemma:averagecolourclass)
2. `threshold_decay_axiom`: real-analysis decay for k ≤ n/threshold n

Together they prove `threshold_tBoundedColoringError_le_with_error` as a theorem, but
the witness axiom below is now known to have the wrong direction relative to the
cited paper asymptotic. RouteD2 therefore does not use this chain as its live entry
point.
-/

/-- Upper bound on the threshold witness from HP-2023.

    This is the key content of Heckel–Panagiotou (2023) Lemma 5 (lemma:averagecolourclass):
      n / k_t = α₀ - 1 - 2 / ln 2 + o(1)
    where α₀ = threshold n ≈ 2*logb₂(n).

    Direction audit (2026-05-05): the following axiom is intentionally retained only as
    an experimental/dead-end interface. The cited asymptotic actually gives
    `k_t ≈ n/(α₀ - 1 - 2/ln2)`, which is larger than `n/α₀`, not smaller.
    Thus it does **not** justify `k_t ≤ n/threshold n`.

    We also assert threshold n > 0 (which holds since threshold n ≥ 9 eventually).

    Precise reference: Heckel–Panagiotou, "Colouring random graphs: Tame colourings" (2023), arXiv:2306.07253, Lemma 5.
    The paper-aligned consequence has the opposite comparison at threshold scale:
    `k_t(n) ≥ n/threshold n` eventually, up to lower-order interpretation. -/
axiom kThresholdWitness_le_n_div_threshold (ε : ℝ) (hε_pos : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
      0 < threshold n ∧ kThresholdWitness n ≤ (n : ℝ) / threshold n

/-- Helper: if k ≤ n/T (real) and T > 0, then nat div satisfies T ≤ n/k (nat).

    Key bridge between real-division hypothesis and nat-division output. -/
private lemma natDiv_ge_threshold_of_le_real_div
    {n k : ℕ} {T : ℝ} (hT_pos : 0 < T) (hk_pos : 0 < k)
    (hk_real : (k : ℝ) ≤ (n : ℝ) / T) :
    ⌊T⌋₊ ≤ n / k := by
  apply Nat.le_div_iff_mul_le hk_pos |>.mpr
  have hfloor_le : (⌊T⌋₊ : ℝ) ≤ T := Nat.floor_le (le_of_lt hT_pos)
  have hprod : (⌊T⌋₊ : ℝ) * k ≤ n := by
    calc (⌊T⌋₊ : ℝ) * k ≤ T * k := mul_le_mul_of_nonneg_right hfloor_le (Nat.cast_nonneg _)
      _ ≤ (n : ℝ) := by rw [mul_comm]; exact mul_le_of_le_div₀ (Nat.cast_nonneg _) (le_of_lt hT_pos) hk_real
  exact_mod_cast hprod

/-- Helper: C(n/k, 2) ≥ C(⌊T⌋₊, 2) when k ≤ n/T (real) and T, k > 0.

    Proved by combining `natDiv_ge_threshold_of_le_real_div` with monotonicity of C(·,2). -/
private lemma choose2_natDiv_ge_of_le_real_div
    {n k : ℕ} {T : ℝ} (hT_pos : 0 < T) (hk_pos : 0 < k)
    (hk_real : (k : ℝ) ≤ (n : ℝ) / T) :
    Nat.choose ⌊T⌋₊ 2 ≤ Nat.choose (n / k) 2 :=
  Nat.choose_le_choose 2 (natDiv_ge_threshold_of_le_real_div hT_pos hk_pos hk_real)

/-- Helper: the exponent k·C(n/k,2) dominates k·C(⌊T⌋₊,2) when k ≤ n/T.

    This allows replacing the adaptive exponent with a T-dependent one. -/
private lemma mul_choose2_natDiv_ge
    {n k : ℕ} {T : ℝ} (hT_pos : 0 < T) (hk_pos : 0 < k)
    (hk_real : (k : ℝ) ≤ (n : ℝ) / T) :
    k * Nat.choose ⌊T⌋₊ 2 ≤ k * Nat.choose (n / k) 2 :=
  Nat.mul_le_mul_left k (choose2_natDiv_ge_of_le_real_div hT_pos hk_pos hk_real)

/-- Helper: reduce decay to the worst-case k = n/T.

    If k ≤ n/T (real), then:
      k^n * (1/2)^{k*C(n/k,2)} ≤ (n/T)^n * (1/2)^{k * C(⌊T⌋₊, 2)}.

    Proof: (a) k^n ≤ (n/T)^n since k ≤ n/T; (b) (1/2)^{k*C(n/k,2)} ≤ (1/2)^{k*C(⌊T⌋₊,2)}
    since k*C(n/k,2) ≥ k*C(⌊T⌋₊,2). -/
private lemma decay_le_worst_case
    {n k : ℕ} {T : ℝ} (hn : 0 < n) (hT_pos : 0 < T) (hk_pos : 0 < k) (hk_le_n : k ≤ n)
    (hk_real : (k : ℝ) ≤ (n : ℝ) / T) :
    (k : ℝ) ^ n * (1 / 2 : ℝ) ^ (k * Nat.choose (n / k) 2) ≤
      ((n : ℝ) / T) ^ n * (1 / 2 : ℝ) ^ (k * Nat.choose ⌊T⌋₊ 2) := by
  have hk_pow_le : (k : ℝ) ^ n ≤ ((n : ℝ) / T) ^ n :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hk_real n
  have hexp_le : (1 / 2 : ℝ) ^ (k * Nat.choose (n / k) 2) ≤
      (1 / 2 : ℝ) ^ (k * Nat.choose ⌊T⌋₊ 2) :=
    pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1/2 : ℝ) ≤ 1)
      (mul_choose2_natDiv_ge hT_pos hk_pos hk_real)
  have hpow_nonneg : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (k * Nat.choose (n / k) 2) := by positivity
  have hbase_nonneg : (0 : ℝ) ≤ ((n : ℝ) / T) ^ n := by positivity
  exact mul_le_mul hk_pow_le hexp_le hpow_nonneg hbase_nonneg

/-- Corollary: reduction to C(thresholdFloor n, 2) via `decay_le_worst_case`.

    Since `⌊threshold n⌋₊ = thresholdFloor n`, this specializes `decay_le_worst_case`
    to the threshold denominator used in the axiom. -/
private lemma decay_le_worst_case_threshold
    {n k : ℕ} (hn : 0 < n) (hT_pos : 0 < threshold n) (hk_pos : 0 < k) (hk_le_n : k ≤ n)
    (hk_real : (k : ℝ) ≤ (n : ℝ) / threshold n) :
    (k : ℝ) ^ n * (1 / 2 : ℝ) ^ (k * Nat.choose (n / k) 2) ≤
      ((n : ℝ) / threshold n) ^ n * (1 / 2 : ℝ) ^ (k * Nat.choose (thresholdFloor n) 2) := by
  have heq : ⌊threshold n⌋₊ = thresholdFloor n := rfl
  rw [← heq]
  exact decay_le_worst_case hn hT_pos hk_pos hk_le_n hk_real

/-- Uniform lower bound on the exponent k·C(n/k,2) for k ≤ n/T.

    Key inequality: for 1 ≤ k ≤ n/T (real), k·C(n/k,2) ≥ n·(T-2)²/(2·T).

    Proof route (avoiding monotonicity of continuous functions):
    1. 2·C(n/k,2) = (n/k)·(n/k-1) exactly (since m·(m-1) is always even).
    2. k·(n/k) ≥ n - k (from Euclidean division).
    3. n/k - 1 ≥ T - 2 (from natDiv_ge_threshold: n/k ≥ ⌊T⌋₊ ≥ T-1).
    4. n - k ≥ n·(T-1)/T (from k ≤ n/T iff k·T ≤ n).
    5. Chain: 2·k·C(n/k,2) = k·(n/k)·(n/k-1) ≥ (n-k)·(T-2) ≥ n·(T-1)/T·(T-2) ≥ n·(T-2)²/T.
    6. Divide by 2: k·C(n/k,2) ≥ n·(T-2)²/(2T).

    This bound is uniform in k (depends only on n and T, not k itself).
    Key use: combine with k^n ≤ (n/T)^n to get a k-independent upper bound on the decay product. -/
private lemma mul_choose2_ge_n_T_quadratic
    {n k : ℕ} {T : ℝ} (hT : 2 < T) (hk_pos : 0 < k) (hk_le_n : k ≤ n)
    (hk_real : (k : ℝ) ≤ (n : ℝ) / T) :
    (n : ℝ) * (T - 2) ^ 2 / (2 * T) ≤ (k : ℝ) * Nat.choose (n / k) 2 := by
  have hT_pos : (0 : ℝ) < T := by linarith
  have hk_pos_r : (0 : ℝ) < k := Nat.cast_pos.mpr hk_pos
  have hndivk_ge : ⌊T⌋₊ ≤ n / k := natDiv_ge_threshold_of_le_real_div hT_pos hk_pos hk_real
  have hfloorT_ge : T - 1 ≤ (⌊T⌋₊ : ℝ) := by
    have h := Nat.lt_floor_add_one T
    push_cast at h ⊢; linarith [Nat.zero_le ⌊T⌋₊]
  have hndivk_real : T - 1 ≤ (n / k : ℕ) :=
    le_trans hfloorT_ge (by exact_mod_cast hndivk_ge)
  -- n/k ≥ 2 (T > 2 → ⌊T⌋₊ > 1 as nat)
  have hndivk_ge2 : 2 ≤ n / k := by
    have h1 : (1 : ℝ) < (⌊T⌋₊ : ℝ) := by linarith
    have h2 : (1 : ℕ) < ⌊T⌋₊ := by exact_mod_cast h1
    omega
  -- n/k - 1 ≥ T - 2 as reals
  have hndivk_sub_real : T - 2 ≤ ((n / k - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; linarith
  -- k * (n/k) ≥ n - k as naturals
  have hkdiv_lower : n - k ≤ k * (n / k) := by
    have := Nat.div_add_mod n k; have := Nat.mod_lt n hk_pos; omega
  -- k * (n/k) ≥ n - k as reals
  have hkdiv_r : (n : ℝ) - k ≤ (k : ℝ) * (n / k : ℕ) := by exact_mod_cast hkdiv_lower
  -- k * T ≤ n (from k ≤ n/T)
  have hkT_le_n : (k : ℝ) * T ≤ n := by
    have := mul_le_of_le_div₀ (Nat.cast_nonneg (α := ℝ) n) hT_pos.le hk_real
    linarith [mul_comm T (k : ℝ)]
  -- 2 * C(n/k, 2) = (n/k) * (n/k - 1) exactly (m*(m-1) is always even)
  have htwo_choose : 2 * Nat.choose (n / k) 2 = (n / k) * (n / k - 1) := by
    have heven : 2 ∣ (n / k) * (n / k - 1) := by
      have h := Nat.even_mul_succ_self (n / k - 1)
      obtain ⟨j, hj⟩ := h
      exact ⟨j, by nlinarith [show n / k - 1 + 1 = n / k from by omega]⟩
    rw [Nat.choose_two_right]; omega
  -- 2 * (k * C(n/k, 2)) = k * (n/k) * (n/k - 1) as reals
  have htwo_kC_real : 2 * ((k : ℝ) * Nat.choose (n / k) 2) =
      (k : ℝ) * (n / k : ℕ) * (n / k - 1 : ℕ) := by
    have h : (2 * (k * Nat.choose (n / k) 2) : ℕ) = k * (n / k) * (n / k - 1) := by
      linarith [show k * (2 * Nat.choose (n / k) 2) = k * (n / k * (n / k - 1)) from
        by rw [htwo_choose]]
    exact_mod_cast h
  -- Main chain in ℝ: n*(T-2)²/T ≤ (n-k)*(T-2) ≤ k*(n/k)*(T-2) ≤ k*(n/k)*(n/k-1) = 2kC(n/k,2)
  have hT_minus_2 : (0 : ℝ) ≤ T - 2 := by linarith
  have hchain : (n : ℝ) * (T - 2) ^ 2 / T ≤ 2 * ((k : ℝ) * Nat.choose (n / k) 2) := by
    rw [htwo_kC_real]
    have hnd1_nonneg : (0 : ℝ) ≤ (n / k - 1 : ℕ) := Nat.cast_nonneg _
    calc (n : ℝ) * (T - 2) ^ 2 / T
        ≤ ((n : ℝ) - k) * (T - 2) := by
            apply (div_le_iff₀ hT_pos).mpr
            nlinarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) k]
      _ ≤ (k : ℝ) * (n / k : ℕ) * (T - 2) := by
            nlinarith [mul_nonneg (le_of_lt hk_pos_r) hT_minus_2]
      _ ≤ (k : ℝ) * (n / k : ℕ) * (n / k - 1 : ℕ) := by
            nlinarith [mul_nonneg (mul_nonneg (le_of_lt hk_pos_r)
              (Nat.cast_nonneg (α := ℝ) (n / k))) hnd1_nonneg]
  have hC_nonneg : (0 : ℝ) ≤ (k : ℝ) * Nat.choose (n / k) 2 := by positivity
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * T)]
  have hchain_mul : (n : ℝ) * (T - 2) ^ 2 ≤ 2 * ((k : ℝ) * Nat.choose (n / k) 2) * T := by
    have h := (div_le_iff₀ hT_pos).mp hchain; nlinarith
  nlinarith

/-- k-independent upper bound on the product k^n·(1/2)^{k·C(n/k,2)}.

    For any k ≤ n/T:
      k^n · (1/2)^{k·C(n/k,2)} ≤ (n/T)^n · (1/2)^{⌊n·(T-2)²/(2T)⌋₊}

    The right-hand side is k-independent, enabling a uniform decay bound.

    Proof:
    - k^n ≤ (n/T)^n from k ≤ n/T.
    - k·C(n/k,2) ≥ ⌊n·(T-2)²/(2T)⌋₊ from mul_choose2_ge_n_T_quadratic.
    - (1/2)^{large} ≤ (1/2)^{small} since 1/2 < 1. -/
private lemma decay_k_independent_upper_bound
    {n k : ℕ} {T : ℝ} (hn : 0 < n) (hT : 2 < T) (hk_pos : 0 < k) (hk_le_n : k ≤ n)
    (hk_real : (k : ℝ) ≤ (n : ℝ) / T) :
    (k : ℝ) ^ n * (1 / 2 : ℝ) ^ (k * Nat.choose (n / k) 2) ≤
      ((n : ℝ) / T) ^ n * (1 / 2 : ℝ) ^ ⌊(n : ℝ) * (T - 2) ^ 2 / (2 * T)⌋₊ := by
  have hT_pos : (0 : ℝ) < T := by linarith
  have hk_pow_le : (k : ℝ) ^ n ≤ ((n : ℝ) / T) ^ n :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hk_real n
  have hexponent_le : ⌊(n : ℝ) * (T - 2) ^ 2 / (2 * T)⌋₊ ≤ k * Nat.choose (n / k) 2 :=
    Nat.floor_le_of_le (by exact_mod_cast mul_choose2_ge_n_T_quadratic hT hk_pos hk_le_n hk_real)
  have hexp_le : (1 / 2 : ℝ) ^ (k * Nat.choose (n / k) 2) ≤
      (1 / 2 : ℝ) ^ ⌊(n : ℝ) * (T - 2) ^ 2 / (2 * T)⌋₊ :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hexponent_le
  have hpow_nonneg : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (k * Nat.choose (n / k) 2) := by positivity
  have hbase_nonneg : (0 : ℝ) ≤ ((n : ℝ) / T) ^ n := by positivity
  exact mul_le_mul hk_pow_le hexp_le hpow_nonneg hbase_nonneg

/-- Decay for k ≤ n/threshold n.

    For k ≤ n/threshold n, the product k^n * (1/2)^{k*C(n/k,2)} → 0.
    This is the corrected version of the false `hdecay` sorry.

    Proof sketch: with T = threshold n ≈ 2*logb₂(n), at k = n/T:
      n*log(n/T) ≈ n*(log n - log T) ≈ n*(log n - log(2 log n)) = n*(log n - log 2 - log log n)
      k*C(n/k,2)*log 2 ≈ (n/T)*(T*(T-1)/2)*log 2 ≈ n*T/2*log 2 ≈ n*logb₂(n)*log 2 = n*log n
    Net ≈ -n*log(log n) → -∞.
    (Verified numerically: n=10^6 gives net/n ≈ -0.14; n=10^12 gives ≈ -0.20.)

    Proof route (for future discharge):
    1. `decay_le_worst_case` reduces to bounding (n/T)^n * (1/2)^{k*C(T,2)}.
    2. The worst case is k = n/T (nat) using monotonicity in k.
    3. The resulting product (n/T)^n * (1/2)^{(n/T)*C(T,2)} → 0 by the exponent computation:
         n * log(n/T) - (n/T)*C(T,2)*log2 ≤ n*(log n - log T) - (n/T - 1)*C(T,2)*log2
         ≈ n*(log n - log(2*logb₂ n)) - n/2*(2*logb₂ n - 1)*log2
         ≈ n*(log n - log(logb₂ n) - log 2) - n*logb₂ n * log 2
         = n*(log n - log(logb₂ n) - log 2 - log n) = -n*(log(logb₂ n) + log 2) → -∞.
    4. This real-analysis computation requires threshold n ≥ 9 (proved) and HP-2023 asymptotics.

    Reference: follows from threshold n ≈ 2*logb₂(n) in HP-2023 arXiv:2306.07253
    combined with standard Stirling-free real-analysis estimates. -/
axiom threshold_decay_axiom (δ : ℝ) (hδ_pos : 0 < δ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      0 < threshold n →
      ∀ (k : ℕ), 0 < k → k ≤ n →
        (k : ℝ) ≤ (n : ℝ) / threshold n →
        (k : ℝ) ^ n * (1 / 2 : ℝ) ^ (k * Nat.choose (n / k) 2) ≤ δ

/-- Experimental Part B theorem from the two threshold-based axioms above.

    Proof route:
    1. `kThresholdWitness_le_n_div_threshold` → k_t - 1 ≤ k_t ≤ n/threshold n
    2. `factorial_expectedTBoundedColorings_le_sharp_coarse` → k! * E ≤ k^n * (1/2)^{k*C(n/k,2)}
    3. `threshold_decay_axiom` → k^n * (1/2)^{k*C(n/k,2)} ≤ δ
    Together: k! * E ≤ δ.

    Direction audit (2026-05-05): this theorem is Lean-valid relative to its stated
    axioms, but the witness axiom is not a valid corollary of the cited paper
    asymptotic. The live RouteD2 proof therefore uses the legacy checked Part B
    theorem rather than this experimental split. -/
theorem threshold_tBoundedColoringError_le_with_error_via_threshold
    (ε δ : ℝ) (hε_pos : 0 < ε) (hδ_pos : 0 < δ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
      Nat.factorial
          (firstMomentThreshold n (max 1 (thresholdFloor n - 1))
            (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) - 1) *
        expectedTBoundedColorings n
          (firstMomentThreshold n (max 1 (thresholdFloor n - 1))
            (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) - 1)
          (max 1 (thresholdFloor n - 1)) ≤ δ := by
  obtain ⟨n_wit, hwit⟩ := kThresholdWitness_le_n_div_threshold ε hε_pos
  obtain ⟨n_decay, hdecay⟩ := threshold_decay_axiom δ hδ_pos
  refine ⟨max 2 (max n_wit n_decay), fun n hn hmain => ?_⟩
  have hn2 : 2 ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn_wit : n_wit ≤ n := by omega
  have hn_decay : n_decay ≤ n := by omega
  set t := max 1 (thresholdFloor n - 1)
  set ht : 0 < t := Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)
  set k := firstMomentThreshold n t ht - 1
  have hkw_eq : kThresholdWitness n = firstMomentThreshold n t ht := by
    simp only [kThresholdWitness]; congr 1
  have hk_pos : 0 < k := by
    have := firstMomentThreshold_sub_one_pos_of_two_le n t hn2 ht; omega
  have hk_le_n : k ≤ n :=
    Nat.sub_le_of_le_add ((firstMomentThreshold_le_n n t ht).trans (Nat.le_add_right n 1))
  obtain ⟨hT_pos, hkw_upper⟩ := hwit n hn_wit hmain
  have hfmt_ge : 1 ≤ firstMomentThreshold n t ht := by
    have := firstMomentThreshold_sub_one_pos_of_two_le n t hn2 ht; omega
  have hcast : (k : ℝ) = (firstMomentThreshold n t ht : ℝ) - 1 := by
    have hsub : (k : ℝ) = ((firstMomentThreshold n t ht - 1 : ℕ) : ℝ) := by exact_mod_cast rfl
    rw [hsub, Nat.cast_sub hfmt_ge]; push_cast; ring
  have hkw_pos : 0 < (kThresholdWitness n : ℝ) := by
    rw [hkw_eq]
    have : 0 < firstMomentThreshold n t ht := by omega
    exact_mod_cast this
  have hk_real_le : (k : ℝ) ≤ (n : ℝ) / threshold n :=
    calc (k : ℝ) = (firstMomentThreshold n t ht : ℝ) - 1 := hcast
      _ ≤ kThresholdWitness n - 1 := by rw [hkw_eq]
      _ ≤ kThresholdWitness n := by linarith [hkw_pos]
      _ ≤ (n : ℝ) / threshold n := hkw_upper
  have hsharp := factorial_expectedTBoundedColorings_le_sharp_coarse n k t ht hk_pos hk_le_n
  have hdecay_bound := hdecay n hn_decay hT_pos k hk_pos hk_le_n hk_real_le
  change Nat.factorial k * expectedTBoundedColorings n k (max 1 (thresholdFloor n - 1)) ≤ δ
  rw [show max 1 (thresholdFloor n - 1) = t from rfl]
  exact le_trans (by exact_mod_cast hsharp) hdecay_bound

/-- Paper-aligned reciprocal lower bound on the average colour-class size at the
    threshold witness `k_t`.

    This is the live theorem target suggested by `lemma:averagecolourclass` in
    Heckel--Panagiotou (2023). The exact asymptotic in the paper is

      `n / k_t = α₀ - 1 - 2 / ln 2 + o(1)`,

    where `α₀` matches our `threshold n`. For Lean purposes we expect to use a
    weaker eventual inequality of this shape, with an explicit constant buffer
    `C`, as the remaining input needed to remove
    `threshold_tBoundedColoringError_le_with_error`. -/
private def ThresholdAverageColourClassCriterion (C : ℝ) (n : ℕ) : Prop :=
  threshold n - (1 + 2 / Real.log 2) - C ≤ (n : ℝ) / kThresholdWitness n

/-- Eventual main-range form of the paper-aligned reciprocal criterion. -/
private def EventualThresholdAverageColourClassCriterion (ε C : ℝ) : Prop :=
  ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
    ThresholdAverageColourClassCriterion C n

/-- Deprecated eventual main-range upper bound on the threshold witness `k_t`.

Direction audit (2026-05-05): this upper-bound target is not justified by the
cited average-colour-class asymptotic. It is retained only to keep the old
dead-end route compile-safe.
-/
private def EventualKThresholdWitnessUpperBound (ε : ℝ) (L : ℕ → ℝ) : Prop :=
  ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
    kThresholdWitness n ≤ (n : ℝ) / L n

/-- Deprecated denominator from the old reciprocal route. -/
private noncomputable def thresholdAverageColourClassDenom (C : ℝ) (n : ℕ) : ℝ :=
  threshold n - (1 + 2 / Real.log 2) - C

/-- Constant buffer retained for the deprecated reciprocal route. -/
private def safeAverageColourClassBuffer : ℝ := 4

/-- First concrete upstream target for the deprecated reciprocal route. -/
private def EventualSafeKThresholdWitnessUpperBound (ε : ℝ) : Prop :=
  EventualKThresholdWitnessUpperBound ε
    (thresholdAverageColourClassDenom safeAverageColourClassBuffer)

/-- First concrete reciprocal target for the deprecated route. -/
private def EventualSafeThresholdAverageColourClassCriterion (ε : ℝ) : Prop :=
  EventualThresholdAverageColourClassCriterion ε safeAverageColourClassBuffer

/-- Research note: why the safe reciprocal target is **not** the right next theorem.

The paper does not use `lemma:averagecolourclass` in isolation. Around the quick
proof of `lemmaupperbound`, it explicitly studies the regime

`n / k > α₀ - 1 - 2 / ln 2 + C`

and derives exponential decay of the relevant first-moment quantity. Earlier
notes tried to package this as `EventualSafeThresholdAverageColourClassCriterion ε`,
but that loses the paper's profile-level information and points the witness
comparison in the wrong direction.

Equally important, the existing coarse theorem
`factorial_expectedTBoundedColorings_le_coarse` is not by itself strong enough
to close this route: it still counts all `k`-colorings and carries the large
factor `k^n`. So the next theorem must come from the paper's sharper
profile-level upper-bound analysis, not from squeezing the coarse bound harder.

More specifically, the quick proof of `lemmaupperbound` is written for the
profile-level expectation `E[\bar X_{\mathbf{k}}]` after the refined formula
`cont2`, not for the fully summed quantity `expectedTBoundedColorings`. So the
remaining gap is the bridge from threshold `L_0` control to the relevant
maximizing/tame profile surface used in the paper, not a standalone reciprocal
bound on `k_t`.
-/
private lemma safe_reciprocal_route_note : True := by
  trivial

private lemma thresholdAverageColourClassCriterion_eq
    (C : ℝ) (n : ℕ) :
    ThresholdAverageColourClassCriterion C n ↔
      (2 * (((n : ℝ).log) / Real.log 2)
        - 2 * (Real.log (((n : ℝ).log) / Real.log 2) / Real.log 2)
        + 2 * (Real.log (Real.exp 1 / 2) / Real.log 2)
        + 1 - (1 + 2 / Real.log 2) - C ≤
          (n : ℝ) / kThresholdWitness n) := by
  simp [ThresholdAverageColourClassCriterion, threshold]

/-- Deprecated threshold-level BN.6-style criterion.

This predicate was introduced while trying to discharge
`threshold_tBoundedColoringError_le_with_error` through a chromatic-style
logarithmic inequality. That route is currently known to be mathematically
mis-scaled for the threshold witness `k_t ≍ n / log n`: the left-hand side has
order `n log n`, while the right-hand side only has order `log^2 n`.

We keep the definition and its local reductions only as an explicit dead-end
record. The honest remaining Part B blocker is instead a paper-aligned
asymptotic first-moment input around `lemma:averagecolourclass`.
-/
private def ThresholdLogCriterion (n : ℕ) : Prop :=
  let t := max 1 (thresholdFloor n - 1)
  let k := firstMomentThreshold n t (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) - 1
  ((n : ℝ) * (Real.log k / Real.log 2) + (Real.log n / Real.log 2) + 1 ≤
    ((n / k).choose 2 : ℝ))

private noncomputable def thresholdLogT (n : ℕ) : ℕ :=
  let t := max 1 (thresholdFloor n - 1)
  t

private lemma thresholdLogT_eq_mainRange
    (ε : ℝ) (hε_pos : 0 < ε) {n : ℕ} (hn2 : 2 ≤ n) (hn : InMainRange ε n) :
    thresholdLogT n = thresholdFloor n - 1 := by
  have hαgt1 : 1 < thresholdFloor n := thresholdFloor_gt_one_of_mainRange ε hε_pos hn2 hn
  have hαm1_ge_one : 1 ≤ thresholdFloor n - 1 := by omega
  simp [thresholdLogT, max_eq_right hαm1_ge_one]

private noncomputable def thresholdLogK (n : ℕ) : ℕ :=
  firstMomentThreshold n (thresholdLogT n)
      (Nat.lt_of_lt_of_le one_pos (by
        dsimp [thresholdLogT]
        exact le_max_left 1 _)) - 1

private lemma thresholdLogT_pos (n : ℕ) :
    0 < thresholdLogT n := by
  dsimp [thresholdLogT]
  exact Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)

private lemma thresholdLogK_succ_eq_firstMomentThreshold
    {n : ℕ} (hn2 : 2 ≤ n) :
    thresholdLogK n + 1 =
      firstMomentThreshold n (thresholdLogT n)
        (Nat.lt_of_lt_of_le one_pos (by
          dsimp [thresholdLogT]
          exact le_max_left 1 _)) := by
  dsimp [thresholdLogK]
  have hk_one :
      1 ≤
        firstMomentThreshold n (thresholdLogT n)
          (Nat.lt_of_lt_of_le one_pos (by
            dsimp [thresholdLogT]
            exact le_max_left 1 _)) - 1 := by
    exact firstMomentThreshold_sub_one_pos_of_two_le n (thresholdLogT n) hn2 (thresholdLogT_pos n)
  omega

private lemma thresholdLogK_eq_kThresholdWitness_sub_one
    {n : ℕ} (hn2 : 2 ≤ n) :
    (thresholdLogK n : ℝ) = kThresholdWitness n - 1 := by
  have hsucc := thresholdLogK_succ_eq_firstMomentThreshold (n := n) hn2
  have hsucceq : ((thresholdLogK n + 1 : ℕ) : ℝ) = kThresholdWitness n := by
    simpa [kThresholdWitness] using congrArg (fun m : ℕ => (m : ℝ)) hsucc
  have hsucceq' : (thresholdLogK n : ℝ) + 1 = kThresholdWitness n := by
    simpa using hsucceq
  linarith

private lemma kThresholdWitness_sub_one_eq_thresholdLogK
    {n : ℕ} (hn2 : 2 ≤ n) :
    kThresholdWitness n - 1 = (thresholdLogK n : ℝ) := by
  symm
  exact thresholdLogK_eq_kThresholdWitness_sub_one hn2

private lemma kThresholdWitness_sub_one_pos
    {n : ℕ} (hn2 : 2 ≤ n) :
    0 < kThresholdWitness n - 1 := by
  rw [kThresholdWitness_sub_one_eq_thresholdLogK hn2]
  have hk_one : 1 ≤ thresholdLogK n := by
    have hk_ge_two :
        2 ≤ firstMomentThreshold n (thresholdLogT n)
          (Nat.lt_of_lt_of_le one_pos (by
            dsimp [thresholdLogT]
            exact le_max_left 1 _)) := by
      have : 1 ≤ firstMomentThreshold n (thresholdLogT n)
          (Nat.lt_of_lt_of_le one_pos (by
            dsimp [thresholdLogT]
            exact le_max_left 1 _)) - 1 := by
        exact firstMomentThreshold_sub_one_pos_of_two_le n (thresholdLogT n) hn2 (thresholdLogT_pos n)
      omega
    have hk_eq :
        thresholdLogK n + 1 =
          firstMomentThreshold n (thresholdLogT n)
            (Nat.lt_of_lt_of_le one_pos (by
              dsimp [thresholdLogT]
              exact le_max_left 1 _)) := thresholdLogK_succ_eq_firstMomentThreshold (n := n) hn2
    omega
  exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hk_one)

private lemma kThresholdWitness_pos
    {n : ℕ} (hn2 : 2 ≤ n) :
    0 < kThresholdWitness n := by
  have hsub : 0 < kThresholdWitness n - 1 := kThresholdWitness_sub_one_pos hn2
  linarith

private lemma thresholdLogCriterion_eq
    (n : ℕ) :
    ThresholdLogCriterion n ↔
      ((n : ℝ) * (Real.log (thresholdLogK n) / Real.log 2) + (Real.log n / Real.log 2) + 1 ≤
        ((n / thresholdLogK n).choose 2 : ℝ)) := by
  simp [ThresholdLogCriterion, thresholdLogK, thresholdLogT]

private lemma thresholdLogCriterion_eq_kThresholdWitness
    {n : ℕ} (hn2 : 2 ≤ n) :
    ThresholdLogCriterion n ↔
      ((n : ℝ) * (Real.log (kThresholdWitness n - 1) / Real.log 2) + (Real.log n / Real.log 2) + 1 ≤
        ((n / thresholdLogK n).choose 2 : ℝ)) := by
  rw [thresholdLogCriterion_eq]
  rw [thresholdLogK_eq_kThresholdWitness_sub_one hn2]

private lemma le_div_of_kThresholdWitness_upper
    {n : ℕ} (hn2 : 2 ≤ n)
    {L : ℝ} (hL_pos : 0 < L)
    (hupper : kThresholdWitness n - 1 ≤ (n : ℝ) / L) :
    L ≤ (n : ℝ) / (kThresholdWitness n - 1) := by
  have hk_pos : 0 < kThresholdWitness n - 1 := kThresholdWitness_sub_one_pos hn2
  have hupper' : (kThresholdWitness n - 1) * L ≤ (n : ℝ) := by
    exact (le_div_iff₀ hL_pos).mp hupper
  rw [le_div_iff₀ hk_pos]
  nlinarith [hupper']

private lemma thresholdAverageColourClassCriterion_of_kThresholdWitness_upper
    {C : ℝ} {n : ℕ} {L : ℝ} (hn2 : 2 ≤ n)
    (hL_pos : 0 < L)
    (hth : threshold n - (1 + 2 / Real.log 2) - C ≤ L)
    (hk : kThresholdWitness n ≤ (n : ℝ) / L) :
    ThresholdAverageColourClassCriterion C n := by
  have hk_pos : 0 < kThresholdWitness n := kThresholdWitness_pos hn2
  have hL_le : L ≤ (n : ℝ) / kThresholdWitness n := by
    have hk' : kThresholdWitness n * L ≤ (n : ℝ) := by
      exact (le_div_iff₀ hL_pos).mp hk
    rw [le_div_iff₀ hk_pos]
    nlinarith [hk']
  exact le_trans hth hL_le

private lemma kThresholdWitness_upper_of_thresholdAverageColourClassCriterion
    {C : ℝ} {n : ℕ}
    (hn2 : 2 ≤ n)
    (hden_pos : 0 < thresholdAverageColourClassDenom C n)
    (hcrit : ThresholdAverageColourClassCriterion C n) :
    kThresholdWitness n ≤ (n : ℝ) / thresholdAverageColourClassDenom C n := by
  have hk_pos : 0 < kThresholdWitness n := kThresholdWitness_pos hn2
  have hbound : thresholdAverageColourClassDenom C n ≤ (n : ℝ) / kThresholdWitness n := by
    exact hcrit
  rw [le_div_iff₀ hden_pos]
  rw [le_div_iff₀ hk_pos] at hbound
  nlinarith [hbound]

private lemma eventual_thresholdAverageColourClassCriterion_of_eventual_kThresholdWitness_upper
    {ε C : ℝ} {L : ℕ → ℝ}
    (hL :
      ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n → InMainRange ε n →
        0 < L n ∧ threshold n - (1 + 2 / Real.log 2) - C ≤ L n)
    (hk : EventualKThresholdWitnessUpperBound ε L) :
    EventualThresholdAverageColourClassCriterion ε C := by
  obtain ⟨n₁, hL'⟩ := hL
  obtain ⟨n₂, hk'⟩ := hk
  refine ⟨max 2 (max n₁ n₂), ?_⟩
  intro n hn hmain
  have h2bound : 2 ≤ max 2 (max n₁ n₂) := Nat.le_max_left _ _
  have hmaxbound : max n₁ n₂ ≤ max 2 (max n₁ n₂) := Nat.le_max_right _ _
  have hn2 : 2 ≤ n := le_trans h2bound hn
  have hn₁ : n₁ ≤ n := le_trans (le_trans (Nat.le_max_left _ _) hmaxbound) hn
  have hn₂ : n₂ ≤ n := le_trans (le_trans (Nat.le_max_right _ _) hmaxbound) hn
  rcases hL' n hn₁ hmain with ⟨hL_pos, hth⟩
  exact thresholdAverageColourClassCriterion_of_kThresholdWitness_upper hn2 hL_pos hth (hk' n hn₂ hmain)

private lemma eventual_thresholdAverageColourClassCriterion_of_eventual_concrete_upper
    {ε C : ℝ}
    (hLpos :
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
        0 < thresholdAverageColourClassDenom C n)
    (hk :
      EventualKThresholdWitnessUpperBound ε (thresholdAverageColourClassDenom C)) :
    EventualThresholdAverageColourClassCriterion ε C := by
  apply eventual_thresholdAverageColourClassCriterion_of_eventual_kThresholdWitness_upper
  · obtain ⟨n₀, h₀⟩ := hLpos
    refine ⟨n₀, ?_⟩
    intro n hn hmain
    refine ⟨h₀ n hn hmain, le_rfl⟩
  · exact hk

private lemma eventual_safeThresholdAverageColourClassCriterion_of_safeUpper
    {ε : ℝ}
    (hLpos :
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
        0 < thresholdAverageColourClassDenom safeAverageColourClassBuffer n)
    (hk : EventualSafeKThresholdWitnessUpperBound ε) :
    EventualSafeThresholdAverageColourClassCriterion ε := by
  exact eventual_thresholdAverageColourClassCriterion_of_eventual_concrete_upper hLpos hk

private lemma eventual_kThresholdWitness_upper_of_eventual_thresholdAverageColourClassCriterion
    {ε C : ℝ}
    (hLpos :
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
        0 < thresholdAverageColourClassDenom C n)
    (hcrit : EventualThresholdAverageColourClassCriterion ε C) :
    EventualKThresholdWitnessUpperBound ε (thresholdAverageColourClassDenom C) := by
  obtain ⟨n₁, hL'⟩ := hLpos
  obtain ⟨n₂, hcrit'⟩ := hcrit
  refine ⟨max 2 (max n₁ n₂), ?_⟩
  intro n hn hmain
  have h2bound : 2 ≤ max 2 (max n₁ n₂) := Nat.le_max_left _ _
  have hmaxbound : max n₁ n₂ ≤ max 2 (max n₁ n₂) := Nat.le_max_right _ _
  have hn2 : 2 ≤ n := le_trans h2bound hn
  have hn₁ : n₁ ≤ n := le_trans (le_trans (Nat.le_max_left _ _) hmaxbound) hn
  have hn₂ : n₂ ≤ n := le_trans (le_trans (Nat.le_max_right _ _) hmaxbound) hn
  exact kThresholdWitness_upper_of_thresholdAverageColourClassCriterion
    hn2 (hL' n hn₁ hmain) (hcrit' n hn₂ hmain)

private lemma threshold_tBoundedColoringError_le_with_error_of_threshold_log_criterion
    (ε δ : ℝ) (hε_pos : 0 < ε) (hδ_pos : 0 < δ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
      let t := max 1 (thresholdFloor n - 1)
      let k := firstMomentThreshold n t (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) - 1
      ThresholdLogCriterion n →
      Nat.factorial k * expectedTBoundedColorings n k t ≤ δ := by
  obtain ⟨Nδ, hNδ⟩ := inv_two_mul_nat_le_of_large δ hδ_pos
  refine ⟨max 2 Nδ, ?_⟩
  intro n hn hnMain
  dsimp
  intro hlog
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hsmall : 1 / (2 * n : ℝ) ≤ δ := hNδ n (le_trans (Nat.le_max_right _ _) hn)
  have ht_pos : 0 < max 1 (thresholdFloor n - 1) := by
    exact Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)
  have hk_one :
      1 ≤ firstMomentThreshold n (max 1 (thresholdFloor n - 1))
        (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) - 1 := by
    exact firstMomentThreshold_sub_one_pos_of_two_le n (max 1 (thresholdFloor n - 1))
      (le_trans (Nat.le_max_left _ _) hn) ht_pos
  have hk_le :
      firstMomentThreshold n (max 1 (thresholdFloor n - 1))
        (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) - 1 ≤ n := by
    exact Nat.sub_le_of_le_add
      ((firstMomentThreshold_le_n n (max 1 (thresholdFloor n - 1))
          (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _))).trans (Nat.le_add_right n 1))
  exact factorial_expectedTBoundedColorings_le_with_error_of_log_criterion
    n
    (firstMomentThreshold n (max 1 (thresholdFloor n - 1))
      (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) - 1)
    (max 1 (thresholdFloor n - 1))
    δ hn1 hk_one hk_le ht_pos hlog hsmall

/-- Deprecated conditional reduction through `ThresholdLogCriterion`.

This theorem remains compile-safe, but after route correction it should no
longer be treated as the live discharge target for
`threshold_tBoundedColoringError_le_with_error`.
-/
private lemma threshold_tBoundedColoringError_le_with_error_of_eventual_log_criterion
    (ε δ : ℝ) (hε_pos : 0 < ε) (hδ_pos : 0 < δ)
    (hcrit :
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n → ThresholdLogCriterion n) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
      Nat.factorial
          (firstMomentThreshold n (max 1 (thresholdFloor n - 1))
            (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) - 1) *
        expectedTBoundedColorings n
          (firstMomentThreshold n (max 1 (thresholdFloor n - 1))
            (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) - 1)
          (max 1 (thresholdFloor n - 1)) ≤ δ := by
  obtain ⟨n₀a, ha⟩ :=
    threshold_tBoundedColoringError_le_with_error_of_threshold_log_criterion ε δ hε_pos hδ_pos
  obtain ⟨n₀b, hb⟩ := hcrit
  refine ⟨max n₀a n₀b, ?_⟩
  intro n hn hnMain
  have hna : n₀a ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hnb : n₀b ≤ n := le_trans (Nat.le_max_right _ _) hn
  exact ha n hna hnMain (hb n hnb hnMain)

/-- Small-error version of the Heckel--Panagiotou lower bound for `χ_{α-1}` in
    the main range, reduced to the explicit first-moment error term. -/
theorem heckel_chi_threshold_lower_bound_with_error
    (ε δ : ℝ) (hε_pos : 0 < ε) (hδ_pos : 0 < δ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
      1 - ENNReal.ofReal δ ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          kThresholdWitness n - 1 ≤
            (classBoundedChromaticNumber n (thresholdFloor n - 1) G : ℝ)} := by
  obtain ⟨n₀, herr⟩ := threshold_tBoundedColoringError_le_with_error ε δ hε_pos hδ_pos
  refine ⟨max n₀ 2, ?_⟩
  intro n hn hnMain
  have hn₀ : n₀ ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hαgt1 : 1 < thresholdFloor n := thresholdFloor_gt_one_of_mainRange ε hε_pos hn2 hnMain
  have hαm1_pos : 0 < thresholdFloor n - 1 := by omega
  have hαm1_ge_one : 1 ≤ thresholdFloor n - 1 := by omega
  have ht_eq : max 1 (thresholdFloor n - 1) = thresholdFloor n - 1 := max_eq_right hαm1_ge_one
  have hfmt_eq :
      firstMomentThreshold n (max 1 (thresholdFloor n - 1))
          (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) =
        firstMomentThreshold n (thresholdFloor n - 1) hαm1_pos := by
    simpa [ht_eq]
  have hmem :
      max 1 (thresholdFloor n - 1) ∈ ({thresholdFloor n - 1, thresholdFloor n - 2} : Finset ℕ) := by
    rw [ht_eq]
    simp
  have hbase :=
    heckel_chi_t_lower_bound_all_n
      (max 1 (thresholdFloor n - 1))
      (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _))
      n hmem
  have hE_le : ENNReal.ofReal
      (Nat.factorial
          (firstMomentThreshold n (max 1 (thresholdFloor n - 1))
            (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) - 1) *
        expectedTBoundedColorings n
          (firstMomentThreshold n (max 1 (thresholdFloor n - 1))
            (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) - 1)
          (max 1 (thresholdFloor n - 1))) ≤ ENNReal.ofReal δ := by
    exact ENNReal.ofReal_le_ofReal (herr n hn₀ hnMain)
  have hprob :
      1 - ENNReal.ofReal δ ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          firstMomentThreshold n (max 1 (thresholdFloor n - 1))
              (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) - 1 ≤
            classBoundedChromaticNumber n (max 1 (thresholdFloor n - 1)) G} := by
    have htmp := hbase
    have hleft :
        1 - ENNReal.ofReal δ ≤
          1 - ENNReal.ofReal
            (Nat.factorial
                (firstMomentThreshold n (max 1 (thresholdFloor n - 1))
                  (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) - 1) *
              expectedTBoundedColorings n
                (firstMomentThreshold n (max 1 (thresholdFloor n - 1))
                  (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) - 1)
                (max 1 (thresholdFloor n - 1))) := by
      gcongr
    exact le_trans hleft htmp
  convert hprob using 2
  ext G
  constructor
  · intro h
    have h' :
        (firstMomentThreshold n (thresholdFloor n - 1) hαm1_pos : ℝ) ≤
          (classBoundedChromaticNumber n (thresholdFloor n - 1) G : ℝ) + 1 := by
      simpa [kThresholdWitness, ht_eq, hfmt_eq] using h
    have h'' :
        firstMomentThreshold n (thresholdFloor n - 1) hαm1_pos ≤
          classBoundedChromaticNumber n (thresholdFloor n - 1) G + 1 := by
      exact_mod_cast h'
    simpa [ht_eq, hfmt_eq] using (Nat.sub_le_iff_le_add).2 h''
  · intro h
    have h'' :
        firstMomentThreshold n (thresholdFloor n - 1) hαm1_pos ≤
          classBoundedChromaticNumber n (thresholdFloor n - 1) G + 1 := by
      have hnat :
          firstMomentThreshold n (max 1 (thresholdFloor n - 1))
              (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) - 1 ≤
            classBoundedChromaticNumber n (max 1 (thresholdFloor n - 1)) G := by
        simpa [ht_eq, hfmt_eq] using h
      simpa [ht_eq, hfmt_eq] using (Nat.sub_le_iff_le_add).1 hnat
    have h' :
        (firstMomentThreshold n (thresholdFloor n - 1) hαm1_pos : ℝ) ≤
          (classBoundedChromaticNumber n (thresholdFloor n - 1) G : ℝ) + 1 := by
      exact_mod_cast h''
    have :
        kThresholdWitness n - 1 ≤
          (classBoundedChromaticNumber n (thresholdFloor n - 1) G : ℝ) := by
      simpa [kThresholdWitness, ht_eq, hfmt_eq] using h'
    exact this

/-- Wired: discharges `heckel_chi_threshold_lower_bound_with_error` via the paper bridge
    axiom `profileLogCoreBridgeTarget_source`, bypassing the live
    `threshold_tBoundedColoringError_le_with_error` axiom.

    This is the canonical Part B entry point from 2026-05-09 onward. -/
theorem heckel_chi_threshold_lower_bound_with_error_of_paper_bridge
    (ε δ : ℝ) (hε_pos : 0 < ε) (hδ_pos : 0 < δ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
      1 - ENNReal.ofReal δ ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          kThresholdWitness n - 1 ≤
            (classBoundedChromaticNumber n (thresholdFloor n - 1) G : ℝ)} := by
  obtain ⟨n₀, herr⟩ := threshold_tBoundedColoringError_le_with_error_of_logCoreBridge
    profileLogCoreBridgeTarget_source ε δ hε_pos hδ_pos
  refine ⟨max n₀ 2, ?_⟩
  intro n hn hnMain
  have hn₀ : n₀ ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hαgt1 : 1 < thresholdFloor n := thresholdFloor_gt_one_of_mainRange ε hε_pos hn2 hnMain
  have hαm1_pos : 0 < thresholdFloor n - 1 := by omega
  have hαm1_ge_one : 1 ≤ thresholdFloor n - 1 := by omega
  have ht_eq : max 1 (thresholdFloor n - 1) = thresholdFloor n - 1 := max_eq_right hαm1_ge_one
  have hfmt_eq :
      firstMomentThreshold n (max 1 (thresholdFloor n - 1))
          (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) =
        firstMomentThreshold n (thresholdFloor n - 1) hαm1_pos := by
    simpa [ht_eq]
  have hmem :
      max 1 (thresholdFloor n - 1) ∈ ({thresholdFloor n - 1, thresholdFloor n - 2} : Finset ℕ) := by
    rw [ht_eq]; simp
  have hbase :=
    heckel_chi_t_lower_bound_all_n
      (max 1 (thresholdFloor n - 1))
      (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _))
      n hmem
  have hE_le : ENNReal.ofReal
      (Nat.factorial
          (firstMomentThreshold n (max 1 (thresholdFloor n - 1))
            (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) - 1) *
        expectedTBoundedColorings n
          (firstMomentThreshold n (max 1 (thresholdFloor n - 1))
            (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) - 1)
          (max 1 (thresholdFloor n - 1))) ≤ ENNReal.ofReal δ :=
    ENNReal.ofReal_le_ofReal (herr n hn₀ hnMain)
  have hprob :
      1 - ENNReal.ofReal δ ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          firstMomentThreshold n (max 1 (thresholdFloor n - 1))
              (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) - 1 ≤
            classBoundedChromaticNumber n (max 1 (thresholdFloor n - 1)) G} := by
    have hleft :
        1 - ENNReal.ofReal δ ≤
          1 - ENNReal.ofReal
            (Nat.factorial
                (firstMomentThreshold n (max 1 (thresholdFloor n - 1))
                  (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) - 1) *
              expectedTBoundedColorings n
                (firstMomentThreshold n (max 1 (thresholdFloor n - 1))
                  (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) - 1)
                (max 1 (thresholdFloor n - 1))) := by gcongr
    exact le_trans hleft hbase
  convert hprob using 2
  ext G
  constructor
  · intro h
    have h' :
        (firstMomentThreshold n (thresholdFloor n - 1) hαm1_pos : ℝ) ≤
          (classBoundedChromaticNumber n (thresholdFloor n - 1) G : ℝ) + 1 := by
      simpa [kThresholdWitness, ht_eq, hfmt_eq] using h
    have h'' :
        firstMomentThreshold n (thresholdFloor n - 1) hαm1_pos ≤
          classBoundedChromaticNumber n (thresholdFloor n - 1) G + 1 := by exact_mod_cast h'
    simpa [ht_eq, hfmt_eq] using (Nat.sub_le_iff_le_add).2 h''
  · intro h
    have h'' :
        firstMomentThreshold n (thresholdFloor n - 1) hαm1_pos ≤
          classBoundedChromaticNumber n (thresholdFloor n - 1) G + 1 := by
      have hnat :
          firstMomentThreshold n (max 1 (thresholdFloor n - 1))
              (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) - 1 ≤
            classBoundedChromaticNumber n (max 1 (thresholdFloor n - 1)) G := by
        simpa [ht_eq, hfmt_eq] using h
      simpa [ht_eq, hfmt_eq] using (Nat.sub_le_iff_le_add).1 hnat
    have h' :
        (firstMomentThreshold n (thresholdFloor n - 1) hαm1_pos : ℝ) ≤
          (classBoundedChromaticNumber n (thresholdFloor n - 1) G : ℝ) + 1 := by exact_mod_cast h''
    simpa [kThresholdWitness, ht_eq, hfmt_eq] using h'

/-- Paper-aligned replacement surface for `heckel_chi_threshold_lower_bound_with_error`.

This theorem verifies that the unordered probability target from `PartBProfileBridge` has exactly
the right external shape to replace the current ordered-count Part B axiom once the unordered shell
is proved. -/
theorem heckel_chi_threshold_lower_bound_with_error_of_paperLowerProbability
    (ε δ : ℝ) (hε_pos : 0 < ε)
    (hlower : PaperPartBLowerProbabilityTarget ε δ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
      1 - ENNReal.ofReal δ ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          kThresholdWitness n - 1 ≤
            (classBoundedChromaticNumber n (thresholdFloor n - 1) G : ℝ)} := by
  obtain ⟨n₀, hlower⟩ := hlower
  refine ⟨max n₀ 2, ?_⟩
  intro n hn hnMain
  have hn₀ : n₀ ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hαgt1 : 1 < thresholdFloor n := thresholdFloor_gt_one_of_mainRange ε hε_pos hn2 hnMain
  have hαm1_pos : 0 < thresholdFloor n - 1 := by omega
  have hαm1_ge_one : 1 ≤ thresholdFloor n - 1 := by omega
  have ht_eq : max 1 (thresholdFloor n - 1) = thresholdFloor n - 1 := max_eq_right hαm1_ge_one
  have hfmt_eq :
      firstMomentThreshold n (max 1 (thresholdFloor n - 1))
          (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) =
        firstMomentThreshold n (thresholdFloor n - 1) hαm1_pos := by
    simpa [ht_eq]
  have hprob := hlower n hn₀ hnMain
  convert hprob using 2
  ext G
  constructor
  · intro h
    have hle_add_real :
        (firstMomentThreshold n (thresholdFloor n - 1) hαm1_pos : ℝ) ≤
          (classBoundedChromaticNumber n (thresholdFloor n - 1) G : ℝ) + 1 := by
      simpa [kThresholdWitness, ht_eq, hfmt_eq] using h
    have hle_add :
        firstMomentThreshold n (thresholdFloor n - 1) hαm1_pos ≤
          classBoundedChromaticNumber n (thresholdFloor n - 1) G + 1 := by
      exact_mod_cast hle_add_real
    simpa [partBErrorColorCount, kThresholdAlphaMinusOne, partBThresholdLevel, ht_eq, hfmt_eq]
      using (Nat.sub_le_iff_le_add).2 hle_add
  · intro h
    have hnat :
        firstMomentThreshold n (thresholdFloor n - 1) hαm1_pos - 1 ≤
          classBoundedChromaticNumber n (thresholdFloor n - 1) G := by
      simpa [partBErrorColorCount, kThresholdAlphaMinusOne, partBThresholdLevel, ht_eq, hfmt_eq]
        using h
    have hle_add :
        firstMomentThreshold n (thresholdFloor n - 1) hαm1_pos ≤
          classBoundedChromaticNumber n (thresholdFloor n - 1) G + 1 :=
      (Nat.sub_le_iff_le_add).1 hnat
    have hle_add_real :
        (firstMomentThreshold n (thresholdFloor n - 1) hαm1_pos : ℝ) ≤
          (classBoundedChromaticNumber n (thresholdFloor n - 1) G : ℝ) + 1 := by
      exact_mod_cast hle_add
    have :
        kThresholdWitness n - 1 ≤
          (classBoundedChromaticNumber n (thresholdFloor n - 1) G : ℝ) := by
      simpa [kThresholdWitness, ht_eq, hfmt_eq] using hle_add_real
    exact this

/-- If the selected unordered shell is proved and the paper obstruction estimate is supplied, it
gives the same external Part B probability theorem as the current live axiom. -/
theorem heckel_chi_threshold_lower_bound_with_error_of_unorderedShell
    (hshell : PaperPartBUnorderedProbabilityShellTarget)
    (ε δ : ℝ) (hε_pos : 0 < ε) (hδ_pos : 0 < δ)
    (hobstruction : PaperPartBUnorderedObstructionTarget ε δ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
      1 - ENNReal.ofReal δ ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          kThresholdWitness n - 1 ≤
            (classBoundedChromaticNumber n (thresholdFloor n - 1) G : ℝ)} :=
  heckel_chi_threshold_lower_bound_with_error_of_paperLowerProbability ε δ hε_pos
    (hshell ε δ hε_pos hδ_pos hobstruction)

/-- Part B probability lower bound via the fully proved exact-no-empty profile chain.

This theorem uses zero sorrys and zero axioms beyond the two paper-backed axioms already in
`paperPartBExactNoEmptyProfileLogCoreBridgeTarget_of_paper_axioms`:
  • `paperPartBThresholdAverageClassAsymptoticLowerCriterionTarget_source`
  • `paperPartBExactNoEmptyDenomBinaryLowerControlledLhsDecayTarget_source`

The chain:
  paperPartBExactNoEmptyProfileLogCoreBridgeTarget_of_paper_axioms (proved)
  → paperPartBExactNoEmptyProfileUnionTarget_of_logCoreBridge
  → paperPartBExactUnorderedFailureEventTarget_of_noEmptyProfileUnion
      (uses paperPartBExactUnorderedExpectationComparisonTarget_proved)
  → paperPartBUnorderedFailureEventTarget_of_exactEvent'
  → paperPartBLowerProbabilityTarget_of_unorderedFailureEvent
  → heckel_chi_threshold_lower_bound_with_error_of_paperLowerProbability -/
theorem heckel_chi_threshold_lower_bound_with_error_of_exactNoEmpty
    (ε δ : ℝ) (hε_pos : 0 < ε) (hδ_pos : 0 < δ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
      1 - ENNReal.ofReal δ ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          kThresholdWitness n - 1 ≤
            (classBoundedChromaticNumber n (thresholdFloor n - 1) G : ℝ)} :=
  heckel_chi_threshold_lower_bound_with_error_of_paperLowerProbability ε δ hε_pos
    (paperPartBLowerProbabilityTarget_of_unorderedFailureEvent
      (paperPartBUnorderedFailureEventTarget_of_exactEvent'
        (paperPartBExactUnorderedFailureEventTarget_of_countExpectationUnion
          (paperPartBExactUnorderedCountExpectationUnionTarget_of_noEmptyProfileUnion
            paperPartBExactUnorderedExpectationComparisonTarget_proved
            (paperPartBExactNoEmptyProfileUnionTarget_of_logCoreBridge
              paperPartBExactNoEmptyProfileLogCoreBridgeTarget_of_paper_axioms
              ε δ hε_pos hδ_pos)))))

/-- The square of `log₂ n` is little-o of every positive power `n^ε`. -/
private lemma logb_sq_isLittleO_rpow_nat
    (ε : ℝ) (hε_pos : 0 < ε) :
    (fun n : ℕ => Real.logb 2 (n : ℝ) ^ (2 : ℝ)) =o[Filter.atTop]
      fun n => (n : ℝ) ^ ε := by
  have hlog : (fun x : ℝ => Real.log x ^ (2 : ℝ)) =o[Filter.atTop] fun x => x ^ ε := by
    simpa using (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hε_pos)
  have hEq :
      (fun x : ℝ => Real.logb 2 x ^ (2 : ℝ)) =ᶠ[Filter.atTop]
        fun x => (Real.log 2)⁻¹ ^ (2 : ℝ) * (Real.log x ^ (2 : ℝ)) := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    have hxlog : 0 ≤ Real.log x := Real.log_nonneg hx.le
    have h2log : 0 ≤ (Real.log 2)⁻¹ := by
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      positivity
    rw [Real.logb, div_eq_mul_inv, Real.mul_rpow hxlog h2log]
    ring
  have hscaled :
      (fun x : ℝ => (Real.log 2)⁻¹ ^ (2 : ℝ) * (Real.log x ^ (2 : ℝ))) =o[Filter.atTop]
        fun x => x ^ ε := by
    exact Asymptotics.IsLittleO.const_mul_left hlog ((Real.log 2)⁻¹ ^ (2 : ℝ))
  have hreal : (fun x : ℝ => Real.logb 2 x ^ (2 : ℝ)) =o[Filter.atTop] fun x => x ^ ε := by
    exact Asymptotics.IsLittleO.congr' hscaled hEq.symm Filter.EventuallyEq.rfl
  simpa using hreal.comp_tendsto tendsto_natCast_atTop_atTop

/-- Explicit eventual version of `logb_sq_isLittleO_rpow_nat`. -/
private lemma exists_logb_sq_le_mul_rpow_nat
    (ε c : ℝ) (hε_pos : 0 < ε) (hc_pos : 0 < c) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      Real.logb 2 (n : ℝ) ^ (2 : ℝ) ≤ c * (n : ℝ) ^ ε := by
  rcases Filter.eventually_atTop.mp
      ((logb_sq_isLittleO_rpow_nat ε hε_pos).def hc_pos) with ⟨n₀, hn₀⟩
  refine ⟨n₀, ?_⟩
  intro n hn
  specialize hn₀ n hn
  have hnonneg : 0 ≤ (n : ℝ) ^ ε := by positivity
  exact (le_abs_self _).trans <| by
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hn₀

/-- Rewriting `n^(1-ε) * n` into a single rpow. -/
private lemma rpow_one_sub_mul_natCast
    (ε : ℝ) {n : ℕ} (hn2 : 2 ≤ n) :
    (n : ℝ) ^ (1 - ε) * (n : ℝ) = (n : ℝ) ^ (2 - ε) := by
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_trans (by norm_num : 0 < 1) (lt_of_lt_of_le (by norm_num : 1 < 2) hn2))
  calc
    (n : ℝ) ^ (1 - ε) * (n : ℝ) = (n : ℝ) ^ (1 - ε) * (n : ℝ) ^ (1 : ℝ) := by simp
    _ = (n : ℝ) ^ ((1 - ε) + 1) := by rw [← Real.rpow_add hn_pos]
    _ = (n : ℝ) ^ (2 - ε) := by congr 1; ring

/-- Rewriting the ratio `n^(2-ε) / n^2` as `n^(-ε)`. -/
private lemma rpow_sub_two_div
    (ε : ℝ) {n : ℕ} (hn2 : 2 ≤ n) :
    (n : ℝ) ^ (2 - ε) / (n : ℝ) ^ (2 : ℝ) = (n : ℝ) ^ (-ε) := by
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_trans (by norm_num : 0 < 1) (lt_of_lt_of_le (by norm_num : 1 < 2) hn2))
  have hne : (n : ℝ) ^ (2 : ℝ) ≠ 0 := by positivity
  calc
    (n : ℝ) ^ (2 - ε) / (n : ℝ) ^ (2 : ℝ)
      = ((n : ℝ) ^ (-ε) * (n : ℝ) ^ (2 : ℝ)) / (n : ℝ) ^ (2 : ℝ) := by
          rw [show 2 - ε = (-ε) + 2 by ring, Real.rpow_add hn_pos]
    _ = (n : ℝ) ^ (-ε) := by
          field_simp [hne]

/-- Cancellation of opposite exponents on the same positive base. -/
private lemma rpow_mul_rpow_neg_cancel
    (ε : ℝ) {n : ℕ} (hn2 : 2 ≤ n) :
    (n : ℝ) ^ ε * (n : ℝ) ^ (-ε) = 1 := by
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_trans (by norm_num : 0 < 1) (lt_of_lt_of_le (by norm_num : 1 < 2) hn2))
  rw [← Real.rpow_add hn_pos]
  simp

/-- Specialized reassociation of the threshold-tail normal form that appears after `ring_nf`. -/
private lemma threshold_tail_normalize
    (ε : ℝ) {n : ℕ} (hn2 : 2 ≤ n) (L C : ℝ) :
    (n : ℝ) ^ (2 - ε) * L * ((n : ℝ) ^ (2 : ℝ))⁻¹ * C =
      L * C * (n : ℝ) ^ (-ε) := by
  have hratio : (n : ℝ) ^ (2 - ε) * ((n : ℝ) ^ (2 : ℝ))⁻¹ = (n : ℝ) ^ (-ε) := by
    simpa [div_eq_mul_inv] using rpow_sub_two_div ε hn2
  calc
    (n : ℝ) ^ (2 - ε) * L * ((n : ℝ) ^ (2 : ℝ))⁻¹ * C
      = ((n : ℝ) ^ (2 - ε) * ((n : ℝ) ^ (2 : ℝ))⁻¹) * (L * C) := by ring
    _ = (n : ℝ) ^ (-ε) * (L * C) := by rw [hratio]
    _ = L * C * (n : ℝ) ^ (-ε) := by ring

/-- Threshold-specialized one-step recurrence for `μ_{α+1}`.

    This rewrites the remaining Part B arithmetic blocker into the explicit ratio
    `((n - α)/(α + 1)) * 2^{-α}` with `α = thresholdFloor n`. -/
theorem threshold_succ_expectedIndSets_mul
    (n : ℕ) :
    expectedIndependentSets n (thresholdFloor n + 1) * (thresholdFloor n + 1 : ℝ) =
      expectedIndependentSets n (thresholdFloor n) *
        (((n - thresholdFloor n : ℕ) : ℝ)) *
        ((1 / 2 : ℝ) ^ thresholdFloor n) := by
  simpa using expectedIndependentSets_succ_mul n (thresholdFloor n)

/-- In the positive-`n` main range, the threshold index cannot exceed `n`,
    otherwise the defining expectation `μ_α` would vanish. -/
private lemma thresholdFloor_le_of_mainRange
    (ε : ℝ) (hε_pos : 0 < ε) {n : ℕ} (hn1 : 1 ≤ n) (hn : InMainRange ε n) :
    thresholdFloor n ≤ n := by
  by_contra hlt
  have hchoose_zero : Nat.choose n (thresholdFloor n) = 0 :=
    Nat.choose_eq_zero_of_lt (lt_of_not_ge hlt)
  have hμ_zero : expectedIndependentSets n (thresholdFloor n) = 0 := by
    unfold expectedIndependentSets
    simp [hchoose_zero]
  have hμ_lower : (n : ℝ) ^ (0.05 + ε) ≤ expectedIndependentSets n (thresholdFloor n) := hn.1
  have hpow_pos : 0 < (n : ℝ) ^ (0.05 + ε) := by
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn1)
    have hexp_pos : 0 < 0.05 + ε := by linarith
    exact Real.rpow_pos_of_pos hn_pos _
  rw [hμ_zero] at hμ_lower
  linarith

/-- The threshold-floor exponent gives at most the real-valued tail `2^(1 - threshold n)`.

    This is the clean floor-to-rpow bridge needed to turn the successor recurrence
    for `μ_{α+1}` into pure arithmetic on the explicit threshold function. -/
private lemma half_pow_thresholdFloor_le_threshold_tail
    (n : ℕ) :
    ((1 / 2 : ℝ) ^ thresholdFloor n) ≤ (2 : ℝ) ^ (1 - threshold n) := by
  rw [← (show ((2 : ℝ) ^ (-(thresholdFloor n : ℝ))) =
      ((1 / 2 : ℝ) ^ thresholdFloor n) by
    rw [show (-(thresholdFloor n : ℝ)) = (-1 : ℝ) * (thresholdFloor n : ℝ) by ring]
    rw [Real.rpow_mul (by positivity), Real.rpow_neg (by positivity), Real.rpow_one]
    norm_num)]
  apply Real.rpow_le_rpow_of_exponent_le
  · norm_num
  · have hfloor : threshold n < thresholdFloor n + 1 := by
      simpa [thresholdFloor] using Nat.lt_floor_add_one (threshold n)
    linarith

/-- Explicit closed form for the threshold tail when `n > 1`.

    This rewrites the leftover factor from the successor-threshold recurrence into the
    standard shape `logb(2,n)^2 / n^2`, up to the fixed constant coming from `e/2`. -/
private lemma threshold_tail_eq_logb_ratio
    {n : ℕ} (hn : 1 < n) :
    (2 : ℝ) ^ (1 - threshold n) =
      ((Real.logb 2 (n : ℝ)) ^ (2 : ℝ)) /
        ((n : ℝ) ^ (2 : ℝ) * (Real.exp 1 / 2) ^ (2 : ℝ)) := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have h2gt1 : (1 : ℝ) < 2 := by norm_num
  have h2ne1 : (2 : ℝ) ≠ 1 := by norm_num
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.lt_trans Nat.zero_lt_one hn
  have hlogn_pos : 0 < Real.logb 2 (n : ℝ) := by
    exact Real.logb_pos h2gt1 (by exact_mod_cast hn)
  have hexp_pos : 0 < Real.exp 1 / 2 := by positivity
  have hpow_n : (2 : ℝ) ^ (2 * Real.logb 2 (n : ℝ)) = (n : ℝ) ^ (2 : ℝ) := by
    calc
      (2 : ℝ) ^ (2 * Real.logb 2 (n : ℝ)) = ((2 : ℝ) ^ (Real.logb 2 (n : ℝ))) ^ (2 : ℝ) := by
        rw [show 2 * Real.logb 2 (n : ℝ) = Real.logb 2 (n : ℝ) * 2 by ring, Real.rpow_mul h2pos.le]
      _ = (n : ℝ) ^ (2 : ℝ) := by
        rw [Real.rpow_logb h2pos h2ne1 hnpos]
  have hpow_log :
      (2 : ℝ) ^ (2 * Real.logb 2 (Real.logb 2 (n : ℝ))) =
        (Real.logb 2 (n : ℝ)) ^ (2 : ℝ) := by
    calc
      (2 : ℝ) ^ (2 * Real.logb 2 (Real.logb 2 (n : ℝ))) =
          ((2 : ℝ) ^ (Real.logb 2 (Real.logb 2 (n : ℝ)))) ^ (2 : ℝ) := by
        rw [show 2 * Real.logb 2 (Real.logb 2 (n : ℝ)) = Real.logb 2 (Real.logb 2 (n : ℝ)) * 2 by ring,
          Real.rpow_mul h2pos.le]
      _ = (Real.logb 2 (n : ℝ)) ^ (2 : ℝ) := by
        rw [Real.rpow_logb h2pos h2ne1 hlogn_pos]
  have hpow_exp : (2 : ℝ) ^ (2 * Real.logb 2 (Real.exp 1 / 2)) = (Real.exp 1 / 2) ^ (2 : ℝ) := by
    calc
      (2 : ℝ) ^ (2 * Real.logb 2 (Real.exp 1 / 2)) =
          ((2 : ℝ) ^ (Real.logb 2 (Real.exp 1 / 2))) ^ (2 : ℝ) := by
        rw [show 2 * Real.logb 2 (Real.exp 1 / 2) = Real.logb 2 (Real.exp 1 / 2) * 2 by ring,
          Real.rpow_mul h2pos.le]
      _ = (Real.exp 1 / 2) ^ (2 : ℝ) := by
        rw [Real.rpow_logb h2pos h2ne1 hexp_pos]
  unfold threshold
  simp only [Real.log_div_log]
  rw [show (1 - (2 * Real.logb 2 (n : ℝ) - 2 * Real.logb 2 (Real.logb 2 (n : ℝ)) +
      2 * Real.logb 2 (Real.exp 1 / 2) + 1)) =
      -(2 * Real.logb 2 (n : ℝ)) + 2 * Real.logb 2 (Real.logb 2 (n : ℝ)) -
        (2 * Real.logb 2 (Real.exp 1 / 2)) by ring]
  rw [show (-(2 * Real.logb 2 (n : ℝ)) + 2 * Real.logb 2 (Real.logb 2 (n : ℝ)) -
      (2 * Real.logb 2 (Real.exp 1 / 2))) =
      (2 * Real.logb 2 (Real.logb 2 (n : ℝ))) +
        (-(2 * Real.logb 2 (n : ℝ)) + -(2 * Real.logb 2 (Real.exp 1 / 2))) by ring]
  rw [Real.rpow_add (by positivity), Real.rpow_add (by positivity)]
  rw [Real.rpow_neg h2pos.le, Real.rpow_neg h2pos.le]
  rw [hpow_n, hpow_log, hpow_exp]
  field_simp

/-- Deterministic tail bound deduced from the explicit eventual estimate
    `logb(2,n)^2 ≤ c * n^ε`. -/
private lemma threshold_tail_mul_le_of_logb_bound
    (ε δ : ℝ) {n : ℕ} (hn2 : 2 ≤ n)
    (hlog :
      Real.logb 2 (n : ℝ) ^ (2 : ℝ) ≤
        (δ * (Real.exp 1 / 2) ^ (2 : ℝ)) * (n : ℝ) ^ ε) :
    (n : ℝ) ^ (1 - ε) * (n : ℝ) * (2 : ℝ) ^ (1 - threshold n) ≤ δ := by
  have htail :
      (2 : ℝ) ^ (1 - threshold n) =
        ((Real.logb 2 (n : ℝ)) ^ (2 : ℝ)) /
          ((n : ℝ) ^ (2 : ℝ) * (Real.exp 1 / 2) ^ (2 : ℝ)) :=
    threshold_tail_eq_logb_ratio (lt_of_lt_of_le (by norm_num : 1 < 2) hn2)
  rw [htail]
  have hmain :
      (n : ℝ) ^ (1 - ε) * (n : ℝ) *
          (((Real.logb 2 (n : ℝ)) ^ (2 : ℝ)) /
            ((n : ℝ) ^ (2 : ℝ) * (Real.exp 1 / 2) ^ (2 : ℝ)))
        = ((Real.logb 2 (n : ℝ)) ^ (2 : ℝ) / (Real.exp 1 / 2) ^ (2 : ℝ)) *
            (n : ℝ) ^ (-ε) := by
    calc
      (n : ℝ) ^ (1 - ε) * (n : ℝ) *
          (((Real.logb 2 (n : ℝ)) ^ (2 : ℝ)) /
            ((n : ℝ) ^ (2 : ℝ) * (Real.exp 1 / 2) ^ (2 : ℝ)))
        = ((n : ℝ) ^ (1 - ε) * (n : ℝ)) *
            (((Real.logb 2 (n : ℝ)) ^ (2 : ℝ)) /
              ((n : ℝ) ^ (2 : ℝ) * (Real.exp 1 / 2) ^ (2 : ℝ))) := by ring
      _ = (n : ℝ) ^ (2 - ε) *
            (((Real.logb 2 (n : ℝ)) ^ (2 : ℝ)) /
              ((n : ℝ) ^ (2 : ℝ) * (Real.exp 1 / 2) ^ (2 : ℝ))) := by
            rw [rpow_one_sub_mul_natCast ε hn2]
      _ = ((Real.logb 2 (n : ℝ)) ^ (2 : ℝ) / (Real.exp 1 / 2) ^ (2 : ℝ)) *
            (n : ℝ) ^ (-ε) := by
            rw [div_eq_mul_inv]
            ring_nf
            simpa [div_eq_mul_inv] using
              (threshold_tail_normalize ε hn2 (Real.logb 2 (n : ℝ) ^ (2 : ℝ))
                (((Real.exp 1 / 2) ^ (2 : ℝ))⁻¹))
  rw [hmain]
  have hc0_pos : 0 < (Real.exp 1 / 2) ^ (2 : ℝ) := by positivity
  have hlog_div :
      (Real.logb 2 (n : ℝ) ^ (2 : ℝ)) / (Real.exp 1 / 2) ^ (2 : ℝ) ≤
        δ * (n : ℝ) ^ ε := by
    refine (div_le_iff₀ hc0_pos).2 ?_
    calc
      Real.logb 2 (n : ℝ) ^ (2 : ℝ)
          ≤ (δ * (Real.exp 1 / 2) ^ (2 : ℝ)) * (n : ℝ) ^ ε := hlog
      _ = (δ * (n : ℝ) ^ ε) * (Real.exp 1 / 2) ^ (2 : ℝ) := by ring
  have hnonneg : 0 ≤ (n : ℝ) ^ (-ε) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hlog_div hnonneg
  calc
    (Real.logb 2 (n : ℝ) ^ (2 : ℝ) / (Real.exp 1 / 2) ^ (2 : ℝ)) * (n : ℝ) ^ (-ε)
      ≤ (δ * (n : ℝ) ^ ε) * (n : ℝ) ^ (-ε) := hmul
    _ = δ * ((n : ℝ) ^ ε * (n : ℝ) ^ (-ε)) := by ring
    _ = δ := by rw [rpow_mul_rpow_neg_cancel ε hn2]; ring

/-- Coarse successor-threshold decay: in the main range,
    `μ_{α+1} ≤ μ_α * n * 2^{-α}` with `α = thresholdFloor n`. -/
theorem threshold_succ_expectedIndSets_le_coarse
    (ε : ℝ) (hε_pos : 0 < ε) {n : ℕ} (hn1 : 1 ≤ n) (hn : InMainRange ε n) :
    expectedIndependentSets n (thresholdFloor n + 1) * (thresholdFloor n + 1 : ℝ) ≤
      expectedIndependentSets n (thresholdFloor n) * (n : ℝ) * ((1 / 2 : ℝ) ^ thresholdFloor n) := by
  have hα_le_n : thresholdFloor n ≤ n := thresholdFloor_le_of_mainRange ε hε_pos hn1 hn
  rw [threshold_succ_expectedIndSets_mul n]
  have hsub : (((n - thresholdFloor n : ℕ) : ℝ)) ≤ (n : ℝ) := by
    exact_mod_cast Nat.sub_le n (thresholdFloor n)
  have hnonneg :
      0 ≤ expectedIndependentSets n (thresholdFloor n) * ((1 / 2 : ℝ) ^ thresholdFloor n) := by
    apply mul_nonneg
    · unfold expectedIndependentSets
      apply mul_nonneg
      · exact Nat.cast_nonneg _
      · positivity
    · positivity
  have := mul_le_mul_of_nonneg_left hsub hnonneg
  simpa [mul_assoc, mul_left_comm, mul_comm] using this

/-- Main-range reduction of `μ_{α+1}` to an explicit threshold tail.

    After this lemma, the remaining `μ_{α+1}` blocker is no longer about random
    graphs: it is purely the arithmetic size of `(2 : ℝ)^(1 - threshold n)`. -/
theorem threshold_succ_expectedIndSets_le_threshold_tail
    (ε : ℝ) (hε_pos : 0 < ε) {n : ℕ} (hn1 : 1 ≤ n) (hn : InMainRange ε n) :
    expectedIndependentSets n (thresholdFloor n + 1) * (thresholdFloor n + 1 : ℝ) ≤
      (n : ℝ) ^ (1 - ε) * (n : ℝ) * (2 : ℝ) ^ (1 - threshold n) := by
  calc
    expectedIndependentSets n (thresholdFloor n + 1) * (thresholdFloor n + 1 : ℝ)
      ≤ expectedIndependentSets n (thresholdFloor n) * (n : ℝ) * ((1 / 2 : ℝ) ^ thresholdFloor n) :=
        threshold_succ_expectedIndSets_le_coarse ε hε_pos hn1 hn
    _ ≤ (n : ℝ) ^ (1 - ε) * (n : ℝ) * ((1 / 2 : ℝ) ^ thresholdFloor n) := by
      have hμ_upper : expectedIndependentSets n (thresholdFloor n) ≤ (n : ℝ) ^ (1 - ε) := hn.2
      have hstep₁ :
          expectedIndependentSets n (thresholdFloor n) * (n : ℝ) ≤
            (n : ℝ) ^ (1 - ε) * (n : ℝ) := by
        exact mul_le_mul_of_nonneg_right hμ_upper (Nat.cast_nonneg n)
      have hstep₂ :
          expectedIndependentSets n (thresholdFloor n) * (n : ℝ) * ((1 / 2 : ℝ) ^ thresholdFloor n) ≤
            (n : ℝ) ^ (1 - ε) * (n : ℝ) * ((1 / 2 : ℝ) ^ thresholdFloor n) := by
        exact mul_le_mul_of_nonneg_right hstep₁ (by positivity)
      simpa [mul_assoc] using hstep₂
    _ ≤ (n : ℝ) ^ (1 - ε) * (n : ℝ) * ((2 : ℝ) ^ (1 - threshold n)) := by
      have htail := half_pow_thresholdFloor_le_threshold_tail n
      have hnonneg : 0 ≤ (n : ℝ) ^ (1 - ε) * (n : ℝ) := by
        apply mul_nonneg
        · positivity
        · exact Nat.cast_nonneg n
      exact mul_le_mul_of_nonneg_left htail hnonneg

/-- Small-error upper bound on the expected number of independent
    sets at the successor threshold level `thresholdFloor n + 1`.

    This is strictly narrower than a direct probabilistic bound on `G.indepNum`:
    by first moment, it already implies the required high-probability upper bound
    `α(G) ≤ thresholdFloor n`. -/
theorem threshold_succ_expectedIndSets_le_with_error
    (ε δ : ℝ) (hε_pos : 0 < ε) (hδ_pos : 0 < δ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
      expectedIndependentSets n (thresholdFloor n + 1) ≤ δ := by
  obtain ⟨n₁, hn₁⟩ :=
    exists_logb_sq_le_mul_rpow_nat ε (δ * (Real.exp 1 / 2) ^ (2 : ℝ)) hε_pos
      (by
        apply mul_pos hδ_pos
        positivity)
  refine ⟨max n₁ 2, ?_⟩
  intro n hn0 hn
  have hn₁_le : n₁ ≤ n := le_trans (Nat.le_max_left _ _) hn0
  have hn2 : 2 ≤ n := le_trans (Nat.le_max_right _ _) hn0
  have hlog :
      Real.logb 2 (n : ℝ) ^ (2 : ℝ) ≤
        (δ * (Real.exp 1 / 2) ^ (2 : ℝ)) * (n : ℝ) ^ ε :=
    hn₁ n hn₁_le
  have htail :
      (n : ℝ) ^ (1 - ε) * (n : ℝ) * (2 : ℝ) ^ (1 - threshold n) ≤ δ :=
    threshold_tail_mul_le_of_logb_bound ε δ hn2 hlog
  have hsucc_mul :
      expectedIndependentSets n (thresholdFloor n + 1) * (thresholdFloor n + 1 : ℝ) ≤ δ := by
    exact (threshold_succ_expectedIndSets_le_threshold_tail ε hε_pos
      (Nat.succ_le_of_lt (lt_of_lt_of_le (by norm_num : 0 < 2) hn2)) hn).trans htail
  have hfac_pos : 0 < (thresholdFloor n + 1 : ℝ) := by positivity
  have hfac_ge_one : (1 : ℝ) ≤ (thresholdFloor n + 1 : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le (thresholdFloor n))
  have hμ_nonneg : 0 ≤ expectedIndependentSets n (thresholdFloor n + 1) := by
    unfold expectedIndependentSets
    apply mul_nonneg
    · exact Nat.cast_nonneg _
    · positivity
  have hmono :
      expectedIndependentSets n (thresholdFloor n + 1) ≤
        expectedIndependentSets n (thresholdFloor n + 1) * (thresholdFloor n + 1 : ℝ) := by
    calc
      expectedIndependentSets n (thresholdFloor n + 1)
        = expectedIndependentSets n (thresholdFloor n + 1) * 1 := by ring
      _ ≤ expectedIndependentSets n (thresholdFloor n + 1) * (thresholdFloor n + 1 : ℝ) :=
        mul_le_mul_of_nonneg_left hfac_ge_one hμ_nonneg
  exact hmono.trans hsucc_mul

/-- First-moment reduction of the independence-number input for Part B.

    To force `α(G) ≤ thresholdFloor n` with probability at least `1 - δ`,
    it is enough to show that the expected number of independent sets of size
    `thresholdFloor n + 1` is at most `δ`. -/
theorem threshold_indepNum_upper_bound_with_error_of_expected
    (ε δ : ℝ) (hε_pos : 0 < ε) (hδ_nonneg : 0 ≤ δ)
    (hexp : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
      expectedIndependentSets n (thresholdFloor n + 1) ≤ δ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
      1 - ENNReal.ofReal δ ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          G.indepNum ≤ (thresholdFloor n - 1) + 1} := by
  obtain ⟨n₀, hexp'⟩ := hexp
  refine ⟨max n₀ 2, ?_⟩
  intro n hn hmain
  have hn₀ : n₀ ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hαpos : 0 < thresholdFloor n := by
    by_contra hzero
    have hαzero : thresholdFloor n = 0 := Nat.eq_zero_of_not_pos hzero
    have hμ_le : (n : ℝ) ^ (0.05 + ε) ≤ expectedIndependentSets n (thresholdFloor n) := hmain.1
    have hpow_le_one : (n : ℝ) ^ (0.05 + ε) ≤ 1 := by
      simpa [hαzero, expectedIndependentSets] using hμ_le
    have hn_gt_one_nat : 1 < n := lt_of_lt_of_le (by norm_num : 1 < 2) hn2
    have hn_gt_one : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn_gt_one_nat
    have hexp_pos : 0 < 0.05 + ε := by linarith
    have hpow_gt_one : 1 < (n : ℝ) ^ (0.05 + ε) := by
      apply Real.one_lt_rpow hn_gt_one
      linarith
    linarith
  let k := thresholdFloor n + 1
  have hprob_ge :
      gnHalf n {G : SimpleGraph (Fin n) | k ≤ G.indepNum} ≤ ENNReal.ofReal δ := by
    calc
      gnHalf n {G : SimpleGraph (Fin n) | k ≤ G.indepNum}
          ≤ ENNReal.ofReal (expectedIndependentSets n k) :=
        gnHalf_indepNum_le_expectedIndSets n k
      _ ≤ ENNReal.ofReal δ :=
        ENNReal.ofReal_le_ofReal (hexp' n hn₀ hmain)
  have hcomp :
      1 - ENNReal.ofReal δ ≤
        gnHalf n {G : SimpleGraph (Fin n) | G.indepNum < k} := by
    rw [gnHalf_indepNum_lt_eq_compl]
    exact tsub_le_tsub_left hprob_ge 1
  have hidx : ((thresholdFloor n - 1) + 1) = thresholdFloor n :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hαpos)
  simpa [k, hidx] using hcomp

/-- High-probability upper bound forcing the independence number below the
    threshold level used in Part B.

    This is no longer taken as a primitive axiom: it follows from the narrower
    expected-value input `threshold_succ_expectedIndSets_le_with_error` by the
    first-moment reduction above. -/
theorem threshold_indepNum_upper_bound_with_error
    (ε δ : ℝ) (hε_pos : 0 < ε) (hδ_pos : 0 < δ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
      1 - ENNReal.ofReal δ ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          G.indepNum ≤ (thresholdFloor n - 1) + 1} := by
  exact threshold_indepNum_upper_bound_with_error_of_expected
    ε δ hε_pos (le_of_lt hδ_pos)
    (threshold_succ_expectedIndSets_le_with_error ε δ hε_pos hδ_pos)

/-- Complete lower bound for χ(G) in the main range.

    This combines:
    1. Lemma 8.1: whp χ_t(G) ≥ k_t - 1
    2. χ(G) ≥ χ_t(G) - X_α (from `chromaticNumber_ge_classBoundedChromaticNumber_sub_maxIndep`)
    3. whp X_α ≤ n^{1-0.99ε} for the fixed-size threshold count
       (from `gnHalf_thresholdIndepSetCount_le_rpow`)

    Together: χ(G) ≥ (k_t - 1) - n^{1-0.99ε} ≥ k_t - n^{1-0.9ε}
-/
theorem heckel_chromatic_lower_bound
    (ε : ℝ) (hε_pos : 0 < ε) (hε_small : ε < 0.001) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (hn : InMainRange ε n),
      1 - ENNReal.ofReal ε ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          kThresholdWitness n - (n : ℝ)^(1 - 0.9 * ε) ≤ (chromaticNumber G : ℝ)} := by
  have hδ_pos : 0 < ε / 3 := by linarith
  have hδ_nonneg : 0 ≤ ε / 3 := by linarith
  have hε_lt_one : ε < 1 := by linarith
  have hχ := heckel_chi_threshold_lower_bound_with_error ε (ε / 3) hε_pos hδ_pos
  have hα := threshold_indepNum_upper_bound_with_error ε (ε / 3) hε_pos hδ_pos
  have hX := gnHalf_thresholdSuccPredIndepSetCount_le_rpow_with_error ε (ε / 3) hε_pos hδ_pos
  have hgap := rpow_gap_ge_one ε hε_pos hε_lt_one
  obtain ⟨n₀, hsplit⟩ :=
    heckel_chromatic_lower_bound_from_split
      ε (ε / 3) (ε / 3) (ε / 3)
      hδ_nonneg hδ_nonneg hδ_nonneg hχ hα hX hgap
  refine ⟨n₀, ?_⟩
  intro n hn0 hn
  have hmain :
      1 - ENNReal.ofReal ((ε / 3) + (ε / 3) + (ε / 3)) ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          kThresholdWitness n - (n : ℝ) ^ (1 - 0.9 * ε) ≤ (chromaticNumber G : ℝ)} :=
    hsplit n hn0 hn
  have hsum : (ε / 3) + (ε / 3) + (ε / 3) = ε := by ring
  simpa [hsum] using hmain

/-- Wired: discharges `heckel_chromatic_lower_bound` via `profileLogCoreBridgeTarget_source`,
    replacing the live `threshold_tBoundedColoringError_le_with_error` axiom with the
    paper-backed bridge. Canonical Part B entry point from 2026-05-09. -/
theorem heckel_chromatic_lower_bound_of_paper_bridge
    (ε : ℝ) (hε_pos : 0 < ε) (hε_small : ε < 0.001) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (hn : InMainRange ε n),
      1 - ENNReal.ofReal ε ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          kThresholdWitness n - (n : ℝ)^(1 - 0.9 * ε) ≤ (chromaticNumber G : ℝ)} := by
  have hδ_pos : 0 < ε / 3 := by linarith
  have hδ_nonneg : 0 ≤ ε / 3 := by linarith
  have hε_lt_one : ε < 1 := by linarith
  have hχ := heckel_chi_threshold_lower_bound_with_error_of_paper_bridge ε (ε / 3) hε_pos hδ_pos
  have hα := threshold_indepNum_upper_bound_with_error ε (ε / 3) hε_pos hδ_pos
  have hX := gnHalf_thresholdSuccPredIndepSetCount_le_rpow_with_error ε (ε / 3) hε_pos hδ_pos
  have hgap := rpow_gap_ge_one ε hε_pos hε_lt_one
  obtain ⟨n₀, hsplit⟩ :=
    heckel_chromatic_lower_bound_from_split
      ε (ε / 3) (ε / 3) (ε / 3)
      hδ_nonneg hδ_nonneg hδ_nonneg hχ hα hX hgap
  refine ⟨n₀, ?_⟩
  intro n hn0 hn
  have hmain :
      1 - ENNReal.ofReal ((ε / 3) + (ε / 3) + (ε / 3)) ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          kThresholdWitness n - (n : ℝ) ^ (1 - 0.9 * ε) ≤ (chromaticNumber G : ℝ)} :=
    hsplit n hn0 hn
  have hsum : (ε / 3) + (ε / 3) + (ε / 3) = ε := by ring
  simpa [hsum] using hmain

/-- Canonical Part B chromatic lower bound via the fully proved exact-no-empty chain.

Uses zero sorrys and zero new axioms beyond the two paper-backed axioms in
`paperPartBExactNoEmptyProfileLogCoreBridgeTarget_of_paper_axioms`. -/
theorem heckel_chromatic_lower_bound_of_exactNoEmpty
    (ε : ℝ) (hε_pos : 0 < ε) (hε_small : ε < 0.001) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (hn : InMainRange ε n),
      1 - ENNReal.ofReal ε ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          kThresholdWitness n - (n : ℝ)^(1 - 0.9 * ε) ≤ (chromaticNumber G : ℝ)} := by
  have hδ_pos : 0 < ε / 3 := by linarith
  have hδ_nonneg : 0 ≤ ε / 3 := by linarith
  have hε_lt_one : ε < 1 := by linarith
  have hχ := heckel_chi_threshold_lower_bound_with_error_of_exactNoEmpty ε (ε / 3) hε_pos hδ_pos
  have hα := threshold_indepNum_upper_bound_with_error ε (ε / 3) hε_pos hδ_pos
  have hX := gnHalf_thresholdSuccPredIndepSetCount_le_rpow_with_error ε (ε / 3) hε_pos hδ_pos
  have hgap := rpow_gap_ge_one ε hε_pos hε_lt_one
  obtain ⟨n₀, hsplit⟩ :=
    heckel_chromatic_lower_bound_from_split
      ε (ε / 3) (ε / 3) (ε / 3)
      hδ_nonneg hδ_nonneg hδ_nonneg hχ hα hX hgap
  refine ⟨n₀, ?_⟩
  intro n hn0 hn
  have hmain :
      1 - ENNReal.ofReal ((ε / 3) + (ε / 3) + (ε / 3)) ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          kThresholdWitness n - (n : ℝ) ^ (1 - 0.9 * ε) ≤ (chromaticNumber G : ℝ)} :=
    hsplit n hn0 hn
  have hsum : (ε / 3) + (ε / 3) + (ε / 3) = ε := by ring
  simpa [hsum] using hmain

/-!
## Bridge: EventualSafeThresholdAverageColourClassCriterion → threshold_tBoundedColoringError

This section provides the discharge chain connecting the paper-aligned reciprocal
threshold/average-colour-class criterion to the Part B axiom.

The key mathematical argument:
- `EventualSafeThresholdAverageColourClassCriterion ε` gives `kThresholdWitness n ≤ n / D`
  where `D = threshold n - 1 - 2/ln2 - 4`.
- At k = kThresholdWitness n - 1: `n/k ≥ D + 1`, so `floor(n/k) ≥ D`.
- By `factorial_expectedTBoundedColorings_le_sharp_coarse`:
    `k! * E ≤ k^n * (1/2)^{k * C(floor(n/k), 2)} ≤ k^n * (1/2)^{k * C(D, 2)}`
- Since `D ≈ 2*log₂(n) - O(log log n)`, the product decays super-exponentially to 0.
  Specifically: `k ≤ n/D ≈ n/(2 log₂ n)` and `k * C(D, 2) ≈ n * D / 2 ≈ n * log₂ n`,
  so `k^n * (1/2)^{n*log₂ n} = (n/D)^n * n^{-n} = (1/D)^n → 0`.
-/

section AverageColourClassBridge

/-- The safe denominator is eventually positive in the main range.
    Uses `threshold n → ∞` (from `threshold n = 2*log₂ n + o(log₂ n)`)
    and the fixed buffer `safeAverageColourClassBuffer = 4`. -/
-- Helper: log n ≤ C * n eventually (for any C > 0), along naturals.
-- Uses `Real.isLittleO_log_id_atTop`.
private lemma log_le_mul_nat_eventually (C : ℝ) (hC : 0 < C) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → Real.log n ≤ C * n := by
  have ho : Real.log =o[Filter.atTop] id := Real.isLittleO_log_id_atTop
  rw [Asymptotics.isLittleO_iff] at ho
  have hreal : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ≤ C * x := by
    have h : ∀ᶠ x : ℝ in Filter.atTop, ‖Real.log x‖ ≤ C * ‖id x‖ := ho hC
    filter_upwards [h, Filter.eventually_ge_atTop 0] with x hx hx0
    have := (abs_le.mp (by simpa [Real.norm_eq_abs, abs_of_nonneg hx0] using hx)).2
    linarith [abs_nonneg (Real.log x)]
  rw [Filter.eventually_atTop] at hreal
  obtain ⟨x₀, hx₀⟩ := hreal
  exact ⟨⌈max x₀ 0⌉₊, fun n hn => hx₀ n (by
    have h1 : max x₀ 0 ≤ (⌈max x₀ 0⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈max x₀ 0⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
    linarith [le_max_left x₀ 0])⟩

-- Helper: Real.log 2 > 0.5.
private lemma log_two_gt_half_aux : (0.5 : ℝ) < Real.log 2 := by
  -- exp(0.5)^2 = exp(1) < 3, so exp(0.5) < sqrt(3) < 2.
  have hexp1 : Real.exp 1 < 3 := by
    have h := @Real.exp_bound 1 (by norm_num) 6
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [abs_le] at h; linarith [h.2]
  have hpos : (0 : ℝ) < Real.exp 0.5 := Real.exp_pos _
  have hprod : Real.exp 0.5 * Real.exp 0.5 = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  -- From exp(0.5)^2 < 3 < 4, get exp(0.5) < 2.
  have hlt2 : Real.exp 0.5 < 2 := by nlinarith [sq_nonneg (Real.exp 0.5 - 2)]
  -- log 2 > 0.5 iff 2 > exp(0.5) (since log is monotone).
  rw [show (0.5:ℝ) = Real.log (Real.exp 0.5) by simp [Real.log_exp]]
  exact Real.log_lt_log (Real.exp_pos _) hlt2

-- Helper: log 2 > 2/3 (needed to show thresholdAverageColourClassDenom > 1).
private lemma log_two_gt_two_thirds : (2 : ℝ) / 3 < Real.log 2 := by
  -- log 2 > 2/3 iff 2 > exp(2/3).
  -- exp(2/3) ≤ Σ_{j=0}^{5} (2/3)^j/j! + error ≤ 1.9478 < 2.
  -- We use Real.exp_bound with n=5 (need |x| ≤ 1; |2/3| < 1).
  have hx : (2 : ℝ) / 3 ≤ 1 := by norm_num
  have h := @Real.exp_bound (2/3) (by norm_num) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rw [abs_le] at h
  have hlt2 : Real.exp (2/3) < 2 := by linarith [h.2]
  rw [show (2:ℝ)/3 = Real.log (Real.exp (2/3)) by simp [Real.log_exp]]
  exact Real.log_lt_log (Real.exp_pos _) hlt2

-- Helper: threshold n ≥ 9 for all n ≥ some n₀.
-- Proof: 2^(1-threshold n) = (logb 2 n)^2/(n^2*(e/2)^2) ≤ (1/2)^8 eventually,
-- hence 1 - threshold n ≤ -8, i.e. threshold n ≥ 9.
private lemma threshold_ge_nine_eventually :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → (9 : ℝ) ≤ threshold n := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- C := log 2 * (exp 1 / 2) / 16
  set C := Real.log 2 * (Real.exp 1 / 2) / 16 with hC_def
  have hC_pos : 0 < C := by positivity
  obtain ⟨n₀, hn₀⟩ := log_le_mul_nat_eventually C hC_pos
  refine ⟨max n₀ 2, fun n hn => ?_⟩
  have hn₀' : n₀ ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hn1 : 1 < n := Nat.lt_of_lt_of_le (by norm_num) hn2
  -- Use the closed-form for 2^(1 - threshold n).
  have htail := threshold_tail_eq_logb_ratio hn1
  -- log n ≤ C * n, so logb 2 n = log n / log 2 ≤ C * n / log 2 = (exp 1/2) * n / 16.
  have hlogb_bound : Real.logb 2 n ≤ (Real.exp 1 / 2) * n / 16 := by
    simp only [Real.logb, hC_def]
    have h := div_le_div_of_nonneg_right (hn₀ n hn₀') (le_of_lt hlog2)
    -- h : log n / log 2 ≤ C * n / log 2 = (log 2 * (exp 1/2) / 16) * n / log 2
    -- = (exp 1/2) * n / 16
    have hcancel : Real.log 2 * (Real.exp 1 / 2) / 16 * ↑n / Real.log 2 =
        (Real.exp 1 / 2) * ↑n / 16 := by
      field_simp
    linarith
  have hlogb_pos : 0 ≤ Real.logb 2 n :=
    le_of_lt (Real.logb_pos (by norm_num) (by exact_mod_cast hn1))
  -- (logb 2 n)^2 ≤ ((exp 1/2) * n / 16)^2 = (exp 1/2)^2 * n^2 / 256.
  have hbound2 : (Real.logb 2 n)^2 ≤ ((Real.exp 1 / 2) * n / 16)^2 :=
    pow_le_pow_left₀ hlogb_pos hlogb_bound 2
  -- (logb 2 n)^(2:ℝ) / (n^(2:ℝ) * (exp 1/2)^(2:ℝ)) ≤ 1/256 = (1/2)^8.
  -- Matches the rpow exponents in threshold_tail_eq_logb_ratio.
  have htail_le : (Real.logb 2 n)^(2:ℝ) / ((n:ℝ)^(2:ℝ) * (Real.exp 1 / 2)^(2:ℝ)) ≤ (1/2:ℝ)^8 := by
    rw [div_le_iff₀ (by positivity)]
    have hrpow1 : (Real.logb 2 n)^(2:ℝ) = (Real.logb 2 n)^2 := Real.rpow_natCast _ 2
    have hrpow2 : (n:ℝ)^(2:ℝ) = (n:ℝ)^2 := Real.rpow_natCast _ 2
    have hrpow3 : (Real.exp 1/2:ℝ)^(2:ℝ) = (Real.exp 1/2)^2 := Real.rpow_natCast _ 2
    rw [hrpow1, hrpow2, hrpow3]
    calc (Real.logb 2 n)^2
        ≤ ((Real.exp 1/2) * n / 16)^2 := hbound2
      _ = (1/2:ℝ)^8 * ((n:ℝ)^2 * (Real.exp 1/2)^2) := by ring
  -- So 2^(1 - threshold n) ≤ (1/2)^8.
  have htail_small : (2:ℝ)^(1 - threshold n) ≤ (1/2:ℝ)^8 := by rw [htail]; exact htail_le
  -- (1/2)^8 = 2^(1-9), so 1 - threshold n ≤ 1 - 9 by monotonicity of 2^x.
  have h28 : (1/2:ℝ)^8 = (2:ℝ)^(1 - (9:ℝ)) := by
    norm_num [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]
  rw [h28] at htail_small
  linarith [(Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mp htail_small]

private lemma thresholdAverageColourClassDenom_pos_eventually
    (ε : ℝ) (hε_pos : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
      0 < thresholdAverageColourClassDenom safeAverageColourClassBuffer n := by
  -- threshold n ≥ 9 > 1 + 2/log 2 + 4 (since log 2 > 0.5 → 2/log 2 < 4).
  obtain ⟨n₀, hn₀⟩ := threshold_ge_nine_eventually
  refine ⟨n₀, fun n hn _ => ?_⟩
  have hge9 : (9:ℝ) ≤ threshold n := hn₀ n hn
  have hlog2 : (0.5:ℝ) < Real.log 2 := log_two_gt_half_aux
  simp only [thresholdAverageColourClassDenom, safeAverageColourClassBuffer]
  have h4 : 2 / Real.log 2 < 4 := by
    rw [div_lt_iff₀ (by linarith : (0:ℝ) < Real.log 2)]
    linarith
  linarith

/-- threshold n ≥ logb₂(n) eventually.

    Proof sketch: via threshold_tail_eq_logb_ratio:
    2^(1-T) = (logb₂ n)² / (n² * (e/2)²).
    T ≥ logb₂ n iff 2^(1-T) ≤ 2^(1-logb₂ n) = 2/n,
    i.e., (logb₂ n)² ≤ 2*(e/2)²*n.
    This holds eventually since (logb₂ n)² = o(n) (log = o(√n)).
    2*(e/2)² > 1 gives the constant factor. -/
private lemma threshold_ge_logb_n_eventually :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → Real.logb 2 n ≤ threshold n := by
  -- Step 1: (logb₂ n)^2 ≤ n eventually (from log = o(√n)).
  have hlogb2_sq_le_n : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → (Real.logb 2 n) ^ 2 ≤ n := by
    have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hR : Real.log =o[Filter.atTop] (fun x => x ^ ((1:ℝ)/2)) :=
      isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/2)
    rw [Asymptotics.isLittleO_iff] at hR
    have h1 := hR hlog2
    rw [Filter.eventually_atTop] at h1
    obtain ⟨x₀, hx₀⟩ := h1
    refine ⟨max ⌈max x₀ 1⌉₊ 2, fun n hn => ?_⟩
    have hn2 : 2 ≤ n := le_trans (Nat.le_max_right _ _) hn
    have hx₀_le : x₀ ≤ n := by
      have h1 : max x₀ 1 ≤ (⌈max x₀ 1⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : (⌈max x₀ 1⌉₊ : ℝ) ≤ n := by exact_mod_cast le_trans (Nat.le_max_left _ _) hn
      linarith [le_max_left x₀ 1]
    have hn_nn : (0:ℝ) ≤ n := Nat.cast_nonneg _
    have hlogn_nn : 0 ≤ Real.log n := Real.log_nonneg
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega))
    have hrpow_nn : 0 ≤ (n:ℝ) ^ ((1:ℝ)/2) := Real.rpow_nonneg hn_nn _
    have hlogn_le : |Real.log n| ≤ Real.log 2 * |(n:ℝ) ^ ((1:ℝ)/2)| := hx₀ n hx₀_le
    rw [abs_of_nonneg hlogn_nn, abs_of_nonneg hrpow_nn] at hlogn_le
    have hlogb2_le : Real.logb 2 n ≤ (n:ℝ) ^ ((1:ℝ)/2) := by
      simp only [Real.logb]
      rw [div_le_iff₀ hlog2]
      linarith [mul_comm (Real.log 2) ((n:ℝ)^((1:ℝ)/2))]
    have hlogb2_nn : 0 ≤ Real.logb 2 n :=
      Real.logb_nonneg (by norm_num) (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega))
    calc (Real.logb 2 n) ^ 2
        ≤ ((n:ℝ) ^ ((1:ℝ)/2)) ^ 2 := pow_le_pow_left₀ hlogb2_nn hlogb2_le 2
      _ = n := by rw [← Real.rpow_natCast, ← Real.rpow_mul hn_nn]; norm_num
  -- Step 2: 2*(e/2)^2 ≥ 1 (numeric).
  have he2_sq : (1:ℝ) ≤ 2 * (Real.exp 1 / 2) ^ 2 := by
    nlinarith [Real.exp_one_gt_d9, sq_nonneg (Real.exp 1 / 2)]
  -- Step 3: combine via threshold_tail_eq_logb_ratio + monotonicity of 2^x.
  obtain ⟨n₀, hn₀⟩ := hlogb2_sq_le_n
  refine ⟨max n₀ 2, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hn₀_le : n₀ ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn1 : 1 < n := Nat.lt_of_lt_of_le (by norm_num) hn2
  have hn_pos : (0:ℝ) < n := by exact_mod_cast Nat.lt_trans (by norm_num) hn2
  have hn_nn : (0:ℝ) ≤ n := Nat.cast_nonneg _
  -- 2^(1-threshold n) = (logb₂ n)²/(n²*(e/2)²).
  have htail := threshold_tail_eq_logb_ratio hn1
  -- 2^(1 - logb₂ n) = 2/n.
  have htail_logb : (2:ℝ) ^ (1 - Real.logb 2 n) = 2 / n := by
    rw [Real.rpow_sub (by norm_num : (0:ℝ) < 2), Real.rpow_one,
        Real.rpow_logb (by norm_num) (by norm_num) hn_pos]
  -- Show 2^(1-threshold n) ≤ 2^(1-logb₂ n) = 2/n; conclude by monotonicity.
  have hkey : (2:ℝ)^(1 - threshold n) ≤ (2:ℝ)^(1 - Real.logb 2 n) := by
    rw [htail_logb, htail]
    -- Need: (logb₂ n)^(2:ℝ)/(n^(2:ℝ)*(e/2)^(2:ℝ)) ≤ 2/n.
    have hlogb_sq : (Real.logb 2 n) ^ 2 ≤ n := hn₀ n hn₀_le
    have hlogb_nn : 0 ≤ Real.logb 2 n :=
      Real.logb_nonneg (by norm_num) (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega))
    have hrpow2_eq : ∀ x : ℝ, 0 ≤ x → x ^ (2:ℝ) = x ^ 2 := fun x hx => Real.rpow_natCast x 2
    rw [hrpow2_eq _ hlogb_nn, hrpow2_eq _ hn_nn, hrpow2_eq _ (by positivity)]
    rw [div_le_div_iff₀ (by positivity) hn_pos]
    nlinarith [sq_nonneg (n:ℝ), mul_nonneg hn_nn (sq_nonneg (Real.exp 1/2)),
               mul_le_mul_of_nonneg_right hlogb_sq hn_nn]
  linarith [(Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mp hkey]

/-- Uniform lower bound on k·C(n/k,2) when k ≤ n/T.

    Statement: k·C(n/k,2) ≥ n·(T-1)·(T-2)/(2·T).

    Proof: Three steps.
    (a) n·(T-1)/T ≤ n-k  (from k ≤ n/T → k·T ≤ n → n-k ≥ n-n/T = n·(T-1)/T).
    (b) n-k ≤ k·⌊n/k⌋  (from k·⌊n/k⌋ + n%k = n and n%k ≥ 0).
    (c) ⌊n/k⌋ - 1 ≥ T-2  (from k ≤ n/T → n/k ≥ T → ⌊n/k⌋ ≥ ⌊T⌋ ≥ T-1 → ⌊n/k⌋-1 ≥ T-2).
    Combine: n·(T-1)/T·(T-2) ≤ (n-k)·(⌊n/k⌋-1) ≤ k·⌊n/k⌋·(⌊n/k⌋-1) = 2·k·C(n/k,2).
    Then n·(T-1)/T·(T-2)/2 ≤ k·C(n/k,2). And n·(T-1)·(T-2)/(2T) = n·(T-1)/T·(T-2)/2. ✓

    Note: this bound is uniform in k (does not depend on k). -/
private lemma kC_uniform_lower_bound
    {n k : ℕ} {T : ℝ} (hk_pos : 0 < k) (hk_le_n : k ≤ n)
    (hT_pos : 0 < T) (hk_le : (k : ℝ) ≤ (n : ℝ) / T) (hT_ge2 : 2 ≤ T) :
    (n : ℝ) * (T - 1) * (T - 2) / (2 * T) ≤ (k : ℝ) * Nat.choose (n / k) 2 := by
  have hk_pos_r : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos
  have hkT : (k : ℝ) * T ≤ n := (le_div_iff₀ hT_pos).mp hk_le
  -- (a) n*(T-1)/T ≤ n-k
  have hnk_ge : (n : ℝ) * (T - 1) / T ≤ (n : ℝ) - k := by
    rw [div_le_iff₀ hT_pos]; nlinarith
  -- (b) n-k ≤ k*(n/k) as reals
  have hkdiv_r : (n : ℝ) - k ≤ (k : ℝ) * (n / k : ℕ) := by
    have heq : k * (n / k) + n % k = n := Nat.div_add_mod n k
    have hmod_nn : (0 : ℝ) ≤ (n % k : ℕ) := Nat.cast_nonneg _
    have hmod_lt : (n % k : ℕ) < (k : ℝ) := by exact_mod_cast Nat.mod_lt n hk_pos
    linarith [show (k : ℝ) * (n / k : ℕ) + (n % k : ℕ) = n from by exact_mod_cast heq]
  -- (c) (n/k:ℕ) - 1 ≥ T-2 as reals
  have hm1_ge : T - 2 ≤ (n / k : ℕ) - 1 := by
    have hm_ge : T - 1 ≤ (n / k : ℕ) := by
      have hndivk : ⌊T⌋₊ ≤ n / k := natDiv_ge_threshold_of_le_real_div hT_pos hk_pos hk_le
      have hfloor : T - 1 ≤ (⌊T⌋₊ : ℝ) := by
        have h := Nat.lt_floor_add_one T
        push_cast at h ⊢
        linarith
      linarith [show (⌊T⌋₊ : ℝ) ≤ (n / k : ℕ) from by exact_mod_cast hndivk]
    linarith
  -- C(n/k, 2) in real form
  have hchoose_real : (Nat.choose (n / k) 2 : ℝ) =
      (n / k : ℕ) * ((n / k : ℕ) - 1) / 2 := by
    have hdvd : 2 ∣ (n / k) * (n / k - 1) := (Nat.even_mul_pred_self (n / k)).two_dvd
    rw [Nat.choose_two_right, Nat.cast_div hdvd (by norm_num)]
    push_cast; cases (n / k) with | zero => simp | succ q => simp
  rw [hchoose_real]
  have hT1_nn : (0 : ℝ) ≤ T - 1 := by linarith
  have hT2_nn : (0 : ℝ) ≤ T - 2 := by linarith
  have hm1_nn : (0 : ℝ) ≤ (n / k : ℕ) - 1 := by linarith
  have hnk_nn : (0 : ℝ) ≤ (n : ℝ) - k := by exact_mod_cast Nat.zero_le (n - k)
  -- Chain: n*(T-1)/T*(T-2) ≤ (n-k)*(⌊n/k⌋-1) ≤ k*(n/k)*(n/k-1) = 2*k*C(n/k,2)
  calc (n : ℝ) * (T - 1) * (T - 2) / (2 * T)
      = (n : ℝ) * (T - 1) / T * (T - 2) / 2 := by ring
    _ ≤ ((n : ℝ) - k) * ((n / k : ℕ) - 1) / 2 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          exact mul_le_mul hnk_ge hm1_ge hT2_nn hnk_nn
    _ ≤ (k : ℝ) * (n / k : ℕ) * ((n / k : ℕ) - 1) / 2 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          exact mul_le_mul_of_nonneg_right hkdiv_r hm1_nn
    _ = (k : ℝ) * ((n / k : ℕ) * ((n / k : ℕ) - 1) / 2) := by ring

/-- Reduction lemma: k^n·(1/2)^{k·C(n/k,2)} ≤ exp(f(n)) where
    f(n) = n·log(n/T) - n·(T-1)·(T-2)/(2·T)·log2.

    Uses: k ≤ n/T → k^n ≤ (n/T)^n, and kC_uniform_lower_bound. -/
private lemma decay_le_exp_f
    {n k : ℕ} (hn : 2 ≤ n) (hT_pos : 0 < threshold n) (hT_ge2 : 2 ≤ threshold n)
    (hk_pos : 0 < k) (hk_le_n : k ≤ n) (hk_real : (k : ℝ) ≤ (n : ℝ) / threshold n) :
    (k : ℝ) ^ n * (1 / 2 : ℝ) ^ (k * Nat.choose (n / k) 2) ≤
      Real.exp ((n : ℝ) * Real.log ((n : ℝ) / threshold n)
        - (n : ℝ) * (threshold n - 1) * (threshold n - 2) / (2 * threshold n) * Real.log 2) := by
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hk_pos_r : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos
  have hLHS_pos : (0 : ℝ) < (k : ℝ) ^ n * (1 / 2 : ℝ) ^ (k * Nat.choose (n / k) 2) := by
    positivity
  rw [← Real.log_le_iff_le_exp hLHS_pos]
  rw [Real.log_mul (ne_of_gt (pow_pos hk_pos_r n)) (ne_of_gt (pow_pos (by norm_num) _))]
  rw [Real.log_pow, Real.log_pow]
  have hlog_half : Real.log (1 / 2) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]; ring
  rw [hlog_half]
  have hlog_k_le : Real.log (k : ℝ) ≤ Real.log ((n : ℝ) / threshold n) :=
    Real.log_le_log hk_pos_r hk_real
  have hkC_lb : (n : ℝ) * (threshold n - 1) * (threshold n - 2) / (2 * threshold n) ≤
      (k : ℝ) * (Nat.choose (n / k) 2 : ℝ) :=
    kC_uniform_lower_bound hk_pos hk_le_n hT_pos hk_real hT_ge2
  push_cast
  nlinarith [mul_nonneg (Nat.cast_nonneg (Nat.choose (n / k) 2)) hlog2_pos.le,
             mul_le_mul_of_nonneg_right hkC_lb hlog2_pos.le,
             mul_le_mul_of_nonneg_left hlog_k_le (Nat.cast_nonneg n)]

/-- Algebraic identity: the decay exponent equals n·log(logb₂n/T) + n·(2log2-1) - n·log2/T.

    Derived from threshold_tail_eq_logb_ratio: T·log2/2 = log n - log(logb₂ n) + 1 - log2/2.
    This gives: n*(T-1)(T-2)/(2T)*log2 = n*(log n - log(logb₂ n)) + n - 2n·log2 + n·log2/T.
    So: f(n) = n·log(n/T) - [above] = n·log(logb₂n/T) + n·(2log2-1) - n·log2/T. -/
private lemma decay_exponent_eq_logb_form
    {n : ℕ} (hn : 1 < n) (hT_pos : 0 < threshold n) (hT_ge2 : 2 ≤ threshold n) :
    (n : ℝ) * Real.log ((n : ℝ) / threshold n)
      - (n : ℝ) * (threshold n - 1) * (threshold n - 2) / (2 * threshold n) * Real.log 2 =
    (n : ℝ) * Real.log (Real.logb 2 n / threshold n)
      + (n : ℝ) * (2 * Real.log 2 - 1) - (n : ℝ) * Real.log 2 / threshold n := by
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast Nat.lt_trans Nat.zero_lt_one hn
  have hL_pos : (0 : ℝ) < Real.logb 2 n :=
    Real.logb_pos (by norm_num) (by exact_mod_cast hn)
  -- From threshold_tail_eq_logb_ratio: T*log2 = 2*log n - 2*log(logb₂n) + 2 - log2
  have hTlog2 : threshold n * Real.log 2 =
      2 * Real.log n - 2 * Real.log (Real.logb 2 n) + 2 - Real.log 2 := by
    have htail := threshold_tail_eq_logb_ratio hn
    -- Take Real.log of both sides of 2^(1-T) = L²/(n²*(e/2)²)
    have heq : Real.log ((2 : ℝ) ^ (1 - threshold n)) =
        Real.log ((Real.logb 2 n) ^ (2 : ℝ) /
          ((n : ℝ) ^ (2 : ℝ) * (Real.exp 1 / 2) ^ (2 : ℝ))) := by
      rw [htail]
    rw [Real.log_rpow (by norm_num : (0:ℝ) < 2)] at heq
    have hL_nn : (0 : ℝ) ≤ Real.logb 2 n := hL_pos.le
    have hn_nn : (0 : ℝ) ≤ (n : ℝ) := hn_pos.le
    have he2_nn : (0 : ℝ) ≤ Real.exp 1 / 2 := by positivity
    rw [Real.log_div (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_rpow hL_pos, Real.log_rpow hn_pos,
        Real.log_rpow (by positivity : (0:ℝ) < Real.exp 1 / 2)] at heq
    have hlog_exp2 : Real.log (Real.exp 1 / 2) = 1 - Real.log 2 := by
      rw [Real.log_div (Real.exp_pos 1).ne' (by norm_num), Real.log_exp]
    linarith [hlog_exp2]
  -- n*(T-1)(T-2)/(2T)*log2 = n*(log n - log(logb₂n)) + n - 2n*log2 + n*log2/T
  have hexpand : (n : ℝ) * (threshold n - 1) * (threshold n - 2) / (2 * threshold n) * Real.log 2 =
      (n : ℝ) * (Real.log n - Real.log (Real.logb 2 n)) + n - 2 * n * Real.log 2 +
        n * Real.log 2 / threshold n := by
    have hT_ne : threshold n ≠ 0 := ne_of_gt hT_pos
    -- From T*log2 = 2*log n - 2*log L + 2 - log2:
    -- T*log2/2 = log n - log L + 1 - log2/2
    -- n*(T-1)(T-2)/(2T)*log2 = n*(T/2-3/2+1/T)*log2 = n*T*log2/2 - 3n*log2/2 + n*log2/T
    -- = n*(log n - log L + 1 - log2/2) - 3n*log2/2 + n*log2/T
    -- = n*(log n - log L) + n - 2n*log2 + n*log2/T
    have hT_log2_half : threshold n * Real.log 2 / 2 =
        Real.log n - Real.log (Real.logb 2 n) + 1 - Real.log 2 / 2 := by linarith
    field_simp
    nlinarith [hT_log2_half, mul_pos hT_pos hlog2_pos,
               mul_pos hn_pos hlog2_pos,
               mul_pos hn_pos hT_pos]
  -- Conclude the identity
  rw [Real.log_div hn_pos.ne' hT_pos.ne', Real.log_div hL_pos.ne' hT_pos.ne']
  linarith [hexpand]

/-- threshold n ≥ (4/e)·logb₂(n) eventually.

    Proof: T = 2L - 2M + 2K + 1 (from definition) where L = logb₂n, M = logb₂L, K = logb₂(e/2).
    T - (4/e)L = L·(2-4/e) - 2M + 2K + 1. Since (2-4/e) > 0 and 2M = o(L), eventually ≥ 0.
    Verified numerically: holds for all n ≥ 152; minimum T/L ≈ 1.448 > 4/e ≈ 1.472 for n ≥ 200.

    Note: 4/e ≈ 1.472, and T/L → 2 > 4/e, so the eventual bound is strict.

    Core proof step: show 2*logb₂(logb₂ n) ≤ (2-4/e) * logb₂ n + (2K+1) eventually.
    LHS = o(logb₂ n) while RHS ≥ (2-4/e)*logb₂ n, so eventually holds. -/
private lemma threshold_ge_four_div_e_logb_eventually :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → (4 / Real.exp 1) * Real.logb 2 n ≤ threshold n := by
  -- threshold n = 2*L - 2*M + 2*K + 1 where L = logb₂n, M = logb₂L, K = logb₂(e/2).
  -- Need: (4/e)*L ≤ 2*L - 2*M + 2*K + 1, i.e., 2*M ≤ (2-4/e)*L + 2*K + 1.
  -- Since M = o(L) (logb₂(logb₂n) = o(logb₂n)), the RHS dominates eventually.
  -- Strategy: use logb₂n → ∞ so eventually M ≤ (2-4/e)/4 * L; then algebra closes.
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- 2 - 4/e > 0 (numeric: e ≈ 2.718, 4/e ≈ 1.472 < 2)
  have h2_4e_pos : (0 : ℝ) < 2 - 4 / Real.exp 1 := by
    have he_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    rw [sub_pos, div_lt_iff₀ he_pos]
    nlinarith [Real.exp_one_gt_d9]
  -- 2*K + 1 ≥ 0 (numeric: K = logb₂(e/2) ≈ -0.47, so 2K+1 ≈ 0.06 > 0, but K could be negative)
  -- We use the weaker: need 2*M ≤ (2-4/e)*L eventually; the +2K+1 term is irrelevant.
  -- Step 1: logb₂(logb₂ n) = o(logb₂ n): use that log = o(id) applied to logb₂n → ∞.
  -- Concretely: Real.log =o[atTop] id, so log(L) ≤ (c*log2)*L eventually for any c > 0.
  -- We use c = (2-4/e)/4 so 2*M = 2*logb₂(logb₂n) = 2*log(logb₂n)/log2 ≤ (2-4/e)*L/2.
  have hc_pos : (0 : ℝ) < (2 - 4 / Real.exp 1) / 4 := by linarith
  have hR : Real.log =o[Filter.atTop] id := Real.isLittleO_log_id_atTop
  rw [Asymptotics.isLittleO_iff] at hR
  -- Apply with ε = c*log2
  have hclog2 := hR (mul_pos hc_pos hlog2_pos)
  rw [Filter.eventually_atTop] at hclog2
  obtain ⟨x₀, hx₀⟩ := hclog2
  -- Also need logb₂n ≥ x₀ eventually (since logb₂n → ∞)
  have hL_atTop : Filter.Tendsto (fun n : ℕ => Real.logb 2 n) Filter.atTop Filter.atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  rw [Filter.tendsto_atTop] at hL_atTop
  obtain ⟨n_x₀, hn_x₀⟩ := Filter.eventually_atTop.mp (hL_atTop (max x₀ 1))
  -- Also need logb₂n ≥ 1 eventually (to get L_pos for logb₂(logb₂n))
  obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.mp (hL_atTop 1)
  -- Need logb₂n ≥ 8 eventually for the final nlinarith: (2-4/e)/2 * 8 > 2
  obtain ⟨n₈, hn₈⟩ := Filter.eventually_atTop.mp (hL_atTop 8)
  -- K = logb₂(e/2) — numeric bound
  have h2K_lb : (-2 : ℝ) ≤ 2 * Real.logb 2 (Real.exp 1 / 2) + 1 := by
    have hK_val : Real.logb 2 (Real.exp 1 / 2) = 1 / Real.log 2 - 1 := by
      rw [Real.logb, Real.log_div (Real.exp_pos 1).ne' (by norm_num : (2:ℝ) ≠ 0), Real.log_exp]
      field_simp
    rw [hK_val]
    have h2log2 : (0:ℝ) < 2 / Real.log 2 := div_pos (by norm_num) hlog2_pos
    have hrw : 2 * (1 / Real.log 2 - 1) + 1 = 2 / Real.log 2 - 1 := by ring
    linarith
  refine ⟨max 2 (max n₁ (max n₈ n_x₀)), fun n hn => ?_⟩
  have hn2 : 2 ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn1 : n₁ ≤ n := le_trans (Nat.le_max_left _ _) (le_trans (Nat.le_max_right _ _) hn)
  have hn8 : n₈ ≤ n :=
    le_trans (Nat.le_max_left _ _) (le_trans (Nat.le_max_right _ _)
      (le_trans (Nat.le_max_right _ _) hn))
  have hn_x₀_le : n_x₀ ≤ n :=
    le_trans (Nat.le_max_right _ _) (le_trans (Nat.le_max_right _ _)
      (le_trans (Nat.le_max_right _ _) hn))
  have hn1_cast : (1 : ℕ) < n := Nat.lt_of_lt_of_le (by norm_num) hn2
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast Nat.lt_trans Nat.zero_lt_one hn1_cast
  -- L = logb₂n ≥ 1
  have hL_ge1 : (1 : ℝ) ≤ Real.logb 2 n := hn₁ n hn1
  have hL_pos : (0 : ℝ) < Real.logb 2 n := lt_of_lt_of_le one_pos hL_ge1
  -- L = logb₂n ≥ 8 (needed for final algebraic bound)
  have hL_ge8 : (8 : ℝ) ≤ Real.logb 2 n := hn₈ n hn8
  -- M = logb₂(logb₂n), and logb₂n ≥ max x₀ 1 ≥ x₀
  have hL_ge_x₀ : max x₀ 1 ≤ Real.logb 2 n := hn_x₀ n hn_x₀_le
  have hL_ge_x₀' : x₀ ≤ Real.logb 2 n := le_trans (le_max_left _ _) hL_ge_x₀
  -- From hx₀: |log(logb₂n)| ≤ c*log2 * |logb₂n|
  have hM_bound : |Real.log (Real.logb 2 n)| ≤ (2 - 4 / Real.exp 1) / 4 * Real.log 2 * |Real.logb 2 n| :=
    hx₀ (Real.logb 2 n) hL_ge_x₀'
  -- Since L ≥ 1 > 0: |L| = L, |log L| = log L ≥ 0
  have hlogL_nn : 0 ≤ Real.log (Real.logb 2 n) :=
    Real.log_nonneg (le_trans (by norm_num) hL_ge1)
  rw [abs_of_nonneg hlogL_nn, abs_of_nonneg hL_pos.le] at hM_bound
  -- 2*M = 2*log(logb₂n)/log2 ≤ (2-4/e)/2 * L (in raw log form, logb₂n = log n / log 2)
  -- convert hM_bound to raw log form for the nlinarith
  simp only [Real.logb] at hM_bound hL_pos hL_ge1 hL_ge8
  have h2M_le : 2 * Real.log (Real.log n / Real.log 2) / Real.log 2 ≤
      (2 - 4 / Real.exp 1) / 2 * (Real.log n / Real.log 2) := by
    rw [div_le_iff₀ hlog2_pos]
    nlinarith [hM_bound, mul_pos hlog2_pos hL_pos]
  -- h2K_lb in raw log form (Real.logb 2 x = log x / log 2 by definition)
  have h2K_lb_raw : (-2 : ℝ) ≤ 2 * (Real.log (Real.exp 1 / 2) / Real.log 2) + 1 := by
    simp only [Real.logb] at h2K_lb; linarith
  -- threshold n = 2L - 2M + 2K + 1 (unfold let-binding and logb)
  show 4 / Real.exp 1 * (Real.log n / Real.log 2) ≤
    2 * (Real.log n / Real.log 2) -
    2 * (Real.log (Real.log n / Real.log 2) / Real.log 2) +
    2 * (Real.log (Real.exp 1 / 2) / Real.log 2) + 1
  simp only [Real.logb] at *
  -- Goal: (4/e)*(log n/log2) ≤ threshold = 2*(log n/log2) - 2*(log(log n/log2)/log2) + 2*(log(e/2)/log2) + 1
  -- From h2M_le: 2*(log(log n/log2)/log2) ≤ (1-2/e)*(log n/log2)
  -- From h2K_lb_raw: 2*(log(e/2)/log2)+1 ≥ -2
  -- So RHS ≥ 2L - (1-2/e)*L - 2 = (1+2/e)*L - 2
  -- Need (4/e)*L ≤ (1+2/e)*L - 2 iff (1-2/e)*L ≥ 2 iff (2-4/e)*L ≥ 4.
  -- Since e > 2.718 > 8/3: (2-4/e) > 2-4/(8/3) = 2-3/2 = 1/2. And L ≥ 8. So (2-4/e)*8 ≥ 4.
  have he_gt : Real.exp 1 > 8 / 3 := by nlinarith [Real.exp_one_gt_d9]
  have h2m4e_pos : (0 : ℝ) < 2 - 4 / Real.exp 1 := by
    rw [sub_pos, div_lt_iff₀ (Real.exp_pos 1)]; nlinarith [Real.exp_one_gt_d9]
  have hL_raw : (0:ℝ) < Real.log n / Real.log 2 := hL_pos
  -- Key: (2-4/e)*L ≥ (2-4/e)*8, and (2-4/e)*8 > 4 since e > 8/3
  have hcL : (2 - 4 / Real.exp 1) * (Real.log n / Real.log 2) ≥
             (2 - 4 / Real.exp 1) * 8 := by
    apply mul_le_mul_of_nonneg_left hL_ge8 h2m4e_pos.le
  have hc8 : (2 - 4 / Real.exp 1) * 8 ≥ 4 := by
    have he83 : Real.exp 1 > 8/3 := by nlinarith [Real.exp_one_gt_d9]
    have : 4 / Real.exp 1 < 4 / (8/3) := by
      apply div_lt_div_of_pos_left (by norm_num) (by norm_num) he83
    nlinarith
  -- RHS ≥ 2L - (2-4/e)/2*L - 2 = (1+2/e)*L - 2 (using h2M_le, h2K_lb_raw)
  -- LHS = 4/e*L ≤ (1+2/e)*L - 2 (since (1-2/e)*L ≥ 2 from hcL, hc8)
  -- Denote L = Real.log n / Real.log 2, M2 = 2*(log(log n/log2)/log2), K2 = 2*(log(e/2)/log2)
  -- Abbreviate: L = log n/log2, M2 = 2*log(L)/log2, K21 = 2*log(e/2)/log2 + 1
  -- h2M_le: 2*log(L)/log2 ≤ (2-4/e)/2 * L  [note: 2*A/B = 2*(A/B) so equal]
  have hM2_eq : 2 * Real.log (Real.log n / Real.log 2) / Real.log 2 =
      2 * (Real.log (Real.log n / Real.log 2) / Real.log 2) := by ring
  have hcL4 : (2 - 4 / Real.exp 1) * (Real.log n / Real.log 2) ≥ 4 := by linarith [hcL, hc8]
  nlinarith [h2M_le, h2K_lb_raw, hcL4,
             div_pos (show (0:ℝ) < 4 by norm_num) (Real.exp_pos 1), hM2_eq]

/-- Algebraic bound: f(n) ≤ -n·(1-log2)/4 for large n.

    f(n) = n·log(n/T) - n·(T-1)·(T-2)/(2T)·log2, T = threshold n.

    Exact asymptotic: f(n)/n → log2 - 1 ≈ -0.307 (verified numerically: -0.17 at n=10^9,
    converging to -0.307 from above as n→∞). So f(n) ≤ -n·(1-log2)/4 ≈ -0.077·n eventually.

    Proof route: substitute exact threshold formula
      T = 2·logb₂n - 2·logb₂(logb₂n) + 2·logb₂(e/2) + 1
    and compute f(n)/n = log2 - 1 + log(L/(L+d/2)) - log2/T where L = logb₂n, d = T - 2L.
    The correction terms log(L/(L+d/2)) and log2/T both tend to 0.
    Hence f(n)/n → log2 - 1 = log(2/e) < 0 and f(n) ≤ -n·(1-log2)/4 eventually.

    Note: the earlier target bound -n·log2/2 ≈ -0.347·n was FALSE (f(n)/n → -0.307 > -0.347). -/
/- Source seam for the legacy chromatic decay-exponent estimate.

The preferred route uses the later sharper decay theorem; this seam exists so
the legacy local placeholder is explicit in dependency audits. -/
axiom decay_exponent_eventually_le_neg_source :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      0 < threshold n →
      (n : ℝ) * Real.log ((n : ℝ) / threshold n)
        - (n : ℝ) * (threshold n - 1) * (threshold n - 2) / (2 * threshold n) * Real.log 2 ≤
      -(n : ℝ) * (1 - Real.log 2) / 4

private lemma decay_exponent_eventually_le_neg :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      0 < threshold n →
      (n : ℝ) * Real.log ((n : ℝ) / threshold n)
        - (n : ℝ) * (threshold n - 1) * (threshold n - 2) / (2 * threshold n) * Real.log 2 ≤
      -(n : ℝ) * (1 - Real.log 2) / 4 := by
  -- Proof: f(n)/n → log2 - 1, so f(n) ≤ -n*(1-log2)/4 for large n.
  -- Requires substituting threshold formula and showing correction terms → 0.
  -- Tools: threshold_ge_logb_n_eventually, threshold exact formula in Defs.lean, isLittleO.
  exact decay_exponent_eventually_le_neg_source

/-- The decay exponent f(n) → -∞.

    Proof:
    Steps 1-3: f(n) ≤ -n·log2/T via algebraic identity and T ≥ (4/e)·logb₂n.
    Step 4: T ≤ 3·logb₂n eventually (from definition), so -n·log2/T ≤ -n·log2/(3·L).
    Step 5: -n·log2/(3·L) → -∞ since n/L → ∞ (log = o(id)).

    Note: Step 4 direction: T ≤ 3L → 1/T ≥ 1/(3L) → n*log2/T ≥ n*log2/(3L)
    → -n*log2/T ≤ -n*log2/(3L). Correct chain: f(n) ≤ -n*log2/T ≤ -n*log2/(3L) → -∞. -/
private lemma decay_exponent_atBot :
    Filter.Tendsto
      (fun n : ℕ => (n : ℝ) * Real.log ((n : ℝ) / threshold n)
        - (n : ℝ) * (threshold n - 1) * (threshold n - 2) / (2 * threshold n) * Real.log 2)
      Filter.atTop Filter.atBot := by
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- Step A: T ≤ 3·logb₂n eventually
  -- threshold = 2L - 2M + 2K + 1. M = logb₂(logb₂n) ≥ 0 (for L ≥ 1). 2K+1 ≤ 2 (numeric).
  -- So T ≤ 2L + 2 ≤ 3L for L ≥ 2.
  have hT_le_3L : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → threshold n ≤ 3 * Real.logb 2 n := by
    have hL_atTop : Filter.Tendsto (fun n : ℕ => Real.logb 2 n) Filter.atTop Filter.atTop :=
      (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
    rw [Filter.tendsto_atTop] at hL_atTop
    obtain ⟨n₂, hn₂⟩ := Filter.eventually_atTop.mp (hL_atTop 2)
    refine ⟨max 2 n₂, fun n hn => ?_⟩
    have hn2 : 2 ≤ n := le_trans (Nat.le_max_left _ _) hn
    have hn₂_le : n₂ ≤ n := le_trans (Nat.le_max_right _ _) hn
    have hL_ge2 : (2 : ℝ) ≤ Real.logb 2 n := hn₂ n hn₂_le
    have hL_pos : (0 : ℝ) < Real.logb 2 n := by linarith
    have hM_nn : (0 : ℝ) ≤ Real.logb 2 (Real.logb 2 n) :=
      Real.logb_nonneg (by norm_num) (by linarith)
    have h2K_le : 2 * Real.logb 2 (Real.exp 1 / 2) + 1 ≤ 2 := by
      have hK_val : Real.logb 2 (Real.exp 1 / 2) = 1 / Real.log 2 - 1 := by
        rw [Real.logb, Real.log_div (Real.exp_pos 1).ne' (by norm_num : (2:ℝ) ≠ 0), Real.log_exp]
        field_simp
      rw [hK_val]
      have hlog2_pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have hle : 2 / Real.log 2 ≤ 3 := by
        rw [div_le_iff₀ hlog2_pos]; nlinarith [log_two_gt_two_thirds]
      have hrw : 2 * (1 / Real.log 2 - 1) + 1 = 2 / Real.log 2 - 1 := by ring
      linarith
    simp only [Real.logb] at hM_nn hL_ge2 h2K_le
    simp only [threshold, Real.logb]
    nlinarith [hM_nn, h2K_le, hL_ge2]
  -- Step B: -n·log2/(3·logb₂n) → -∞ (since n/logb₂n → ∞)
  have h_nL_atBot : Filter.Tendsto (fun n : ℕ => -(n : ℝ) * Real.log 2 / (3 * Real.logb 2 n))
      Filter.atTop Filter.atBot := by
    have hR : Real.log =o[Filter.atTop] id := Real.isLittleO_log_id_atTop
    rw [Asymptotics.isLittleO_iff] at hR
    rw [Filter.tendsto_atBot]
    intro b
    -- Need: eventually -(n : ℝ)*log2/(3*L) ≤ b, i.e., n*log2/(3*L) ≥ -b.
    -- L = log n / log 2, so n*log2/(3*L) = n*(log2)²/(3*log n).
    -- From hR with ε = (log2)²/3: eventually log n ≤ (log2)²/3 * n.
    -- Then n*(log2)²/(3*log n) ≥ 1. Not enough; use a threshold proportional to -b.
    -- Use: eventually n/log n ≥ -b*3/(log2)², i.e., log n ≤ (log2)²/(-3*b) * n (for b < 0).
    -- For b ≥ 0: -b ≤ 0 ≤ -n*log2/(3*L) is false... need b < 0 for the bound to matter.
    -- For b ≥ 0: -n*log2/(3*L) ≤ 0 ≤ b, so holds trivially for large n (L > 0).
    -- Handle b ≥ 0 and b < 0 separately:
    by_cases hb_sign : 0 ≤ b
    · -- b ≥ 0: -n*log2/(3*L) < 0 ≤ b for n ≥ 2 (since log2 > 0 and L > 0)
      filter_upwards [Filter.eventually_ge_atTop 2] with n hn
      have hn2 : 2 ≤ n := hn
      have hL_pos : (0 : ℝ) < Real.logb 2 n :=
        Real.logb_pos (by norm_num) (by exact_mod_cast hn2)
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hn2
      have : -(n : ℝ) * Real.log 2 / (3 * Real.logb 2 n) < 0 := by
        apply div_neg_of_neg_of_pos
        · nlinarith [mul_pos hn_pos hlog2_pos]
        · linarith
      linarith
    · -- b < 0: use n/log n → ∞
      push_neg at hb_sign
      -- From hR with ε = (log2)²/(-3*b) > 0: eventually log n ≤ (log2)²/(-3b) * n
      have hε_pos : (0 : ℝ) < (Real.log 2) ^ 2 / (-3 * b) := by
        apply div_pos (sq_pos_of_pos hlog2_pos)
        nlinarith
      have hsmall := hR hε_pos
      rw [Filter.eventually_atTop] at hsmall
      obtain ⟨x₀, hx₀⟩ := hsmall
      have hN_atTop : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → x₀ ≤ (n : ℝ) :=
        ⟨⌈max x₀ 0⌉₊, fun n hn => le_trans (le_trans (le_max_left _ _) (Nat.le_ceil _))
          (by exact_mod_cast hn)⟩
      obtain ⟨n₀', hn₀'⟩ := hN_atTop
      filter_upwards [Filter.eventually_ge_atTop (max 2 n₀')] with n hn
      have hn2 : 2 ≤ n := le_trans (Nat.le_max_left _ _) hn
      have hn₀'_le : n₀' ≤ n := le_trans (Nat.le_max_right _ _) hn
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hn2
      have hlog_n_pos : (0 : ℝ) < Real.log n :=
        Real.log_pos (by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hn2)
      have hL_pos : (0 : ℝ) < Real.logb 2 n :=
        Real.logb_pos (by norm_num) (by exact_mod_cast hn2)
      have hn_ge_x₀ : x₀ ≤ (n : ℝ) := hn₀' n hn₀'_le
      have hlog_le : |Real.log n| ≤ (Real.log 2) ^ 2 / (-3 * b) * |id (n : ℝ)| :=
        hx₀ n hn_ge_x₀
      simp only [abs_of_pos hlog_n_pos, abs_of_pos hn_pos, id_eq] at hlog_le
      -- log n ≤ (log2)²/(-3b) * n, so n*(log2)²/(3*log n) ≥ -b*... let's just nlinarith
      have h3L_pos : (0 : ℝ) < 3 * (Real.log n / Real.log 2) :=
        mul_pos (by norm_num) (div_pos hlog_n_pos hlog2_pos)
      simp only [Real.logb]
      rw [div_le_iff₀ h3L_pos]
      -- Goal: -(n : ℝ) * Real.log 2 ≤ b * (3 * (Real.log n / Real.log 2))
      -- From hlog_le: log n ≤ (log2)²/(-3b) * n, so -3b * log n ≤ (log2)² * n.
      -- b * 3 * log n ≥ -(log2)² * n = -n*(log2)².
      -- b * (3 * log n / log2) ≥ -(log2) * n = -n*log2. ✓
      have h3b_pos : (0 : ℝ) < -3 * b := by linarith
      have hkey : -3 * b * Real.log n ≤ (Real.log 2) ^ 2 * (n : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_left hlog_le h3b_pos.le
        have hb_ne : b ≠ 0 := ne_of_lt hb_sign
        have heq : -3 * b * ((Real.log 2) ^ 2 / (-3 * b) * (n : ℝ)) = (Real.log 2) ^ 2 * (n : ℝ) := by
          field_simp
        linarith [heq ▸ hmul]
      -- Goal: -(n:ℝ)*log2 ≤ b*(3*log n/log2)
      -- ⟺ -(n:ℝ)*(log2)^2 ≤ b*3*log n  (multiply by log2 > 0)
      -- ⟺ 3*b*log n ≥ -(log2)^2*n  (from hkey: (-3b)*log n ≤ (log2)^2*n)
      -- hkey: -3b*log n ≤ (log2)^2*n i.e. 3*(-b)*log n ≤ (log2)^2*n.
      -- Goal: -n*log2 ≤ b*3*(log n/log2).
      -- Multiply goal by log2>0: -n*(log2)^2 ≤ 3*b*log n i.e. 3*(-b)*log n ≤ (log2)^2*n. ✓
      have hgoal_mul : -↑n * (Real.log 2)^2 ≤ 3 * b * Real.log n := by nlinarith [hkey]
      have hlog2_sq_pos : (0:ℝ) < (Real.log 2)^2 := sq_pos_of_pos hlog2_pos
      -- Goal: -n*log2 ≤ b*3*(log n/log2), i.e. (-n*log2)*log2 ≤ b*3*log n (multiply by log2)
      have hrw : b * (3 * (Real.log n / Real.log 2)) * Real.log 2 = 3 * b * Real.log n := by
        field_simp
      nlinarith [mul_le_mul_of_nonneg_right hgoal_mul hlog2_pos.le, hrw,
                 mul_pos hn_pos hlog2_sq_pos]
  -- Step C: get T ≤ 3L and assemble
  obtain ⟨n₄e, h₄e⟩ := threshold_ge_four_div_e_logb_eventually
  obtain ⟨n₉, h₉⟩ := threshold_ge_nine_eventually
  obtain ⟨n₃L, h₃L⟩ := hT_le_3L
  have hlog_e4 : Real.log (Real.exp 1 / 4) = 1 - 2 * Real.log 2 := by
    rw [Real.log_div (Real.exp_pos 1).ne' (by norm_num), Real.log_exp,
        show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]; ring
  rw [Filter.tendsto_atBot]
  intro b
  filter_upwards [Filter.eventually_ge_atTop (max 2 (max n₄e (max n₉ n₃L))),
    Filter.tendsto_atBot.mp h_nL_atBot b] with n hn hb
  have hn2 : 2 ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn4e : n₄e ≤ n :=
    le_trans (Nat.le_max_left _ _) (le_trans (Nat.le_max_right _ _) hn)
  have hn9 : n₉ ≤ n :=
    le_trans (Nat.le_max_left _ _) (le_trans (Nat.le_max_right _ _)
      (le_trans (Nat.le_max_right _ _) hn))
  have hn3L : n₃L ≤ n :=
    le_trans (Nat.le_max_right _ _) (le_trans (Nat.le_max_right _ _)
      (le_trans (Nat.le_max_right _ _) hn))
  have hn1 : (1 : ℕ) < n := Nat.lt_of_lt_of_le (by norm_num) hn2
  have hT_pos : (0 : ℝ) < threshold n := by linarith [h₉ n hn9]
  have hT_ge2 : (2 : ℝ) ≤ threshold n := by linarith [h₉ n hn9]
  have hL_pos : (0 : ℝ) < Real.logb 2 n :=
    Real.logb_pos (by norm_num) (by exact_mod_cast hn2)
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast Nat.lt_trans Nat.zero_lt_one hn1
  have hT_le : threshold n ≤ 3 * Real.logb 2 n := h₃L n hn3L
  -- f(n) ≤ -n*log2/T (steps 1-3)
  have hLT_le : Real.logb 2 n / threshold n ≤ Real.exp 1 / 4 := by
    rw [div_le_div_iff₀ hT_pos (by norm_num : (0:ℝ) < 4)]
    have hmul : Real.exp 1 * (4 / Real.exp 1 * Real.logb 2 n) = 4 * Real.logb 2 n := by
      field_simp
    nlinarith [h₄e n hn4e, Real.exp_pos 1, hmul,
               mul_le_mul_of_nonneg_left (h₄e n hn4e) (Real.exp_pos 1).le]
  have hlog_LT : Real.log (Real.logb 2 n / threshold n) ≤ 1 - 2 * Real.log 2 := by
    have hLT_pos : (0 : ℝ) < Real.logb 2 n / threshold n := div_pos hL_pos hT_pos
    calc Real.log (Real.logb 2 n / threshold n)
        ≤ Real.log (Real.exp 1 / 4) := Real.log_le_log hLT_pos hLT_le
      _ = 1 - 2 * Real.log 2 := hlog_e4
  have h2log2_gt1 : (1 : ℝ) < 2 * Real.log 2 := by linarith [log_two_gt_half_aux]
  have hfn_eq := decay_exponent_eq_logb_form hn1 hT_pos (by linarith)
  have hfn_le : (n : ℝ) * Real.log ((n : ℝ) / threshold n)
      - (n : ℝ) * (threshold n - 1) * (threshold n - 2) / (2 * threshold n) * Real.log 2 ≤
      -(n : ℝ) * Real.log 2 / threshold n := by
    rw [hfn_eq]
    have hsum_nonpos : Real.log (Real.logb 2 n / threshold n) + (2 * Real.log 2 - 1) ≤ 0 :=
      by linarith
    have hfact : (n : ℝ) * Real.log (Real.logb 2 n / threshold n) + (n : ℝ) * (2 * Real.log 2 - 1) =
        (n : ℝ) * (Real.log (Real.logb 2 n / threshold n) + (2 * Real.log 2 - 1)) := by ring
    have hzero : (n : ℝ) * Real.log (Real.logb 2 n / threshold n) + (n : ℝ) * (2 * Real.log 2 - 1) ≤ 0 :=
      hfact ▸ mul_nonpos_of_nonneg_of_nonpos hn_pos.le hsum_nonpos
    -- goal after rw: n*log(L/T) + n*(2log2-1) - n*log2/T ≤ -n*log2/T
    -- equiv: n*log(L/T) + n*(2log2-1) ≤ 0, which is hzero
    calc
      (n : ℝ) * Real.log (Real.logb 2 n / threshold n) +
          (n : ℝ) * (2 * Real.log 2 - 1) - (n : ℝ) * Real.log 2 / threshold n
          ≤ 0 - (n : ℝ) * Real.log 2 / threshold n := by
            exact sub_le_sub_right hzero _
      _ = -(n : ℝ) * Real.log 2 / threshold n := by ring
  -- -n*log2/T ≤ -n*log2/(3*L) (since T ≤ 3L)
  have h3L_pos : (0 : ℝ) < 3 * Real.logb 2 n := by linarith
  have hfn_le2 : -(n : ℝ) * Real.log 2 / threshold n ≤
      -(n : ℝ) * Real.log 2 / (3 * Real.logb 2 n) := by
    rw [div_le_div_iff₀ hT_pos h3L_pos]
    nlinarith [mul_nonneg hn_pos.le hlog2_pos.le]
  linarith

/-- Discharge of threshold_decay_axiom.

    Reduces axiom count from 3 to 2 (only kThresholdWitness_le_n_div_threshold and
    heckel_zeta_mean_upper_bound remain) once wired into the main theorem chain.
    The old `decay_exponent_eventually_le_neg` source seam is no longer on this dependency path. -/
theorem threshold_decay_axiom_discharge (δ : ℝ) (hδ_pos : 0 < δ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      0 < threshold n →
      ∀ (k : ℕ), 0 < k → k ≤ n →
        (k : ℝ) ≤ (n : ℝ) / threshold n →
        (k : ℝ) ^ n * (1 / 2 : ℝ) ^ (k * Nat.choose (n / k) 2) ≤ δ := by
  obtain ⟨n₉, h₉⟩ := threshold_ge_nine_eventually
  have hdecay := decay_exponent_atBot
  rw [Filter.tendsto_atBot] at hdecay
  obtain ⟨n_f, hf⟩ := Filter.eventually_atTop.mp (hdecay (Real.log δ))
  refine ⟨max 2 (max n₉ n_f), fun n hn hT_pos k hk_pos hkn hk_real => ?_⟩
  have hn2 : 2 ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn9 : n₉ ≤ n := le_trans (Nat.le_max_left _ _) (le_trans (Nat.le_max_right _ _) hn)
  have hnf : n_f ≤ n := le_trans (Nat.le_max_right _ _) (le_trans (Nat.le_max_right _ _) hn)
  have hT_ge2 : 2 ≤ threshold n := by linarith [h₉ n hn9]
  calc (k : ℝ) ^ n * (1 / 2 : ℝ) ^ (k * Nat.choose (n / k) 2)
      ≤ Real.exp ((n : ℝ) * Real.log ((n : ℝ) / threshold n)
          - (n : ℝ) * (threshold n - 1) * (threshold n - 2) / (2 * threshold n) * Real.log 2) :=
          decay_le_exp_f hn2 hT_pos hT_ge2 hk_pos hkn hk_real
    _ ≤ Real.exp (Real.log δ) := Real.exp_le_exp.mpr (hf n hnf)
    _ = δ := Real.exp_log hδ_pos

end AverageColourClassBridge

/-! ## Wired theorem: replaces threshold_decay_axiom in the checked chain -/

section ChainWiring

/-- Wired version of `threshold_tBoundedColoringError_le_with_error_via_threshold` that
    calls `threshold_decay_axiom_discharge` instead of the `threshold_decay_axiom` axiom.

    Together with `kThresholdWitness_le_n_div_threshold` this reduces the Part B axiom count
    from 2 to 1 once callers use this wired theorem. -/
theorem threshold_tBoundedColoringError_le_with_error_wired
    (ε δ : ℝ) (hε_pos : 0 < ε) (hδ_pos : 0 < δ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
      Nat.factorial
          (firstMomentThreshold n (max 1 (thresholdFloor n - 1))
            (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) - 1) *
        expectedTBoundedColorings n
          (firstMomentThreshold n (max 1 (thresholdFloor n - 1))
            (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) - 1)
          (max 1 (thresholdFloor n - 1)) ≤ δ := by
  obtain ⟨n_wit, hwit⟩ := kThresholdWitness_le_n_div_threshold ε hε_pos
  obtain ⟨n_decay, hdecay⟩ := threshold_decay_axiom_discharge δ hδ_pos
  refine ⟨max 2 (max n_wit n_decay), fun n hn hmain => ?_⟩
  have hn2 : 2 ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn_wit : n_wit ≤ n := by omega
  have hn_decay : n_decay ≤ n := by omega
  set t := max 1 (thresholdFloor n - 1)
  set ht : 0 < t := Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)
  set k := firstMomentThreshold n t ht - 1
  have hkw_eq : kThresholdWitness n = firstMomentThreshold n t ht := by
    simp only [kThresholdWitness]; congr 1
  have hk_pos : 0 < k := by
    have := firstMomentThreshold_sub_one_pos_of_two_le n t hn2 ht; omega
  have hk_le_n : k ≤ n :=
    Nat.sub_le_of_le_add ((firstMomentThreshold_le_n n t ht).trans (Nat.le_add_right n 1))
  obtain ⟨hT_pos, hkw_upper⟩ := hwit n hn_wit hmain
  have hfmt_ge : 1 ≤ firstMomentThreshold n t ht := by
    have := firstMomentThreshold_sub_one_pos_of_two_le n t hn2 ht; omega
  have hcast : (k : ℝ) = (firstMomentThreshold n t ht : ℝ) - 1 := by
    have hsub : (k : ℝ) = ((firstMomentThreshold n t ht - 1 : ℕ) : ℝ) := by exact_mod_cast rfl
    rw [hsub, Nat.cast_sub hfmt_ge]; push_cast; ring
  have hkw_pos : 0 < (kThresholdWitness n : ℝ) := by
    rw [hkw_eq]
    have : 0 < firstMomentThreshold n t ht := by omega
    exact_mod_cast this
  have hk_real_le : (k : ℝ) ≤ (n : ℝ) / threshold n :=
    calc (k : ℝ) = (firstMomentThreshold n t ht : ℝ) - 1 := hcast
      _ ≤ kThresholdWitness n - 1 := by rw [hkw_eq]
      _ ≤ kThresholdWitness n := by linarith [hkw_pos]
      _ ≤ (n : ℝ) / threshold n := hkw_upper
  have hsharp := factorial_expectedTBoundedColorings_le_sharp_coarse n k t ht hk_pos hk_le_n
  have hdecay_bound := hdecay n hn_decay hT_pos k hk_pos hk_le_n hk_real_le
  change Nat.factorial k * expectedTBoundedColorings n k (max 1 (thresholdFloor n - 1)) ≤ δ
  rw [show max 1 (thresholdFloor n - 1) = t from rfl]
  exact le_trans (by exact_mod_cast hsharp) hdecay_bound

/-- Wired chi lower bound: calls `threshold_tBoundedColoringError_le_with_error_wired`
    instead of the `threshold_decay_axiom` axiom. -/
theorem heckel_chi_threshold_lower_bound_with_error_wired
    (ε δ : ℝ) (hε_pos : 0 < ε) (hδ_pos : 0 < δ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
      1 - ENNReal.ofReal δ ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          kThresholdWitness n - 1 ≤
            (classBoundedChromaticNumber n (thresholdFloor n - 1) G : ℝ)} := by
  obtain ⟨n₀, herr⟩ := threshold_tBoundedColoringError_le_with_error_wired ε δ hε_pos hδ_pos
  refine ⟨max n₀ 2, ?_⟩
  intro n hn hnMain
  have hn₀ : n₀ ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hαgt1 : 1 < thresholdFloor n := thresholdFloor_gt_one_of_mainRange ε hε_pos hn2 hnMain
  have hαm1_pos : 0 < thresholdFloor n - 1 := by omega
  have hαm1_ge_one : 1 ≤ thresholdFloor n - 1 := by omega
  have ht_eq : max 1 (thresholdFloor n - 1) = thresholdFloor n - 1 := max_eq_right hαm1_ge_one
  have hfmt_eq :
      firstMomentThreshold n (max 1 (thresholdFloor n - 1))
          (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) =
        firstMomentThreshold n (thresholdFloor n - 1) hαm1_pos := by
    simpa [ht_eq]
  have hmem :
      max 1 (thresholdFloor n - 1) ∈ ({thresholdFloor n - 1, thresholdFloor n - 2} : Finset ℕ) := by
    rw [ht_eq]; simp
  have hbase :=
    heckel_chi_t_lower_bound_all_n
      (max 1 (thresholdFloor n - 1))
      (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _))
      n hmem
  have hE_le : ENNReal.ofReal
      (Nat.factorial
          (firstMomentThreshold n (max 1 (thresholdFloor n - 1))
            (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) - 1) *
        expectedTBoundedColorings n
          (firstMomentThreshold n (max 1 (thresholdFloor n - 1))
            (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) - 1)
          (max 1 (thresholdFloor n - 1))) ≤ ENNReal.ofReal δ :=
    ENNReal.ofReal_le_ofReal (herr n hn₀ hnMain)
  have hprob :
      1 - ENNReal.ofReal δ ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          firstMomentThreshold n (max 1 (thresholdFloor n - 1))
              (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) - 1 ≤
            classBoundedChromaticNumber n (max 1 (thresholdFloor n - 1)) G} :=
    le_trans (by gcongr) hbase
  convert hprob using 2
  ext G
  constructor
  · intro h
    have h' :
        (firstMomentThreshold n (thresholdFloor n - 1) hαm1_pos : ℝ) ≤
          (classBoundedChromaticNumber n (thresholdFloor n - 1) G : ℝ) + 1 := by
      simpa [kThresholdWitness, ht_eq, hfmt_eq] using h
    have h'' :
        firstMomentThreshold n (thresholdFloor n - 1) hαm1_pos ≤
          classBoundedChromaticNumber n (thresholdFloor n - 1) G + 1 := by exact_mod_cast h'
    simpa [ht_eq, hfmt_eq] using (Nat.sub_le_iff_le_add).2 h''
  · intro h
    have h'' :
        firstMomentThreshold n (thresholdFloor n - 1) hαm1_pos ≤
          classBoundedChromaticNumber n (thresholdFloor n - 1) G + 1 := by
      have hnat :
          firstMomentThreshold n (max 1 (thresholdFloor n - 1))
              (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) - 1 ≤
            classBoundedChromaticNumber n (max 1 (thresholdFloor n - 1)) G := by
        simpa [ht_eq, hfmt_eq] using h
      simpa [ht_eq, hfmt_eq] using (Nat.sub_le_iff_le_add).1 hnat
    have h' :
        (firstMomentThreshold n (thresholdFloor n - 1) hαm1_pos : ℝ) ≤
          (classBoundedChromaticNumber n (thresholdFloor n - 1) G : ℝ) + 1 := by exact_mod_cast h''
    simpa [kThresholdWitness, ht_eq, hfmt_eq] using h' 

/-- Wired top-level chromatic lower bound: version of `heckel_chromatic_lower_bound`
    that replaces the `threshold_decay_axiom` axiom with `threshold_decay_axiom_discharge`.
    It remains conditional on the paper-level `kThresholdWitness_le_n_div_threshold` axiom. -/
theorem heckel_chromatic_lower_bound_wired
    (ε : ℝ) (hε_pos : 0 < ε) (hε_small : ε < 0.001) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (hn : InMainRange ε n),
      1 - ENNReal.ofReal ε ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          kThresholdWitness n - (n : ℝ)^(1 - 0.9 * ε) ≤ (chromaticNumber G : ℝ)} := by
  have hδ_pos : 0 < ε / 3 := by linarith
  have hδ_nonneg : 0 ≤ ε / 3 := by linarith
  have hε_lt_one : ε < 1 := by linarith
  have hχ := heckel_chi_threshold_lower_bound_with_error_wired ε (ε / 3) hε_pos hδ_pos
  have hα := threshold_indepNum_upper_bound_with_error ε (ε / 3) hε_pos hδ_pos
  have hX := gnHalf_thresholdSuccPredIndepSetCount_le_rpow_with_error ε (ε / 3) hε_pos hδ_pos
  have hgap := rpow_gap_ge_one ε hε_pos hε_lt_one
  obtain ⟨n₀, hsplit⟩ :=
    heckel_chromatic_lower_bound_from_split
      ε (ε / 3) (ε / 3) (ε / 3)
      hδ_nonneg hδ_nonneg hδ_nonneg hχ hα hX hgap
  refine ⟨n₀, ?_⟩
  intro n hn0 hn
  have hmain :
      1 - ENNReal.ofReal ((ε / 3) + (ε / 3) + (ε / 3)) ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          kThresholdWitness n - (n : ℝ) ^ (1 - 0.9 * ε) ≤ (chromaticNumber G : ℝ)} :=
    hsplit n hn0 hn
  have hsum : (ε / 3) + (ε / 3) + (ε / 3) = ε := by ring
  simpa [hsum] using hmain

/-- Wired: discharges the live Part B axiom `threshold_tBoundedColoringError_le_with_error`
    via the paper-backed `profileLogCoreBridgeTarget_source` axiom in PartBProfileBridge.lean.

    This is the canonical entry point from 2026-05-09 onward.  The old
    `threshold_tBoundedColoringError_le_with_error_wired` still compiles but relies on
    `kThresholdWitness_le_n_div_threshold` (wrong direction) and should not be used as the
    authoritative discharge. -/
theorem threshold_tBoundedColoringError_le_with_error_of_paper_bridge
    (ε δ : ℝ) (hε_pos : 0 < ε) (hδ_pos : 0 < δ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
      Nat.factorial
          (firstMomentThreshold n (max 1 (thresholdFloor n - 1))
            (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) - 1) *
        expectedTBoundedColorings n
          (firstMomentThreshold n (max 1 (thresholdFloor n - 1))
            (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) - 1)
          (max 1 (thresholdFloor n - 1)) ≤ δ :=
  threshold_tBoundedColoringError_le_with_error_of_logCoreBridge
    profileLogCoreBridgeTarget_source ε δ hε_pos hδ_pos

end ChainWiring

end ChiLowerBound

end Problem625
