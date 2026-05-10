import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Basic
import Erdos625.Defs

/-!
# Bounded Differences for the Cochromatic Number

This file proves that the cochromatic number has the **Lipschitz-1 property** under
single-vertex deletion: for any graph G on a finite type and any vertex v,

    cochromaticNumber (G.induce {v}ᶜ) ≤ cochromaticNumber G
                                        ≤ cochromaticNumber (G.induce {v}ᶜ) + 1

This is the key input to applying Azuma-Hoeffding concentration (via the vertex-exposure
martingale) to ζ(G(n,1/2)).
-/

namespace Problem625

open SimpleGraph

section BoundedDifferences

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (v : V)

set_option linter.unusedSectionVars false in
/-- The set of k with a cochromatic k-coloring is nonempty (identity coloring works). -/
theorem cochromaticColoringExists_card_self :
    {k : ℕ | CochromaticColoringExists G k}.Nonempty := by
  use Fintype.card V
  let e := Fintype.equivFin V
  exact ⟨e, fun i => by
    right; intro u hu w hw huw
    simp only [Set.mem_setOf_eq] at hu hw
    exact fun _ => huw (e.injective (hu ▸ hw.symm))⟩

set_option linter.unusedSectionVars false in
/-- The set of k with a cochromatic k-coloring of G.induce S is nonempty. -/
theorem cochromaticColoringExists_card_induce (S : Set V) [Fintype S] :
    {k : ℕ | CochromaticColoringExists (G.induce S) k}.Nonempty := by
  use Fintype.card S
  let e := Fintype.equivFin S
  exact ⟨e, fun i => by
    right; intro u hu w hw huw
    simp only [Set.mem_setOf_eq] at hu hw
    exact fun _ => huw (e.injective (hu ▸ hw.symm))⟩

/-! ### Part 1: Restriction — ζ(G.induce S) ≤ ζ(G) -/

set_option linter.unusedSectionVars false in
/-- A valid color class in G restricts to a valid color class in the induced subgraph. -/
theorem isValidColorClass_induce_of_isValidColorClass {S : Set V} {C : Set V}
    (hC : IsValidColorClass G C) :
    IsValidColorClass (G.induce S) (Subtype.val ⁻¹' C) := by
  rcases hC with hCliq | hIndep
  · left
    intro ⟨u, _⟩ hu ⟨w, _⟩ hw huw
    simp only [Set.mem_preimage] at hu hw
    exact hCliq u hu w hw (fun h => huw (Subtype.ext h))
  · right
    intro ⟨u, _⟩ hu ⟨w, _⟩ hw huw hadj
    simp only [Set.mem_preimage] at hu hw
    exact hIndep u hu w hw (fun h => huw (Subtype.ext h)) hadj

/-- Restricting a cochromatic k-coloring of G to S gives a cochromatic k-coloring
    of G.induce S. -/
theorem isCochromaticColoring_induce {S : Set V}
    (k : ℕ) (π : V → Fin k) (hπ : IsCochromaticColoring G k π) :
    IsCochromaticColoring (G.induce S) k (fun x : S => π x.val) := by
  intro i
  have h_eq : {w : S | π w.val = i} = Subtype.val ⁻¹' {w | π w = i} := by ext; simp
  rw [h_eq]
  exact isValidColorClass_induce_of_isValidColorClass G (hπ i)

/-- The cochromatic number of an induced subgraph is at most the cochromatic number of G. -/
theorem cochromaticNumber_induce_le (S : Set V) [Fintype S] :
    cochromaticNumber (G.induce S) ≤ cochromaticNumber G := by
  unfold cochromaticNumber
  apply Nat.sInf_le
  -- cochromaticNumber G is in the set for the induced subgraph
  have hmem := Nat.sInf_mem (cochromaticColoringExists_card_self G)
  obtain ⟨π, hπ⟩ := hmem
  exact ⟨fun x => π x.val, isCochromaticColoring_induce G _ π hπ⟩

/-! ### Part 2: Extension by singleton — ζ(G) ≤ ζ(G.induce {v}ᶜ) + 1 -/

set_option linter.unusedSectionVars false in
/-- Extending a cochromatic k-coloring of G.induce {v}ᶜ by assigning v a fresh color
    gives a cochromatic (k+1)-coloring of G. -/
theorem cochromaticColoringExists_extend_singleton
    (k : ℕ) (hk : CochromaticColoringExists (G.induce ({v}ᶜ : Set V)) k) :
    CochromaticColoringExists G (k + 1) := by
  obtain ⟨π, hπ⟩ := hk
  let fresh : Fin (k + 1) := ⟨k, lt_add_one k⟩
  let π' : V → Fin (k + 1) := fun w =>
    if h : w = v then fresh
    else Fin.castSucc (π ⟨w, by simp [Set.mem_compl_iff, h]⟩)
  refine ⟨π', fun i => ?_⟩
  by_cases hi : i = fresh
  · -- Color class = fresh: contains only v (since castSucc maps to values < k)
    subst hi
    left
    intro u hu w hw huw
    simp only [π', Set.mem_setOf_eq] at hu hw
    have u_eq_v : u = v := by
      by_contra h; simp [h] at hu
      exact absurd (Fin.ext_iff.mp hu) (by simp [Fin.val_castSucc, fresh]; omega)
    have w_eq_v : w = v := by
      by_contra h; simp [h] at hw
      exact absurd (Fin.ext_iff.mp hw) (by simp [Fin.val_castSucc, fresh]; omega)
    exact absurd (u_eq_v ▸ w_eq_v ▸ rfl) huw
  · -- Color class i ≠ fresh: only contains vertices ≠ v
    have hi_lt : i.val < k := by
      have := i.isLt; simp [fresh, Fin.ext_iff] at hi; omega
    let i' : Fin k := ⟨i.val, hi_lt⟩
    have key : ∀ w, w ∈ ({w | π' w = i} : Set V) → w ≠ v := by
      intro w hw heq
      simp only [π', Set.mem_setOf_eq, heq, dite_true] at hw
      exact hi hw.symm
    -- Transfer the validity from the induced coloring
    have castSucc_eq : ∀ w (h : w ≠ v),
        π' w = i → π ⟨w, by simp [Set.mem_compl_iff, h]⟩ = i' := by
      intro w h hw
      simp only [π', h, dite_false] at hw
      exact Fin.castSucc_injective _ (hw ▸ Fin.ext (by rfl))
    rcases hπ i' with hCliq | hIndep
    · left
      intro u hu w hw huw
      have hu_ne := key u hu
      have hw_ne := key w hw
      have hu' := castSucc_eq u hu_ne (by exact hu)
      have hw' := castSucc_eq w hw_ne (by exact hw)
      exact hCliq ⟨u, _⟩ (by simpa using hu') ⟨w, _⟩ (by simpa using hw')
        (fun h => huw (congr_arg Subtype.val h))
    · right
      intro u hu w hw huw hadj
      have hu_ne := key u hu
      have hw_ne := key w hw
      have hu' := castSucc_eq u hu_ne (by exact hu)
      have hw' := castSucc_eq w hw_ne (by exact hw)
      exact hIndep ⟨u, _⟩ (by simpa using hu') ⟨w, _⟩ (by simpa using hw')
        (fun h => huw (congr_arg Subtype.val h)) hadj

/-- **ζ(G) ≤ ζ(G.induce {v}ᶜ) + 1**: Deleting one vertex decreases ζ by at most 1. -/
theorem cochromaticNumber_le_induce_compl_singleton_add_one :
    cochromaticNumber G ≤ cochromaticNumber (G.induce ({v}ᶜ : Set V)) + 1 := by
  unfold cochromaticNumber at *
  apply Nat.sInf_le
  apply cochromaticColoringExists_extend_singleton G v
  exact Nat.sInf_mem (cochromaticColoringExists_card_induce G ({v}ᶜ : Set V))

/-! ### Part 3: Combined bounded-differences theorem -/

/-- **Bounded differences for cochromatic number**: Deleting one vertex changes ζ by at most 1.

    cochromaticNumber (G.induce {v}ᶜ) ≤ cochromaticNumber G
                                        ≤ cochromaticNumber (G.induce {v}ᶜ) + 1

    This is the Lipschitz-1 property needed for Azuma-Hoeffding concentration. -/
theorem cochromaticNumber_bounded_diff_singleton :
    cochromaticNumber (G.induce ({v}ᶜ : Set V)) ≤ cochromaticNumber G ∧
    cochromaticNumber G ≤ cochromaticNumber (G.induce ({v}ᶜ : Set V)) + 1 :=
  ⟨cochromaticNumber_induce_le G ({v}ᶜ),
   cochromaticNumber_le_induce_compl_singleton_add_one G v⟩

end BoundedDifferences

end Problem625
