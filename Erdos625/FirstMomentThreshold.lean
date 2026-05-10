import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.SimpleGraph
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.SetBernoulli
import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Erdos625.Defs
import Erdos625.ColoringBasic

/-!
# Problem 625 — First Moment Threshold k_t

Formalizes the *t-bounded first moment threshold* **k_t(n)** from
Heckel–Panagiotou (2023), arXiv:2306.07253, Definition (ktdef) and Lemma 8.1.

## Mathematical content

**Definition** (ktdef, [heckel2023colouring] §1.2):
```
  k_t(n) := min { k : E_{n,k,t} ≥ 1 }
```
where `E_{n,k,t}` is the expected number of unordered t-bounded k-colorings of G(n,1/2).

**Lemma 8.1** ([heckel2023colouring]):
By definition k_t, `E_{n, k_t − 1, t} < 1`. Hence by the first moment method:
```
  ℙ[χ_t(G(n,1/2)) < k_t − 1] ≤ E_{n, k_t − 1, t} < 1
```
so whp `χ_t(G(n,1/2)) ≥ k_t − 1`.

## What this file provides

- `expectedTBoundedColorings n k t` — tractable formula for E_{n,k,t}
- `fmtExists n t` — E_{n,n,t} ≥ 1 (existence witness for Nat.find)
- `firstMomentThreshold n t` — k_t(n) via Nat.find
- `firstMomentThreshold_ge_one` — E_{n, k_t, t} ≥ 1
- `below_threshold_lt_one` — E_{n, k_t − 1, t} < 1 (key step toward Lemma 8.1)

The final connection to gnHalf (step 5 of Lemma 8.1) remains an axiom
`heckel_chi_t_lower_bound` pending formalization of Azuma-Hoeffding for χ_t.
-/

namespace Problem625

open MeasureTheory ProbabilityTheory

/-! ## Expected number of t-bounded k-colorings (exact formula) -/

section ExpectedColorings

/-!
### Coloring profiles

A **k-coloring profile** (Heckel–Panagiotou 2023, §2) on n vertices with t-bound is a
function `f : ℕ → ℕ` where `f u` = number of color classes of size u, satisfying:
- `∑ u, u * f u = n`  (all vertices covered)
- `∑ u, f u = k`      (exactly k color classes)
- `f u = 0` for all `u > t` (t-bounded)

For the exact formula we work with finite supports: `f : Fin (t+1) → ℕ` where index `u`
represents class size `u` (index 0 is unused: size-0 classes don't contribute).
-/

/-- A t-bounded k-coloring profile on n vertices:
    vector (f_1, ..., f_t) where f_u = # classes of size u,
    summing sizes gives n, summing counts gives k. -/
def IsColoringProfile (n k t : ℕ) (f : Fin (t + 1) → ℕ) : Prop :=
  (∑ u : Fin (t + 1), u.val * f u = n) ∧ (∑ u : Fin (t + 1), f u = k)

/-- The multinomial coefficient P_k = n! / ∏_u (u!)^{f_u}:
    number of ordered vertex partitions with profile f.
    f : Fin (n+1) → ℕ gives # color classes of each size. -/
noncomputable def profileP (n : ℕ) (f : Fin (n + 1) → ℕ) : ℕ :=
  Nat.factorial n / ∏ u : Fin (n + 1), (Nat.factorial u.val) ^ f u

/-- The number of forbidden edges f_k = ∑_u C(u, 2) * f_u. -/
noncomputable def profileF (n : ℕ) (f : Fin (n + 1) → ℕ) : ℕ :=
  ∑ u : Fin (n + 1), Nat.choose u.val 2 * f u

/-- The symmetry factor ∏_u (f_u)! for unordered colorings. -/
noncomputable def profileSymm (n : ℕ) (f : Fin (n + 1) → ℕ) : ℕ :=
  ∏ u : Fin (n + 1), Nat.factorial (f u)

/-- The finite set of t-bounded k-coloring profiles on n vertices.
    A profile is a function (Fin (n+1) → Fin (n+1)) giving class counts f_u (# classes of size u),
    where f_u = 0 for u > t (the t-boundedness condition).
    We index by Fin (n+1) to include all possible class sizes 0..n.
    The bound Fin (n+1) for values is valid since f_u ≤ k ≤ n. -/
def coloringProfileFinset (n k t : ℕ) : Finset (Fin (n + 1) → Fin (n + 1)) :=
  Finset.univ.filter (fun f =>
    (∑ u : Fin (n + 1), u.val * (f u).val = n) ∧
    (∑ u : Fin (n + 1), (f u).val = k) ∧
    (∀ u : Fin (n + 1), t < u.val → (f u).val = 0))

/-- Total number of color classes encoded by a profile. -/
def profileColorCount (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) : ℕ :=
  ∑ u : Fin (n + 1), (f u).val

/-- Total vertex count encoded by a profile. -/
def profileVertexWeight (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) : ℕ :=
  ∑ u : Fin (n + 1), u.val * (f u).val

lemma mem_coloringProfileFinset_iff
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)} :
    f ∈ coloringProfileFinset n k t ↔
      profileVertexWeight n f = n ∧
      profileColorCount n f = k ∧
      ∀ u : Fin (n + 1), t < u.val → (f u).val = 0 := by
  simp [coloringProfileFinset, profileVertexWeight, profileColorCount]

lemma profileVertexWeight_eq_of_mem_coloringProfileFinset
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n k t) :
    profileVertexWeight n f = n := by
  exact (mem_coloringProfileFinset_iff.mp hf).1

lemma profileColorCount_eq_of_mem_coloringProfileFinset
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n k t) :
    profileColorCount n f = k := by
  exact (mem_coloringProfileFinset_iff.mp hf).2.1

/-- **Exact formula** for E_{n,k,t} = expected number of unordered t-bounded k-colorings
    of G(n, 1/2).

    From Heckel–Panagiotou (2023), Lemma 2.1 (lem:expxk) and eq. (2.3):

      E_{n,k,t} = ∑_{f ∈ P_{n,k,t}} P_f · (1/2)^{f_f} / ∏_u (f_u)!

    where the sum is over all t-bounded k-profiles on n vertices,
    P_f = n! / ∏_u (u!)^{f_u} and f_f = ∑_u C(u,2) · f_u.
-/
noncomputable def expectedTBoundedColorings (n k t : ℕ) : ℝ :=
  ∑ f ∈ coloringProfileFinset n k t,
    let fu : Fin (n + 1) → ℕ := fun u => (f u).val
    (profileP n fu : ℝ) * (1 / 2 : ℝ) ^ profileF n fu / (profileSymm n fu : ℝ)

/-- The single-profile contribution to `expectedTBoundedColorings`.

This is the paper-level quantity underlying the expectation of
`\bar X_{\mathbf{k}}` for a fixed coloring profile `f`. The current Lean
development mostly works with the fully summed quantity
`expectedTBoundedColorings`; exposing the profile-level summand makes the next
paper-aligned route explicit. -/
noncomputable def profileContribution
    (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) : ℝ :=
  let fu : Fin (n + 1) → ℕ := fun u => (f u).val
  (profileP n fu : ℝ) * (1 / 2 : ℝ) ^ profileF n fu / (profileSymm n fu : ℝ)

lemma profileContribution_eq
    (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) :
    profileContribution n f =
      let fu : Fin (n + 1) → ℕ := fun u => (f u).val
      (profileP n fu : ℝ) * (1 / 2 : ℝ) ^ profileF n fu / (profileSymm n fu : ℝ) := by
  simp [profileContribution]

lemma profileContribution_eq_of_mem_coloringProfileFinset
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n k t) :
    profileContribution n f =
      let fu : Fin (n + 1) → ℕ := fun u => (f u).val
      (profileP n fu : ℝ) * (1 / 2 : ℝ) ^ profileF n fu / (profileSymm n fu : ℝ) := by
  simp [profileContribution]

lemma profileContribution_nonneg
    (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) :
    0 ≤ profileContribution n f := by
  rw [profileContribution_eq]
  positivity

lemma profileContribution_nonneg_of_mem_coloringProfileFinset
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n k t) :
    0 ≤ profileContribution n f := by
  exact profileContribution_nonneg n f

lemma profileContribution_pos_of_profileP_pos
    (n : ℕ) (f : Fin (n + 1) → Fin (n + 1))
    (hP : 0 < profileP n (fun u => (f u).val)) :
    0 < profileContribution n f := by
  rw [profileContribution_eq]
  have hP' : 0 < (profileP n (fun u => (f u).val) : ℝ) := by
    exact_mod_cast hP
  have hPow' : 0 < (1 / 2 : ℝ) ^ profileF n (fun u => (f u).val) := by
    exact pow_pos (by norm_num : (0 : ℝ) < 1 / 2) _
  have hSymm' : 0 < (profileSymm n (fun u => (f u).val) : ℝ) := by
    exact_mod_cast Finset.prod_pos (fun u _ => Nat.factorial_pos ((f u).val))
  positivity

lemma profileContribution_eq_exp_log
    (n : ℕ) (f : Fin (n + 1) → Fin (n + 1))
    (hpos : 0 < profileContribution n f) :
    profileContribution n f = Real.exp (Real.log (profileContribution n f)) := by
  rw [Real.exp_log hpos]

lemma log_profileContribution_eq_of_profileP_pos
    (n : ℕ) (f : Fin (n + 1) → Fin (n + 1))
    (hP : 0 < profileP n (fun u => (f u).val)) :
    Real.log (profileContribution n f) =
      Real.log (profileP n (fun u => (f u).val)) +
        (profileF n (fun u => (f u).val) : ℝ) * Real.log (1 / 2 : ℝ) -
        Real.log (profileSymm n (fun u => (f u).val)) := by
  rw [profileContribution_eq]
  have hP' : 0 < (profileP n (fun u => (f u).val) : ℝ) := by exact_mod_cast hP
  have hPow' : 0 < (1 / 2 : ℝ) ^ profileF n (fun u => (f u).val) := by
    exact pow_pos (by norm_num : (0 : ℝ) < 1 / 2) _
  have hSymm' : 0 < (profileSymm n (fun u => (f u).val) : ℝ) := by
    exact_mod_cast Finset.prod_pos (fun u _ => Nat.factorial_pos ((f u).val))
  have hlogpow :
      Real.log ((1 / 2 : ℝ) ^ profileF n (fun u => (f u).val)) =
        (profileF n (fun u => (f u).val) : ℝ) * Real.log (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, Real.log_rpow (by positivity : (0 : ℝ) < 1 / 2)]
  rw [Real.log_div (mul_ne_zero hP'.ne' hPow'.ne') hSymm'.ne',
    Real.log_mul hP'.ne' hPow'.ne', hlogpow]

lemma profileF_log_half_eq_neg_log_two
    (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) :
    (profileF n (fun u => (f u).val) : ℝ) * Real.log (1 / 2 : ℝ) =
      -((profileF n (fun u => (f u).val) : ℝ) * Real.log 2) := by
  rw [show Real.log (1 / 2 : ℝ) = -Real.log 2 by
        rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]]
  simpa [neg_mul]

lemma profileF_eq_sum_choose_mul
    (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) :
    (profileF n (fun u => (f u).val) : ℝ) =
      ∑ u : Fin (n + 1), ((Nat.choose u.val 2 * (f u).val : ℕ) : ℝ) := by
  unfold profileF
  norm_num [Nat.cast_sum]

lemma profileF_eq_sum_quadratic
    (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) :
    (profileF n (fun u => (f u).val) : ℝ) =
      ∑ u : Fin (n + 1),
        ((((u.val * (u.val - 1)) / 2 : ℕ) * (f u).val : ℕ) : ℝ) := by
  rw [profileF_eq_sum_choose_mul]
  refine Finset.sum_congr rfl ?_
  intro u hu
  rw [Nat.choose_two_right]

lemma profileContribution_le_exp_of_log_bound
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)} {B : ℝ}
    (hpos : 0 < profileContribution n f)
    (hlog : Real.log (profileContribution n f) ≤ B) :
    profileContribution n f ≤ Real.exp B := by
  rw [profileContribution_eq_exp_log n f hpos]
  exact Real.exp_le_exp.mpr hlog

lemma profileContribution_le_exp_of_combinatorial_log_bound
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)} {B : ℝ}
    (hpos : 0 < profileContribution n f)
    (hP : 0 < profileP n (fun u => (f u).val))
    (hcomb :
      Real.log (profileP n (fun u => (f u).val)) -
        Real.log (profileSymm n (fun u => (f u).val)) -
        ((profileF n (fun u => (f u).val) : ℝ) * Real.log 2) ≤ B) :
    profileContribution n f ≤ Real.exp B := by
  apply profileContribution_le_exp_of_log_bound hpos
  rw [log_profileContribution_eq_of_profileP_pos n f hP, profileF_log_half_eq_neg_log_two]
  linarith

/-- The additive combinatorial core in `log(profileContribution)`, separated
from the paper's explicit `phi` and remainder terms. This is the exact piece
that remains to be upper-bounded in the next `cont2` step. -/
noncomputable def profileCombinatorialLogCore
    (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) : ℝ :=
  Real.log (profileP n (fun u => (f u).val)) -
    Real.log (profileSymm n (fun u => (f u).val)) -
    ((profileF n (fun u => (f u).val) : ℝ) * Real.log 2)

lemma profileContribution_le_exp_of_core_bound
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)} {B : ℝ}
    (hpos : 0 < profileContribution n f)
    (hP : 0 < profileP n (fun u => (f u).val))
    (hcore : profileCombinatorialLogCore n f ≤ B) :
    profileContribution n f ≤ Real.exp B := by
  apply profileContribution_le_exp_of_combinatorial_log_bound hpos hP
  simpa [profileCombinatorialLogCore] using hcore

private lemma expectedTBoundedColorings_eq_sum_profileContribution
    (n k t : ℕ) :
    expectedTBoundedColorings n k t =
      ∑ f ∈ coloringProfileFinset n k t, profileContribution n f := by
  simp [expectedTBoundedColorings, profileContribution]

/-- Paper-style support condition appearing in `expectationlemma` and
    `lemmaupperbound`: all nonzero class sizes lie between `0.1 α` and `10 α`,
    where `α = thresholdFloor n`. -/
def ProfileConcentratedNearThreshold
    (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) : Prop :=
  ∀ u : Fin (n + 1), 0 < (f u).val →
    ((thresholdFloor n : ℝ) / 10 ≤ u.val) ∧
      (u.val ≤ 10 * thresholdFloor n)

/-- The paper's `κ_u`: fraction of vertices contained in colour classes of size
`u`, for a fixed profile `f`. -/
noncomputable def profileVertexFractionAt
    (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) (u : Fin (n + 1)) : ℝ :=
  ((u.val * (f u).val : ℕ) : ℝ) / n

/-- Total vertex mass `κ = ∑_u κ_u` associated to a profile. For complete
profiles this should equal `1`. -/
noncomputable def profileVertexFractionMass
    (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) : ℝ :=
  ∑ u : Fin (n + 1), profileVertexFractionAt n f u

/-- The paper's first-moment exponent `φ(κ)` specialized to `p = 1/2`. This is
the natural exponent appearing in `expectationlemma` and the quick proof of
`lemmaupperbound`. -/
noncomputable def profilePhi
    (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) : ℝ :=
  -(1 - profileVertexFractionMass n f) * Real.log (1 - profileVertexFractionMass n f) +
    (Real.log 2 / 2) *
      ∑ u : Fin (n + 1),
        profileVertexFractionAt n f u *
          (threshold n - (1 + 2 / Real.log 2) - u.val)

/-- Paper remainder term `R = ∑ (\alpha-u) k_u + n log log n / log n` from the
derivation of `cont2`, specialized to `p = 1/2` and complete profiles. We keep
only the explicit shape needed for the current sharp-route decomposition. -/
noncomputable def profileRemainder
    (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) : ℝ :=
  ∑ u : Fin (n + 1), (thresholdFloor n - u.val : ℤ) * (f u).val +
    (n : ℝ) * Real.log (Real.log n) / Real.log n

lemma profileVertexFractionAt_mul
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)} {u : Fin (n + 1)}
    (hn : 0 < n) :
    profileVertexFractionAt n f u * n = ((u.val * (f u).val : ℕ) : ℝ) := by
  unfold profileVertexFractionAt
  field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hn)]

lemma profileVertexFractionAt_mul_eq
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)} {u : Fin (n + 1)}
    (hn : 0 < n) :
    profileVertexFractionAt n f u * (n : ℝ) = ((u.val * (f u).val : ℕ) : ℝ) :=
  profileVertexFractionAt_mul hn

lemma profileCount_eq_vertexFraction_mul_div
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)} {u : Fin (n + 1)}
    (hn : 0 < n) (hu : 0 < u.val) :
    ((f u).val : ℝ) = profileVertexFractionAt n f u * n / u.val := by
  have huR : (u.val : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hu)
  have hmul := profileVertexFractionAt_mul (n := n) (f := f) (u := u) hn
  have hnat :
      (((u.val * (f u).val : ℕ) : ℝ)) = (u.val : ℝ) * (f u).val := by
    norm_num [Nat.cast_mul]
  rw [hmul, hnat]
  field_simp [huR]

lemma profileVertexFractionMass_eq_one_of_mem_coloringProfileFinset
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hn : 0 < n)
    (hf : f ∈ coloringProfileFinset n k t) :
    profileVertexFractionMass n f = 1 := by
  have hweight : profileVertexWeight n f = n :=
    profileVertexWeight_eq_of_mem_coloringProfileFinset hf
  unfold profileVertexFractionMass profileVertexFractionAt
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  have hcast :
      (↑(∑ u : Fin (n + 1), u.val * (f u).val) : ℝ) = (n : ℝ) := by
    exact congrArg (fun m : ℕ => (m : ℝ)) hweight
  have hcast' :
      (∑ i : Fin (n + 1), ((i.val * (f i).val : ℕ) : ℝ)) = (n : ℝ) := by
    simpa using hcast
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  change ((∑ i : Fin (n + 1), ((i.val * (f i).val : ℕ) : ℝ)) * (n : ℝ)⁻¹) = 1
  rw [hcast']
  simpa using mul_inv_cancel₀ hnR

lemma profilePhi_eq_of_mem_coloringProfileFinset
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hn : 0 < n)
    (hf : f ∈ coloringProfileFinset n k t) :
    profilePhi n f =
      (Real.log 2 / 2) *
        ∑ u : Fin (n + 1),
          profileVertexFractionAt n f u *
            (threshold n - (1 + 2 / Real.log 2) - u.val) := by
  rw [profilePhi, profileVertexFractionMass_eq_one_of_mem_coloringProfileFinset hn hf]
  norm_num

lemma profilePhi_mul_n_eq_of_mem_coloringProfileFinset
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hn : 0 < n)
    (hf : f ∈ coloringProfileFinset n k t) :
    profilePhi n f * n =
      (Real.log 2 / 2) *
        ∑ u : Fin (n + 1),
          (((u.val * (f u).val : ℕ) : ℝ) *
            (threshold n - (1 + 2 / Real.log 2) - u.val)) := by
  rw [profilePhi_eq_of_mem_coloringProfileFinset hn hf]
  calc
    ((Real.log 2 / 2) *
        ∑ u : Fin (n + 1),
          profileVertexFractionAt n f u *
            (threshold n - (1 + 2 / Real.log 2) - u.val)) * n
        = (Real.log 2 / 2) *
            ((∑ u : Fin (n + 1),
              profileVertexFractionAt n f u *
                (threshold n - (1 + 2 / Real.log 2) - u.val)) * n) := by
            ring
    _ = (Real.log 2 / 2) *
        ∑ u : Fin (n + 1),
          (profileVertexFractionAt n f u * n) *
            (threshold n - (1 + 2 / Real.log 2) - u.val) := by
          congr 1
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro u hu
          ring
    _ = (Real.log 2 / 2) *
        ∑ u : Fin (n + 1),
          (((u.val * (f u).val : ℕ) : ℝ) *
            (threshold n - (1 + 2 / Real.log 2) - u.val)) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro u hu
          rw [profileVertexFractionAt_mul hn]

lemma profilePhi_mul_n_add_remainder_eq_of_mem_coloringProfileFinset
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hn : 0 < n)
    (hf : f ∈ coloringProfileFinset n k t) :
    profilePhi n f * n + profileRemainder n f =
      (Real.log 2 / 2) *
        ∑ u : Fin (n + 1),
          (((u.val * (f u).val : ℕ) : ℝ) *
            (threshold n - (1 + 2 / Real.log 2) - u.val)) +
      ∑ u : Fin (n + 1), (thresholdFloor n - u.val : ℤ) * (f u).val +
      (n : ℝ) * Real.log (Real.log n) / Real.log n := by
  rw [profilePhi_mul_n_eq_of_mem_coloringProfileFinset hn hf, profileRemainder]
  ring

lemma profileRemainder_integer_term_eq_of_mem_coloringProfileFinset_real
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n k t) :
    ((∑ u : Fin (n + 1), (thresholdFloor n - u.val : ℤ) * (f u).val : ℤ) : ℝ) =
      (thresholdFloor n : ℝ) * k - n := by
  have hcountR :
      (∑ u : Fin (n + 1), ((f u).val : ℝ)) = k := by
    simpa [profileColorCount] using
      congrArg (fun m : ℕ => (m : ℝ)) (profileColorCount_eq_of_mem_coloringProfileFinset hf)
  have hweightR :
      (∑ u : Fin (n + 1), ((u.val * (f u).val : ℕ) : ℝ)) = n := by
    simpa [profileVertexWeight] using
      congrArg (fun m : ℕ => (m : ℝ)) (profileVertexWeight_eq_of_mem_coloringProfileFinset hf)
  calc
    ((∑ u : Fin (n + 1), (thresholdFloor n - u.val : ℤ) * (f u).val : ℤ) : ℝ)
        = ∑ u : Fin (n + 1), (((thresholdFloor n - u.val : ℤ) * (f u).val : ℤ) : ℝ) := by
            norm_num
    _ = ∑ u : Fin (n + 1), ((thresholdFloor n : ℝ) * (f u).val - ((u.val * (f u).val : ℕ) : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro u hu
          norm_num [Nat.cast_mul]
          ring
    _ = (∑ u : Fin (n + 1), (thresholdFloor n : ℝ) * (f u).val) -
          ∑ u : Fin (n + 1), ((u.val * (f u).val : ℕ) : ℝ) := by
            rw [Finset.sum_sub_distrib]
    _ = (thresholdFloor n : ℝ) * k -
          ∑ u : Fin (n + 1), ((u.val * (f u).val : ℕ) : ℝ) := by
            rw [← Finset.mul_sum, hcountR]
    _ = (thresholdFloor n : ℝ) * k - n := by
          rw [hweightR]

lemma profileRemainder_scalar_term_eq_sum_thresholdFloor_minus_u_of_mem
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n k t) :
    (thresholdFloor n : ℝ) * k - n =
      ∑ u : Fin (n + 1), ((f u).val : ℝ) * (thresholdFloor n - u.val) := by
  have hcountR :
      (∑ u : Fin (n + 1), ((f u).val : ℝ)) = k := by
    simpa [profileColorCount] using
      congrArg (fun m : ℕ => (m : ℝ)) (profileColorCount_eq_of_mem_coloringProfileFinset hf)
  have hweightR :
      (∑ u : Fin (n + 1), ((u.val * (f u).val : ℕ) : ℝ)) = n := by
    simpa [profileVertexWeight] using
      congrArg (fun m : ℕ => (m : ℝ)) (profileVertexWeight_eq_of_mem_coloringProfileFinset hf)
  calc
    (thresholdFloor n : ℝ) * k - n
        = (thresholdFloor n : ℝ) * (∑ u : Fin (n + 1), ((f u).val : ℝ)) -
            ∑ u : Fin (n + 1), ((u.val * (f u).val : ℕ) : ℝ) := by
              rw [hcountR, hweightR]
    _ = ∑ u : Fin (n + 1), ((thresholdFloor n : ℝ) * ((f u).val : ℝ)) -
            ∑ u : Fin (n + 1), ((u.val * (f u).val : ℕ) : ℝ) := by
              rw [← Finset.mul_sum]
    _ = ∑ u : Fin (n + 1),
          (((thresholdFloor n : ℝ) * ((f u).val : ℝ)) -
            ((u.val * (f u).val : ℕ) : ℝ)) := by
              rw [← Finset.sum_sub_distrib]
    _ = ∑ u : Fin (n + 1), ((f u).val : ℝ) * (thresholdFloor n - u.val) := by
          refine Finset.sum_congr rfl ?_
          intro u hu
          norm_num [Nat.cast_mul]
          ring

/-- The precise pointwise inequality on the combinatorial log-core that would
imply the paper's `cont2`-style bound for one profile. -/
def ProfileCombinatorialCoreCont2BoundPointwise
    (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) : Prop :=
  profileCombinatorialLogCore n f ≤ profilePhi n f * n + profileRemainder n f

lemma cont2Pointwise_of_core_bound
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hpos : 0 < profileContribution n f)
    (hP : 0 < profileP n (fun u => (f u).val))
    (hcore : ProfileCombinatorialCoreCont2BoundPointwise n f) :
    profileContribution n f ≤ Real.exp (profilePhi n f * n + profileRemainder n f) := by
  exact profileContribution_le_exp_of_core_bound hpos hP hcore

/-- Average colour-class size of a complete profile. -/
noncomputable def profileAverageClassSize
    (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) : ℝ :=
  let k : ℕ := ∑ u : Fin (n + 1), (f u).val
  (n : ℝ) / k

lemma profileAverageClassSize_eq_of_mem_coloringProfileFinset
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n k t) :
    profileAverageClassSize n f = (n : ℝ) / k := by
  have hcountR :
      ((∑ u : Fin (n + 1), (f u).val : ℕ) : ℝ) = (k : ℝ) := by
    exact congrArg (fun m : ℕ => (m : ℝ)) (profileColorCount_eq_of_mem_coloringProfileFinset hf)
  simp [profileAverageClassSize, hcountR]

lemma profileColorCount_pos_of_mem_coloringProfileFinset
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hn : 0 < n)
    (hf : f ∈ coloringProfileFinset n k t) :
    0 < k := by
  by_contra hk
  have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
  have hsum0 : ∑ u : Fin (n + 1), (f u).val = 0 := by
    simpa [profileColorCount, hk0] using profileColorCount_eq_of_mem_coloringProfileFinset hf
  have hzero : ∀ u : Fin (n + 1), (f u).val = 0 := by
    intro u
    have hle : (f u).val ≤ ∑ v : Fin (n + 1), (f v).val := by
      exact Finset.single_le_sum
        (f := fun v : Fin (n + 1) => (f v).val)
        (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ u)
    rw [hsum0] at hle
    exact Nat.eq_zero_of_le_zero hle
  have hweight0 : profileVertexWeight n f = 0 := by
    unfold profileVertexWeight
    simp [hzero]
  have hweight : profileVertexWeight n f = n :=
    profileVertexWeight_eq_of_mem_coloringProfileFinset hf
  omega

private lemma real_titu_finset
    {ι : Type*} (s : Finset ι) (a w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 < w i) :
    (∑ i ∈ s, a i) ^ 2 / (∑ i ∈ s, w i) ≤
      ∑ i ∈ s, a i ^ 2 / w i := by
  simpa using (Finset.sq_sum_div_le_sum_sq_div (s := s) (f := a) (g := w) hw)

private def profilePositiveSupport
    (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun u => 0 < (f u).val)

lemma sum_profileColorCount_over_positiveSupport
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n k t) :
    ∑ u ∈ profilePositiveSupport n f, (f u).val = k := by
  rw [show ∑ u ∈ profilePositiveSupport n f, (f u).val =
      ∑ u : Fin (n + 1), if 0 < (f u).val then (f u).val else 0 by
        simp [profilePositiveSupport, Finset.sum_filter]]
  rw [← profileColorCount_eq_of_mem_coloringProfileFinset hf]
  refine Finset.sum_congr rfl ?_
  intro u hu
  by_cases hpos : 0 < (f u).val
  · simp [hpos]
  · simp [hpos, Nat.eq_zero_of_not_pos hpos]

lemma sum_profileVertexWeight_over_positiveSupport
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n k t) :
    ∑ u ∈ profilePositiveSupport n f, u.val * (f u).val = n := by
  calc
    ∑ u ∈ profilePositiveSupport n f, u.val * (f u).val
        = ∑ u : Fin (n + 1), if 0 < (f u).val then u.val * (f u).val else 0 := by
            simp [profilePositiveSupport, Finset.sum_filter]
    _ = ∑ u : Fin (n + 1), u.val * (f u).val := by
          refine Finset.sum_congr rfl ?_
          intro u hu
          by_cases hpos : 0 < (f u).val
          · simp [hpos]
          · simp [hpos, Nat.eq_zero_of_not_pos hpos]
    _ = n := profileVertexWeight_eq_of_mem_coloringProfileFinset hf

lemma sum_profileColorCount_over_positiveSupport_real
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n k t) :
    ∑ u ∈ profilePositiveSupport n f, ((f u).val : ℝ) = (k : ℝ) := by
  simpa using congrArg (fun m : ℕ => (m : ℝ))
    (sum_profileColorCount_over_positiveSupport hf)

lemma sum_profileVertexWeight_over_positiveSupport_real
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n k t) :
    ∑ u ∈ profilePositiveSupport n f, ((u.val * (f u).val : ℕ) : ℝ) = (n : ℝ) := by
  simpa using congrArg (fun m : ℕ => (m : ℝ))
    (sum_profileVertexWeight_over_positiveSupport hf)

lemma profileSizeBiasedAverage_ge_averageClassSize
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hn : 0 < n)
    (hf : f ∈ coloringProfileFinset n k t) :
    (n : ℝ) / k ≤
      ∑ u : Fin (n + 1), profileVertexFractionAt n f u * u.val := by
  let s := profilePositiveSupport n f
  have hk : 0 < k := profileColorCount_pos_of_mem_coloringProfileFinset hn hf
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hw : ∀ u ∈ s, 0 < ((f u).val : ℝ) := by
    intro u hu
    exact_mod_cast (Finset.mem_filter.mp hu).2
  have htitu :=
    real_titu_finset s
      (fun u => ((u.val * (f u).val : ℕ) : ℝ))
      (fun u => ((f u).val : ℝ))
      hw
  have hbase : (n : ℝ) ^ 2 / k ≤
      ∑ u ∈ s, (((u.val * (f u).val : ℕ) : ℝ) ^ 2) / ((f u).val : ℝ) := by
    rw [sum_profileVertexWeight_over_positiveSupport_real hf,
      sum_profileColorCount_over_positiveSupport_real hf] at htitu
    simpa using htitu
  have hdiv :
      (n : ℝ) / k ≤
        (∑ u ∈ s, (((u.val * (f u).val : ℕ) : ℝ) ^ 2) / ((f u).val : ℝ)) / n := by
    apply (le_div_iff₀ hnR).2
    simpa [pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hbase
  have hsimpl_support :
      (∑ u ∈ s, (((u.val * (f u).val : ℕ) : ℝ) ^ 2) / ((f u).val : ℝ)) / n =
        ∑ u ∈ s, profileVertexFractionAt n f u * u.val := by
    calc
      (∑ u ∈ s, (((u.val * (f u).val : ℕ) : ℝ) ^ 2) / ((f u).val : ℝ)) / n
          = ∑ u ∈ s, ((((u.val * (f u).val : ℕ) : ℝ) ^ 2) / ((f u).val : ℝ)) * (n : ℝ)⁻¹ := by
              rw [div_eq_mul_inv, Finset.sum_mul]
      _ = ∑ u ∈ s, profileVertexFractionAt n f u * u.val := by
            refine Finset.sum_congr rfl ?_
            intro u hu
            have hpos : 0 < (f u).val := (Finset.mem_filter.mp hu).2
            have hfu : (((f u).val : ℝ)) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hpos)
            unfold profileVertexFractionAt
            field_simp [hfu, show (n : ℝ) ≠ 0 by exact ne_of_gt hnR]
            have hnat : (u.val * (f u).val) ^ 2 = (u.val * (f u).val) * (f u).val * u.val := by
              rw [pow_two]
              ring_nf
            exact_mod_cast hnat
  have hsimpl_all :
      ∑ u ∈ s, profileVertexFractionAt n f u * u.val =
        ∑ u : Fin (n + 1), profileVertexFractionAt n f u * u.val := by
    calc
      ∑ u ∈ s, profileVertexFractionAt n f u * u.val
          = ∑ u : Fin (n + 1), if 0 < (f u).val then profileVertexFractionAt n f u * u.val else 0 := by
              simp [s, profilePositiveSupport, Finset.sum_filter]
      _ = ∑ u : Fin (n + 1), profileVertexFractionAt n f u * u.val := by
            refine Finset.sum_congr rfl ?_
            intro u hu
            by_cases hpos : 0 < (f u).val
            · simp [hpos]
            · have hzero : (f u).val = 0 := Nat.eq_zero_of_not_pos hpos
              simp [hpos, hzero, profileVertexFractionAt]
  calc
    (n : ℝ) / k
        ≤ (∑ u ∈ s, (((u.val * (f u).val : ℕ) : ℝ) ^ 2) / ((f u).val : ℝ)) / n := hdiv
    _ = ∑ u ∈ s, profileVertexFractionAt n f u * u.val := hsimpl_support
    _ = ∑ u : Fin (n + 1), profileVertexFractionAt n f u * u.val := hsimpl_all

/-- The minimal sharp upper-bound target suggested by paper Lemma `lemmaupperbound`.

This is intentionally phrased for a single profile and a fixed constant buffer
`C`, matching the paper statement before any asymptotic packaging. -/
noncomputable def ProfileUpperBoundRegime
    (C : ℝ) (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) : Prop :=
  ProfileConcentratedNearThreshold n f ∧
  threshold n - (1 + 2 / Real.log 2) + C < profileAverageClassSize n f

lemma profileConcentratedNearThreshold_of_upperBoundRegime
    {C : ℝ} {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : ProfileUpperBoundRegime C n f) :
    ProfileConcentratedNearThreshold n f :=
  hf.1

lemma profileAverageClassSize_lt_of_upperBoundRegime
    {C : ℝ} {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : ProfileUpperBoundRegime C n f) :
    threshold n - (1 + 2 / Real.log 2) + C < profileAverageClassSize n f :=
  hf.2

lemma profileAverageClassSize_lt_div_of_upperBoundRegime
    {C : ℝ} {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hfmem : f ∈ coloringProfileFinset n k t)
    (hreg : ProfileUpperBoundRegime C n f) :
    threshold n - (1 + 2 / Real.log 2) + C < (n : ℝ) / k := by
  rw [← profileAverageClassSize_eq_of_mem_coloringProfileFinset hfmem]
  exact profileAverageClassSize_lt_of_upperBoundRegime hreg

lemma profilePhi_lt_neg_buffer_of_upperBoundRegime
    {C : ℝ} {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hn : 0 < n)
    (hf : f ∈ coloringProfileFinset n k t)
    (hreg : ProfileUpperBoundRegime C n f) :
    profilePhi n f < -(Real.log 2 / 2) * C := by
  let A : ℝ := threshold n - (1 + 2 / Real.log 2)
  have havg : A + C < (n : ℝ) / k := by
    simpa [A] using profileAverageClassSize_lt_div_of_upperBoundRegime hf hreg
  have hsize :
      (n : ℝ) / k ≤ ∑ u : Fin (n + 1), profileVertexFractionAt n f u * u.val :=
    profileSizeBiasedAverage_ge_averageClassSize hn hf
  have hgt :
      A + C < ∑ u : Fin (n + 1), profileVertexFractionAt n f u * u.val :=
    lt_of_lt_of_le havg hsize
  have hmass : profileVertexFractionMass n f = 1 :=
    profileVertexFractionMass_eq_one_of_mem_coloringProfileFinset hn hf
  have hsumA :
      ∑ u : Fin (n + 1), profileVertexFractionAt n f u * A =
        A * profileVertexFractionMass n f := by
    calc
      ∑ u : Fin (n + 1), profileVertexFractionAt n f u * A
          = ∑ u : Fin (n + 1), A * profileVertexFractionAt n f u := by
              refine Finset.sum_congr rfl ?_
              intro u hu
              ring
      _ = A * ∑ u : Fin (n + 1), profileVertexFractionAt n f u := by
              rw [Finset.mul_sum]
      _ = A * profileVertexFractionMass n f := by
              rw [profileVertexFractionMass]
  have hsum :
      ∑ u : Fin (n + 1),
        profileVertexFractionAt n f u * (A - u.val) =
      A - ∑ u : Fin (n + 1), profileVertexFractionAt n f u * u.val := by
    calc
      ∑ u : Fin (n + 1), profileVertexFractionAt n f u * (A - u.val)
          = ∑ u : Fin (n + 1),
              (profileVertexFractionAt n f u * A -
                profileVertexFractionAt n f u * u.val) := by
              refine Finset.sum_congr rfl ?_
              intro u hu
              ring
      _ = (∑ u : Fin (n + 1), profileVertexFractionAt n f u * A) -
            ∑ u : Fin (n + 1), profileVertexFractionAt n f u * u.val := by
              rw [Finset.sum_sub_distrib]
      _ = A * profileVertexFractionMass n f -
            ∑ u : Fin (n + 1), profileVertexFractionAt n f u * u.val := by
              rw [hsumA]
      _ = A - ∑ u : Fin (n + 1), profileVertexFractionAt n f u * u.val := by
              rw [hmass, mul_one]
  have hAminus :
      A - ∑ u : Fin (n + 1), profileVertexFractionAt n f u * u.val < -C := by
    linarith
  rw [profilePhi_eq_of_mem_coloringProfileFinset hn hf, hsum]
  have hmul :
      (Real.log 2 / 2) * (A - ∑ u : Fin (n + 1), profileVertexFractionAt n f u * u.val) <
        (Real.log 2 / 2) * (-C) := by
    exact mul_lt_mul_of_pos_left hAminus (by positivity : 0 < Real.log 2 / 2)
  simpa [neg_mul, mul_comm, mul_left_comm, mul_assoc] using hmul

lemma profileUpperBoundRegime_sum_shift_lt_neg
    {C : ℝ} {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hn : 0 < n)
    (hf : f ∈ coloringProfileFinset n k t)
    (hreg : ProfileUpperBoundRegime C n f) :
    ∑ u : Fin (n + 1),
      ((f u).val : ℝ) * (threshold n - (1 + 2 / Real.log 2) - u.val) < -(C * k) := by
  let A : ℝ := threshold n - (1 + 2 / Real.log 2)
  have hk : 0 < k := profileColorCount_pos_of_mem_coloringProfileFinset hn hf
  have havg : A + C < (n : ℝ) / k := by
    simpa [A] using profileAverageClassSize_lt_div_of_upperBoundRegime hf hreg
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hkR
  have hmult : (A + C) * k < n := by
    have hmul' : (A + C) * (k : ℝ) < ((n : ℝ) / k) * k :=
      mul_lt_mul_of_pos_right havg hkR
    have hright : ((n : ℝ) / k) * k = n := by
      field_simp [hk_ne]
    rw [hright] at hmul'
    exact hmul'
  have hcountR :
      ∑ u : Fin (n + 1), ((f u).val : ℝ) = (k : ℝ) := by
    simpa [profileColorCount] using
      congrArg (fun m : ℕ => (m : ℝ)) (profileColorCount_eq_of_mem_coloringProfileFinset hf)
  have hweightR :
      ∑ u : Fin (n + 1), ((u.val * (f u).val : ℕ) : ℝ) = (n : ℝ) := by
    simpa [profileVertexWeight] using
      congrArg (fun m : ℕ => (m : ℝ)) (profileVertexWeight_eq_of_mem_coloringProfileFinset hf)
  have hsum :
      ∑ u : Fin (n + 1), ((f u).val : ℝ) * (A - u.val) =
        A * k - n := by
    have hsplit :
        ∑ u : Fin (n + 1), ((f u).val : ℝ) * (A - u.val) =
          (∑ u : Fin (n + 1), ((f u).val : ℝ) * A) -
            ∑ u : Fin (n + 1), ((f u).val : ℝ) * u.val := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
    have hsumA :
        ∑ u : Fin (n + 1), ((f u).val : ℝ) * A = k * A := by
      calc
        ∑ u : Fin (n + 1), ((f u).val : ℝ) * A
            = (∑ u : Fin (n + 1), ((f u).val : ℝ)) * A := by
                rw [← Finset.sum_mul]
        _ = k * A := by
              rw [hcountR]
    have hsumU :
        ∑ u : Fin (n + 1), ((f u).val : ℝ) * u.val = n := by
      have hterm :
          (fun u : Fin (n + 1) => ((f u).val : ℝ) * u.val) =
            fun u : Fin (n + 1) => ((u.val * (f u).val : ℕ) : ℝ) := by
        funext u
        norm_num [Nat.cast_mul, mul_comm]
      calc
        ∑ u : Fin (n + 1), ((f u).val : ℝ) * u.val
            = ∑ u : Fin (n + 1), ((u.val * (f u).val : ℕ) : ℝ) := by
                rw [hterm]
        _ = n := hweightR
    calc
      ∑ u : Fin (n + 1), ((f u).val : ℝ) * (A - u.val)
          = (∑ u : Fin (n + 1), ((f u).val : ℝ) * A) -
              ∑ u : Fin (n + 1), ((f u).val : ℝ) * u.val := hsplit
      _ = k * A - n := by rw [hsumA, hsumU]
      _ = A * k - n := by ring
  rw [hsum]
  linarith

lemma profileUpperBoundRegime_sum_threshold_minus_u_minus_one_le
    {C : ℝ} {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hn : 0 < n)
    (hf : f ∈ coloringProfileFinset n k t)
    (hreg : ProfileUpperBoundRegime C n f) :
    ∑ u : Fin (n + 1),
      ((f u).val : ℝ) * (threshold n - u.val - 1) ≤
        ((2 / Real.log 2) - C) * k := by
  have hshift :=
    profileUpperBoundRegime_sum_shift_lt_neg (C := C) hn hf hreg
  have hsumk : (∑ u : Fin (n + 1), ((f u).val : ℝ)) = k := by
    simpa [profileColorCount] using
      congrArg (fun m : ℕ => (m : ℝ)) (profileColorCount_eq_of_mem_coloringProfileFinset hf)
  have hconst :
      ∑ u : Fin (n + 1), ((f u).val : ℝ) * (2 / Real.log 2) =
        (2 / Real.log 2) * k := by
    calc
      ∑ u : Fin (n + 1), ((f u).val : ℝ) * (2 / Real.log 2)
          = (∑ u : Fin (n + 1), ((f u).val : ℝ)) * (2 / Real.log 2) := by
              rw [Finset.sum_mul]
      _ = k * (2 / Real.log 2) := by rw [hsumk]
      _ = (2 / Real.log 2) * k := by ring
  refine le_of_lt ?_
  calc
    ∑ u : Fin (n + 1), ((f u).val : ℝ) * (threshold n - u.val - 1)
        = ∑ u : Fin (n + 1),
            (((f u).val : ℝ) * (threshold n - (1 + 2 / Real.log 2) - u.val) +
              ((f u).val : ℝ) * (2 / Real.log 2)) := by
            congr 1
            funext u
            ring
    _ = ∑ u : Fin (n + 1),
            ((f u).val : ℝ) * (threshold n - (1 + 2 / Real.log 2) - u.val) +
              ∑ u : Fin (n + 1), ((f u).val : ℝ) * (2 / Real.log 2) := by
            rw [Finset.sum_add_distrib]
    _ = ∑ u : Fin (n + 1),
            ((f u).val : ℝ) * (threshold n - (1 + 2 / Real.log 2) - u.val) +
              (2 / Real.log 2) * k := by
            rw [hconst]
    _ < -(C * k) + (2 / Real.log 2) * k := by
          gcongr
    _ = ((2 / Real.log 2) - C) * k := by ring



/-- Minimal profile-level decay target suggested by `lemmaupperbound`.

For a fixed constant buffer `C > 0`, profiles in `ProfileUpperBoundRegime C`
should have exponentially small contribution. This is the sharp profile-level
object that the current Part B route is missing; unlike
`factorial_expectedTBoundedColorings_le_coarse`, it is meant to capture the
paper's quick proof after the refined formula `cont2`. -/
def ProfileContributionExpDecayTarget
    (C c : ℝ) (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) : Prop :=
  ProfileUpperBoundRegime C n f →
    profileContribution n f ≤ Real.exp (-c * n)

lemma profileContributionExpDecayTarget_iff
    {C c : ℝ} {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)} :
    ProfileContributionExpDecayTarget C c n f ↔
      (ProfileUpperBoundRegime C n f →
        profileContribution n f ≤ Real.exp (-c * n)) := by
  rfl

lemma profileContribution_le_expDecay_of_target
    {C c : ℝ} {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (htarget : ProfileContributionExpDecayTarget C c n f)
    (hreg : ProfileUpperBoundRegime C n f) :
    profileContribution n f ≤ Real.exp (-c * n) :=
  htarget hreg

lemma profileContributionExpDecayTarget_mono
    {C c c' : ℝ} {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hc : c ≤ c')
    (htarget : ProfileContributionExpDecayTarget C c' n f) :
    ProfileContributionExpDecayTarget C c n f := by
  intro hreg
  have hbase := htarget hreg
  refine hbase.trans ?_
  gcongr

/-- Eventual form of the profile-level decay target. -/
def EventualProfileContributionExpDecay
    (C c : ℝ) : Prop :=
  ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ f : Fin (n + 1) → Fin (n + 1),
      f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
      ProfileContributionExpDecayTarget C c n f

/-- First conservative constant choices for the profile-level upper-bound route.

We deliberately separate this from the eventual theorem statement so the next
proof attempt can target one concrete pair of constants instead of carrying
parameters through every line of the paper transfer. -/
def safeProfileUpperBoundBuffer : ℝ := 4

/-- A deliberately weak exponential-decay rate used as the first concrete target
    for the paper's `lemmaupperbound` route. -/
noncomputable def safeProfileDecayRate : ℝ := 1 / 10

/-- A concrete safe perturbation budget for the final profile-level route. -/
noncomputable def safeProfileRemainderBudget : ℝ := 1

/-- First concrete sharp profile-level target suggested by `lemmaupperbound`. -/
def EventualSafeProfileContributionExpDecay : Prop :=
  EventualProfileContributionExpDecay safeProfileUpperBoundBuffer safeProfileDecayRate

lemma safeProfileRemainderBudget_admissible :
    safeProfileRemainderBudget ≤
      (Real.log 2 / 2) * safeProfileUpperBoundBuffer - safeProfileDecayRate := by
  have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  norm_num [safeProfileRemainderBudget, safeProfileUpperBoundBuffer, safeProfileDecayRate] at hlog ⊢
  linarith

/-- Concrete one-profile upper-bound regime used for the first sharp transfer
target from `lemmaupperbound`. -/
def SafeProfileUpperBoundRegime
    (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) : Prop :=
  ProfileUpperBoundRegime safeProfileUpperBoundBuffer n f

lemma profileUpperBoundRegime_sum_threshold_minus_u_minus_one_le_of_safeUpperBoundRegime
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hn : 0 < n)
    (hf : f ∈ coloringProfileFinset n k t)
    (hreg : SafeProfileUpperBoundRegime n f) :
    ∑ u : Fin (n + 1),
      ((f u).val : ℝ) * (threshold n - u.val - 1) ≤
        ((2 / Real.log 2) - safeProfileUpperBoundBuffer) * k := by
  exact profileUpperBoundRegime_sum_threshold_minus_u_minus_one_le
    (C := safeProfileUpperBoundBuffer) hn hf hreg

lemma averageClassSize_lt_div_of_safeUpperBoundRegime
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n k t)
    (hreg : SafeProfileUpperBoundRegime n f) :
    threshold n - (1 + 2 / Real.log 2) + safeProfileUpperBoundBuffer < (n : ℝ) / k := by
  exact profileAverageClassSize_lt_div_of_upperBoundRegime
    (C := safeProfileUpperBoundBuffer) hf hreg

lemma safeAverageClassSize_mul_k_lt_n
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hn : 0 < n)
    (hf : f ∈ coloringProfileFinset n k t)
    (hreg : SafeProfileUpperBoundRegime n f) :
    (threshold n - (1 + 2 / Real.log 2) + safeProfileUpperBoundBuffer) * k < n := by
  have havg :
      threshold n - (1 + 2 / Real.log 2) + safeProfileUpperBoundBuffer < (n : ℝ) / k :=
    averageClassSize_lt_div_of_safeUpperBoundRegime hf hreg
  have hk : 0 < k := profileColorCount_pos_of_mem_coloringProfileFinset hn hf
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hkR
  have hmul :
      (threshold n - (1 + 2 / Real.log 2) + safeProfileUpperBoundBuffer) * (k : ℝ) <
        ((n : ℝ) / k) * k :=
    mul_lt_mul_of_pos_right havg hkR
  have hright : ((n : ℝ) / k) * k = n := by
    field_simp [hk_ne]
  rw [hright] at hmul
  simpa using hmul

lemma safeScalarRemainder_lt_linear_k_of_threshold_nonneg
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hn : 0 < n)
    (hf : f ∈ coloringProfileFinset n k t)
    (hth_nonneg : 0 ≤ threshold n)
    (hreg : SafeProfileUpperBoundRegime n f) :
    (thresholdFloor n : ℝ) * k - n <
      ((2 / Real.log 2) - 2) * k := by
  have hk : 0 < k := profileColorCount_pos_of_mem_coloringProfileFinset hn hf
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hA :
      (threshold n - (1 + 2 / Real.log 2) + safeProfileUpperBoundBuffer) * k < n :=
    safeAverageClassSize_mul_k_lt_n hn hf hreg
  have hfloor :
      (thresholdFloor n : ℝ) < (threshold n : ℝ) + 1 := by
    have hfloor_le : (thresholdFloor n : ℝ) ≤ threshold n := by
      exact Nat.floor_le hth_nonneg
    linarith
  have hcoeff :
      threshold n + 1 =
        (threshold n - (1 + 2 / Real.log 2) + safeProfileUpperBoundBuffer) +
          ((2 / Real.log 2) - 2) := by
    simp [safeProfileUpperBoundBuffer]
    ring
  have hmul :
      (thresholdFloor n : ℝ) * k <
        ((threshold n - (1 + 2 / Real.log 2) + safeProfileUpperBoundBuffer) +
          ((2 / Real.log 2) - 2)) * k := by
    rw [← hcoeff]
    apply mul_lt_mul_of_pos_right hfloor hkR
  have hsplit :
      (((threshold n - (1 + 2 / Real.log 2) + safeProfileUpperBoundBuffer) +
          ((2 / Real.log 2) - 2)) : ℝ) * k =
        (threshold n - (1 + 2 / Real.log 2) + safeProfileUpperBoundBuffer) * k +
          (((2 / Real.log 2) - 2) : ℝ) * k := by
    ring
  rw [hsplit] at hmul
  linarith

lemma profilePhi_lt_safe_neg_buffer_of_safeUpperBoundRegime
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hn : 0 < n)
    (hf : f ∈ coloringProfileFinset n k t)
    (hreg : SafeProfileUpperBoundRegime n f) :
    profilePhi n f < -(Real.log 2 / 2) * safeProfileUpperBoundBuffer := by
  exact profilePhi_lt_neg_buffer_of_upperBoundRegime hn hf hreg

lemma profileUpperBoundRegime_weighted_sum_shift_lt_neg_n
    {C : ℝ} {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hn : 0 < n)
    (hf : f ∈ coloringProfileFinset n k t)
    (hreg : ProfileUpperBoundRegime C n f) :
    ∑ u : Fin (n + 1),
      (((u.val * (f u).val : ℕ) : ℝ) *
        (threshold n - (1 + 2 / Real.log 2) - u.val)) < -(C * n) := by
  have hphi : profilePhi n f < -(Real.log 2 / 2) * C :=
    profilePhi_lt_neg_buffer_of_upperBoundRegime hn hf hreg
  have hphi_mul :
      profilePhi n f * n < (-(Real.log 2 / 2) * C) * n := by
    exact mul_lt_mul_of_pos_right hphi (by positivity : (0 : ℝ) < n)
  rw [profilePhi_mul_n_eq_of_mem_coloringProfileFinset hn hf] at hphi_mul
  have hpos : 0 < Real.log 2 / 2 := by positivity
  have hphi_mul' :
      (Real.log 2 / 2) *
          ∑ u : Fin (n + 1),
            (((u.val * (f u).val : ℕ) : ℝ) *
              (threshold n - (1 + 2 / Real.log 2) - u.val))
        <
      (Real.log 2 / 2) * (-(C * n)) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hphi_mul
  have hsum := lt_of_mul_lt_mul_left hphi_mul' hpos.le
  simpa [mul_assoc, mul_left_comm, mul_comm] using hsum

lemma profileUpperBoundRegime_weighted_sum_shift_lt_neg_n_of_safeUpperBoundRegime
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hn : 0 < n)
    (hf : f ∈ coloringProfileFinset n k t)
    (hreg : SafeProfileUpperBoundRegime n f) :
    ∑ u : Fin (n + 1),
      (((u.val * (f u).val : ℕ) : ℝ) *
        (threshold n - (1 + 2 / Real.log 2) - u.val)) < -(safeProfileUpperBoundBuffer * n) := by
  exact profileUpperBoundRegime_weighted_sum_shift_lt_neg_n
    (C := safeProfileUpperBoundBuffer) hn hf hreg

lemma profileUpperBoundRegime_sum_thresholdFloor_minus_u_le_of_safeUpperBoundRegime
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hn : 0 < n)
    (hf : f ∈ coloringProfileFinset n k t)
    (hth_nonneg : 0 ≤ threshold n)
    (hreg : SafeProfileUpperBoundRegime n f) :
    ∑ u : Fin (n + 1), ((f u).val : ℝ) * (thresholdFloor n - u.val) ≤
      ((2 / Real.log 2) - 3) * k := by
  have hbase :
      ∑ u : Fin (n + 1), ((f u).val : ℝ) * (threshold n - u.val - 1) ≤
        ((2 / Real.log 2) - safeProfileUpperBoundBuffer) * k :=
    profileUpperBoundRegime_sum_threshold_minus_u_minus_one_le_of_safeUpperBoundRegime hn hf hreg
  have hfloor_le : (thresholdFloor n : ℝ) ≤ threshold n := by
    exact Nat.floor_le hth_nonneg
  have hpoint :
      ∀ u : Fin (n + 1),
        ((f u).val : ℝ) * (thresholdFloor n - u.val) ≤
          ((f u).val : ℝ) * (threshold n - u.val - 1 + 1) := by
    intro u
    gcongr
    linarith
  have hsum :
      ∑ u : Fin (n + 1), ((f u).val : ℝ) * (thresholdFloor n - u.val) ≤
        ∑ u : Fin (n + 1), ((f u).val : ℝ) * (threshold n - u.val - 1 + 1) := by
    exact Finset.sum_le_sum (by intro u hu; exact hpoint u)
  have hsplit :
      ∑ u : Fin (n + 1), ((f u).val : ℝ) * (threshold n - u.val - 1 + 1) =
        ∑ u : Fin (n + 1), ((f u).val : ℝ) * (threshold n - u.val - 1) + k := by
    calc
      ∑ u : Fin (n + 1), ((f u).val : ℝ) * (threshold n - u.val - 1 + 1)
          = ∑ u : Fin (n + 1),
              (((f u).val : ℝ) * (threshold n - u.val - 1) + ((f u).val : ℝ)) := by
                congr 1
                funext u
                ring
      _ = (∑ u : Fin (n + 1), ((f u).val : ℝ) * (threshold n - u.val - 1)) +
            ∑ u : Fin (n + 1), ((f u).val : ℝ) := by
              rw [Finset.sum_add_distrib]
      _ = (∑ u : Fin (n + 1), ((f u).val : ℝ) * (threshold n - u.val - 1)) + k := by
              have hsumk : (∑ u : Fin (n + 1), ((f u).val : ℝ)) = k := by
                simpa [profileColorCount] using
                  congrArg (fun m : ℕ => (m : ℝ))
                    (profileColorCount_eq_of_mem_coloringProfileFinset hf)
              rw [hsumk]
  calc
    ∑ u : Fin (n + 1), ((f u).val : ℝ) * (thresholdFloor n - u.val)
        ≤ ∑ u : Fin (n + 1), ((f u).val : ℝ) * (threshold n - u.val - 1 + 1) := hsum
    _ = ∑ u : Fin (n + 1), ((f u).val : ℝ) * (threshold n - u.val - 1) + k := hsplit
    _ ≤ (((2 / Real.log 2) - safeProfileUpperBoundBuffer) * k) + k := by gcongr
    _ = ((2 / Real.log 2) - 3) * k := by
          simp [safeProfileUpperBoundBuffer]
          ring

lemma safeWeightedShiftPlusThresholdFloorSum_le
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hn : 0 < n)
    (hf : f ∈ coloringProfileFinset n k t)
    (hth_nonneg : 0 ≤ threshold n)
    (hreg : SafeProfileUpperBoundRegime n f) :
    ∑ u : Fin (n + 1),
      ((f u).val : ℝ) *
        ((Real.log 2 / 2) * u.val * (threshold n - (1 + 2 / Real.log 2) - u.val) +
          (thresholdFloor n - u.val))
      ≤ -(2 * Real.log 2) * n + ((2 / Real.log 2) - 3) * k := by
  have hweighted :
      ∑ u : Fin (n + 1),
        (((u.val * (f u).val : ℕ) : ℝ) *
          (threshold n - (1 + 2 / Real.log 2) - u.val)) < -(safeProfileUpperBoundBuffer * n) :=
    profileUpperBoundRegime_weighted_sum_shift_lt_neg_n_of_safeUpperBoundRegime hn hf hreg
  have hfloor :
      ∑ u : Fin (n + 1), ((f u).val : ℝ) * (thresholdFloor n - u.val) ≤
        ((2 / Real.log 2) - 3) * k :=
    profileUpperBoundRegime_sum_thresholdFloor_minus_u_le_of_safeUpperBoundRegime
      hn hf hth_nonneg hreg
  have hsplit :
      ∑ u : Fin (n + 1),
        ((f u).val : ℝ) *
          ((Real.log 2 / 2) * u.val * (threshold n - (1 + 2 / Real.log 2) - u.val) +
            (thresholdFloor n - u.val))
      =
      (Real.log 2 / 2) *
        ∑ u : Fin (n + 1),
          (((u.val * (f u).val : ℕ) : ℝ) *
            (threshold n - (1 + 2 / Real.log 2) - u.val)) +
      ∑ u : Fin (n + 1), ((f u).val : ℝ) * (thresholdFloor n - u.val) := by
    calc
      ∑ u : Fin (n + 1),
        ((f u).val : ℝ) *
          ((Real.log 2 / 2) * u.val * (threshold n - (1 + 2 / Real.log 2) - u.val) +
            (thresholdFloor n - u.val))
          =
        ∑ u : Fin (n + 1),
          ((Real.log 2 / 2) *
              (((u.val * (f u).val : ℕ) : ℝ) *
                (threshold n - (1 + 2 / Real.log 2) - u.val)) +
            ((f u).val : ℝ) * (thresholdFloor n - u.val)) := by
              refine Finset.sum_congr rfl ?_
              intro u hu
              norm_num
              ring
      _ =
        (Real.log 2 / 2) *
          ∑ u : Fin (n + 1),
            (((u.val * (f u).val : ℕ) : ℝ) *
              (threshold n - (1 + 2 / Real.log 2) - u.val)) +
        ∑ u : Fin (n + 1), ((f u).val : ℝ) * (thresholdFloor n - u.val) := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hweighted' :
      (Real.log 2 / 2) *
          ∑ u : Fin (n + 1),
            (((u.val * (f u).val : ℕ) : ℝ) *
              (threshold n - (1 + 2 / Real.log 2) - u.val))
        ≤ -(2 * Real.log 2) * n := by
    have hpos : 0 < Real.log 2 / 2 := by positivity
    have hmul :
        (Real.log 2 / 2) *
            ∑ u : Fin (n + 1),
              (((u.val * (f u).val : ℕ) : ℝ) *
                (threshold n - (1 + 2 / Real.log 2) - u.val))
          <
        (Real.log 2 / 2) * (-(safeProfileUpperBoundBuffer * n)) := by
      exact mul_lt_mul_of_pos_left hweighted hpos
    have hsimp : (Real.log 2 / 2) * (-(safeProfileUpperBoundBuffer * n)) = -(2 * Real.log 2) * n := by
      simp [safeProfileUpperBoundBuffer]
      ring
    linarith
  rw [hsplit]
  linarith

lemma safePointwise_of_profileContribution_le_exp_phi_perturbed
    {δ : ℝ}
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hn : 0 < n)
    (hf : f ∈ coloringProfileFinset n k t)
    (hphiExp :
      profileContribution n f ≤ Real.exp ((profilePhi n f + δ) * n))
    (hδ :
      δ ≤ (Real.log 2 / 2) * safeProfileUpperBoundBuffer - safeProfileDecayRate)
    (hreg : SafeProfileUpperBoundRegime n f) :
    profileContribution n f ≤ Real.exp (-safeProfileDecayRate * n) := by
  have hphi :
      profilePhi n f < -(Real.log 2 / 2) * safeProfileUpperBoundBuffer :=
    profilePhi_lt_safe_neg_buffer_of_safeUpperBoundRegime hn hf hreg
  have hphi' : profilePhi n f + δ < -safeProfileDecayRate := by
    linarith
  have hnR : (0 : ℝ) ≤ n := by positivity
  have hmul : (profilePhi n f + δ) * n ≤ (-safeProfileDecayRate) * n := by
    nlinarith
  exact hphiExp.trans (Real.exp_le_exp.mpr hmul)

/-- Minimal cont2-style pointwise target: `profileContribution` is controlled by
`exp((profilePhi + δ) n)` for a fixed perturbation `δ`. This is the exact
shape suggested by the paper's `expectationlemma` transfer before using the
safe negative bound on `profilePhi`. -/
def ProfileContributionExpPhiPerturbedPointwise
    (δ : ℝ) (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) : Prop :=
  profileContribution n f ≤ Real.exp ((profilePhi n f + δ) * n)

lemma profileContributionExpPhiPerturbedPointwise_iff
    {δ : ℝ} {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)} :
    ProfileContributionExpPhiPerturbedPointwise δ n f ↔
      profileContribution n f ≤ Real.exp ((profilePhi n f + δ) * n) := by
  rfl

/-- Concrete perturbed-exponent target sufficient for the safe sharp route. -/
def SafeProfileContributionExpPhiPerturbedPointwise
    (δ : ℝ) (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) : Prop :=
  SafeProfileUpperBoundRegime n f →
    ProfileContributionExpPhiPerturbedPointwise δ n f

/-- The concrete live theorem target suggested directly by `cont2`: prove a
safe perturbed-exponent upper bound for one profile in the safe regime. -/
def SafeProfileContributionExpPhiPerturbedTheoremTarget
    (δ : ℝ) : Prop :=
  ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
    f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
    SafeProfileContributionExpPhiPerturbedPointwise δ n f

/-- First ingredient from the paper's `cont2`: a pointwise upper bound on
`profileContribution` with the explicit remainder term left unsimplified. -/
def SafeProfileContributionCont2Pointwise
    (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) : Prop :=
  SafeProfileUpperBoundRegime n f →
    profileContribution n f ≤ Real.exp (profilePhi n f * n + profileRemainder n f)

/-- Safe-regime version of the remaining pointwise core inequality needed for
`cont2`. This isolates the next sharp theorem target to a single comparison
for `profileCombinatorialLogCore`. -/
def SafeProfileCombinatorialCoreCont2BoundPointwise
    (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) : Prop :=
  SafeProfileUpperBoundRegime n f →
    ProfileCombinatorialCoreCont2BoundPointwise n f

/-- The live theorem target for the remaining `cont2` comparison: a safe
pointwise upper bound on the combinatorial log-core for every threshold-level
profile. -/
def SafeProfileCombinatorialCoreCont2BoundTheoremTarget : Prop :=
  ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
    f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
    SafeProfileCombinatorialCoreCont2BoundPointwise n f

lemma safeCont2Pointwise_of_safeCoreBound
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hpos : 0 < profileContribution n f)
    (hP : 0 < profileP n (fun u => (f u).val))
    (hcore : SafeProfileCombinatorialCoreCont2BoundPointwise n f) :
    SafeProfileContributionCont2Pointwise n f := by
  intro hreg
  exact cont2Pointwise_of_core_bound hpos hP (hcore hreg)

lemma safeCont2Pointwise_of_safeCoreBound_and_profileP_pos
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hP : 0 < profileP n (fun u => (f u).val))
    (hcore : SafeProfileCombinatorialCoreCont2BoundPointwise n f) :
    SafeProfileContributionCont2Pointwise n f := by
  exact safeCont2Pointwise_of_safeCoreBound
    (profileContribution_pos_of_profileP_pos n f hP) hP hcore

/-- Second ingredient needed after `cont2`: the remainder is at most `δ n`.
This is the part expected to come from support/tameness estimates on safe
profiles. -/
def SafeProfileRemainderLinearBoundPointwise
    (δ : ℝ) (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) : Prop :=
  SafeProfileUpperBoundRegime n f →
    profileRemainder n f ≤ δ * n

/-- The theorem-level remainder target used to finish the sharp safe route
once the `cont2` surface is already available. -/
def SafeProfileRemainderLinearBoundTheoremTarget
    (δ : ℝ) : Prop :=
  ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
    f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
    SafeProfileRemainderLinearBoundPointwise δ n f

/-- Concrete one-profile remainder target for the current safe route, with the
fixed budget `δ = 1`. -/
def SafeProfileConcreteRemainderPointwise
    (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) : Prop :=
  SafeProfileRemainderLinearBoundPointwise safeProfileRemainderBudget n f

/-- Concrete theorem-level remainder target for the current safe route, with
the fixed budget `δ = 1`. -/
def SafeProfileConcreteRemainderTheoremTarget : Prop :=
  SafeProfileRemainderLinearBoundTheoremTarget safeProfileRemainderBudget

/-- Conditional theorem-level concrete remainder target in the main working
range: the only remaining side conditions are `3 ≤ n` and `0 ≤ threshold n`. -/
def SafeProfileConcreteRemainderConditionalTheoremTarget : Prop :=
  ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
    f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
    3 ≤ n →
    0 ≤ threshold n →
    SafeProfileConcreteRemainderPointwise n f

lemma safeProfileConcreteRemainderPointwise_iff
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)} :
    SafeProfileConcreteRemainderPointwise n f ↔
      SafeProfileUpperBoundRegime n f →
        profileRemainder n f ≤ safeProfileRemainderBudget * n := by
  rfl

lemma safeProfileConcreteRemainderTheoremTarget_apply
    (h : SafeProfileConcreteRemainderTheoremTarget) :
    ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
      f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
      SafeProfileConcreteRemainderPointwise n f :=
  h

lemma safeProfileConcreteRemainderTheoremTarget_of_pointwise
    (h :
      ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
        f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
        SafeProfileConcreteRemainderPointwise n f) :
    SafeProfileConcreteRemainderTheoremTarget :=
  h

lemma safeProfileConcreteRemainderTheoremTarget_of_conditional
    (hcond : SafeProfileConcreteRemainderConditionalTheoremTarget)
    (hside :
      ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
        f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
        3 ≤ n ∧ 0 ≤ threshold n) :
    SafeProfileConcreteRemainderTheoremTarget := by
  intro n f hf
  exact hcond n f hf (hside n f hf).1 (hside n f hf).2

lemma safePhiPerturbed_of_cont2_and_remainder
    {δ : ℝ} {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hcont2 : SafeProfileContributionCont2Pointwise n f)
    (hR : SafeProfileRemainderLinearBoundPointwise δ n f) :
    SafeProfileContributionExpPhiPerturbedPointwise δ n f := by
  intro hreg
  have hbase := hcont2 hreg
  have hrem := hR hreg
  refine hbase.trans ?_
  apply Real.exp_le_exp.mpr
  linarith

lemma safePhiPerturbedTheoremTarget_of_cont2_and_remainder
    {δ : ℝ}
    (hcont2 :
      ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
        f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
        SafeProfileContributionCont2Pointwise n f)
    (hR :
      ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
        f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
        SafeProfileRemainderLinearBoundPointwise δ n f) :
    SafeProfileContributionExpPhiPerturbedTheoremTarget δ := by
  intro n f hf
  exact safePhiPerturbed_of_cont2_and_remainder (hcont2 n f hf) (hR n f hf)

lemma safePointwise_of_safePhiPerturbed
    {δ : ℝ}
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hn : 0 < n)
    (hf : f ∈ coloringProfileFinset n k t)
    (hδ :
      δ ≤ (Real.log 2 / 2) * safeProfileUpperBoundBuffer - safeProfileDecayRate)
    (hpert : SafeProfileContributionExpPhiPerturbedPointwise δ n f)
    (hreg : SafeProfileUpperBoundRegime n f) :
    profileContribution n f ≤ Real.exp (-safeProfileDecayRate * n) := by
  exact safePointwise_of_profileContribution_le_exp_phi_perturbed
    hn hf (hpert hreg) hδ hreg

lemma safeExpDecayPointwise_of_safePhiPerturbedTheoremTarget
    {δ : ℝ}
    (hδ :
      δ ≤ (Real.log 2 / 2) * safeProfileUpperBoundBuffer - safeProfileDecayRate)
    (hpert : SafeProfileContributionExpPhiPerturbedTheoremTarget δ) :
    ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
      f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
      SafeProfileUpperBoundRegime n f →
      profileContribution n f ≤ Real.exp (-safeProfileDecayRate * n) := by
  intro n f hf hreg
  by_cases hn : 0 < n
  · exact safePointwise_of_safePhiPerturbed hn hf hδ (hpert n f hf) hreg
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst hn0
    have hfun : f = fun _ => (0 : Fin 1) := by
      funext u
      fin_cases u
      apply Fin.ext
      omega
    subst hfun
    simp [profileContribution, profileP, profileF, profileSymm, safeProfileDecayRate]

/-- Concrete one-profile decay target used for the first sharp transfer from
the paper. -/
def SafeProfileContributionExpDecayTarget
    (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) : Prop :=
  ProfileContributionExpDecayTarget safeProfileUpperBoundBuffer safeProfileDecayRate n f

/-- Concrete one-profile sharp upper-bound statement in its most directly usable
form for the next transfer from `lemmaupperbound`. -/
def SafeProfileContributionExpDecayPointwise
    (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) : Prop :=
  SafeProfileUpperBoundRegime n f →
    profileContribution n f ≤ Real.exp (-safeProfileDecayRate * n)

/-- The first concrete live theorem target for the sharp route: prove the
paper's upper-bound transfer for one profile in the safe regime. -/
def SafeProfileContributionExpDecayTheoremTarget : Prop :=
  ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
    f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
    SafeProfileContributionExpDecayPointwise n f

lemma safeExpDecay_of_safePhiPerturbedTheoremTarget
    {δ : ℝ}
    (hδ :
      δ ≤ (Real.log 2 / 2) * safeProfileUpperBoundBuffer - safeProfileDecayRate)
    (hpert : SafeProfileContributionExpPhiPerturbedTheoremTarget δ) :
    SafeProfileContributionExpDecayTheoremTarget :=
  safeExpDecayPointwise_of_safePhiPerturbedTheoremTarget hδ hpert

lemma safeProfileContributionExpDecayTarget_iff
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)} :
    SafeProfileContributionExpDecayTarget n f ↔
      SafeProfileContributionExpDecayPointwise n f := by
  rfl

lemma profileContribution_le_safe_expDecay_of_safeTarget
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (htarget : SafeProfileContributionExpDecayTarget n f)
    (hreg : SafeProfileUpperBoundRegime n f) :
    profileContribution n f ≤ Real.exp (-safeProfileDecayRate * n) :=
  htarget hreg

lemma safeProfileContributionExpDecayPointwise_iff
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)} :
    SafeProfileContributionExpDecayPointwise n f ↔
      SafeProfileUpperBoundRegime n f →
        profileContribution n f ≤ Real.exp (-safeProfileDecayRate * n) := by
  rfl

lemma safeTarget_of_pointwise
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (h : SafeProfileContributionExpDecayPointwise n f) :
    SafeProfileContributionExpDecayTarget n f :=
  h

lemma eventualSafeProfileContributionExpDecay_of_theoremTarget
    (h : SafeProfileContributionExpDecayTheoremTarget) :
    EventualSafeProfileContributionExpDecay := by
  refine ⟨0, ?_⟩
  intro n _ f hf
  exact safeTarget_of_pointwise (h n f hf)

lemma eventualSafeProfileContributionExpDecay_gives_safeTarget
    (h : EventualSafeProfileContributionExpDecay) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ f : Fin (n + 1) → Fin (n + 1),
        f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
        SafeProfileContributionExpDecayTarget n f := by
  rcases h with ⟨n₀, hn₀⟩
  refine ⟨n₀, ?_⟩
  intro n hn f hf
  exact hn₀ n hn f hf

lemma eventualSafeProfileContributionExpDecay_gives_safePointwise
    (h : EventualSafeProfileContributionExpDecay) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ f : Fin (n + 1) → Fin (n + 1),
        f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
        SafeProfileContributionExpDecayPointwise n f := by
  rcases eventualSafeProfileContributionExpDecay_gives_safeTarget h with ⟨n₀, hn₀⟩
  refine ⟨n₀, ?_⟩
  intro n hn f hf
  exact safeProfileContributionExpDecayTarget_iff.mp (hn₀ n hn f hf)

lemma profileContribution_le_safe_expDecay_of_eventualSafe
    (h : EventualSafeProfileContributionExpDecay) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ f : Fin (n + 1) → Fin (n + 1),
        f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
        SafeProfileUpperBoundRegime n f →
        profileContribution n f ≤ Real.exp (-safeProfileDecayRate * n) := by
  rcases eventualSafeProfileContributionExpDecay_gives_safeTarget h with ⟨n₀, hn₀⟩
  refine ⟨n₀, ?_⟩
  intro n hn f hf hreg
  exact profileContribution_le_safe_expDecay_of_safeTarget (hn₀ n hn f hf) hreg

lemma eventualSafeProfileContributionExpDecay_iff :
    EventualSafeProfileContributionExpDecay ↔
      EventualProfileContributionExpDecay safeProfileUpperBoundBuffer safeProfileDecayRate := by
  rfl

lemma eventualSafeProfileContributionExpDecay_apply
    (h : EventualSafeProfileContributionExpDecay) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ f : Fin (n + 1) → Fin (n + 1),
        f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
        ProfileContributionExpDecayTarget safeProfileUpperBoundBuffer safeProfileDecayRate n f :=
  h

lemma profileContribution_le_safe_expDecay_of_eventual
    (h : EventualSafeProfileContributionExpDecay) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ f : Fin (n + 1) → Fin (n + 1),
        f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
        ProfileUpperBoundRegime safeProfileUpperBoundBuffer n f →
        profileContribution n f ≤ Real.exp (-safeProfileDecayRate * n) := by
  rcases h with ⟨n₀, hn₀⟩
  refine ⟨n₀, ?_⟩
  intro n hn f hfmem hreg
  exact profileContribution_le_expDecay_of_target (hn₀ n hn f hfmem) hreg

/-- For k = n (each class has size 1, profile f_1 = n):
    E_{n,n,t} = n^n / n! ≥ 1 for n ≥ 1. -/
-- The zero profile: all counts = 0.
private def zeroProfile (n : ℕ) : Fin (n + 1) → Fin (n + 1) := fun _ => ⟨0, Nat.zero_lt_succ _⟩

-- The singletons profile: f(1) = n, f(u) = 0 for u ≠ 1.
private def singletonsProfile (n : ℕ) : Fin (n + 1) → Fin (n + 1) :=
  fun u => if u.val = 1 then ⟨n, Nat.lt_succ_self _⟩ else ⟨0, Nat.zero_lt_succ _⟩

-- The zero profile is in coloringProfileFinset 0 0 t.
private lemma zeroProfile_mem_finset (t : ℕ) :
    zeroProfile 0 ∈ coloringProfileFinset 0 0 t := by
  unfold zeroProfile coloringProfileFinset
  simp

-- The singletons profile is in coloringProfileFinset n n t for n ≥ 1 and t ≥ 1.
private lemma singletonsProfile_mem_finset (n t : ℕ) (hn : 0 < n) (ht : 0 < t) :
    singletonsProfile n ∈ coloringProfileFinset n n t := by
  unfold singletonsProfile coloringProfileFinset
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  -- Rewrite the coerced if-then-else to a natural number if-then-else
  have key : ∀ u : Fin (n + 1),
      ((if u.val = 1 then (⟨n, Nat.lt_succ_self _⟩ : Fin (n+1)) else ⟨0, Nat.zero_lt_succ _⟩) : Fin (n+1)).val =
      if u.val = 1 then n else 0 := fun u => by split_ifs <;> rfl
  simp_rw [key]
  have h1 : (⟨1, Nat.lt_succ_of_le (Nat.one_le_iff_ne_zero.mpr hn.ne')⟩ : Fin (n+1)) ∈ (Finset.univ : Finset (Fin (n+1))) :=
    Finset.mem_univ _
  refine ⟨?_, ?_, ?_⟩
  · -- ∑ u, u.val * (if u.val = 1 then n else 0) = n
    rw [Finset.sum_eq_single (⟨1, Nat.lt_succ_of_le (Nat.one_le_iff_ne_zero.mpr hn.ne')⟩ : Fin (n+1))]
    · simp
    · intro u _ hu; simp [show u.val ≠ 1 from fun h => hu (Fin.ext h)]
    · intro h; exact absurd (Finset.mem_univ _) h
  · -- ∑ u, (if u.val = 1 then n else 0) = n
    rw [Finset.sum_eq_single (⟨1, Nat.lt_succ_of_le (Nat.one_le_iff_ne_zero.mpr hn.ne')⟩ : Fin (n+1))]
    · simp
    · intro u _ hu; simp [show u.val ≠ 1 from fun h => hu (Fin.ext h)]
    · intro h; exact absurd (Finset.mem_univ _) h
  · -- ∀ u, t < u.val → (if u.val = 1 then n else 0) = 0
    intro u hu
    have hne : u.val ≠ 1 := by omega
    simp [hne]

-- The contribution of the zero profile to E_{0,0,t} is 1.
private lemma zeroProfile_contribution (t : ℕ) :
    let f := zeroProfile 0
    let fu : Fin 1 → ℕ := fun u => (f u).val
    (profileP 0 (fun u => (f u).val) : ℝ) * (1 / 2 : ℝ) ^ profileF 0 (fun u => (f u).val) /
      (profileSymm 0 (fun u => (f u).val) : ℝ) = 1 := by
  simp [profileP, profileF, profileSymm, zeroProfile, Nat.factorial]

-- The contribution of the singletons profile to E_{n,n,t} is 1.
private lemma singletonsProfile_contribution (n : ℕ) (hn : 0 < n) :
    let fu : Fin (n + 1) → ℕ := fun u => (singletonsProfile n u).val
    (profileP n fu : ℝ) * (1 / 2 : ℝ) ^ profileF n fu / (profileSymm n fu : ℝ) = 1 := by
  simp only [singletonsProfile, profileP, profileF, profileSymm]
  -- Rewrite coerced if-then-else to natural number if-then-else
  have key : ∀ u : Fin (n + 1),
      ((if u.val = 1 then (⟨n, Nat.lt_succ_self _⟩ : Fin (n+1)) else ⟨0, Nat.zero_lt_succ _⟩) : Fin (n+1)).val =
      if u.val = 1 then n else 0 := fun u => by split_ifs <;> rfl
  simp_rw [key]
  -- profileF: ∑ u, C(u,2) * (if u=1 then n else 0) = C(1,2)*n = 0
  have hF : ∑ u : Fin (n + 1), Nat.choose u.val 2 * (if u.val = 1 then n else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro u _
    rcases eq_or_ne u.val 1 with h | h <;> simp [h]
  -- ∏ u, (u!)^(if u=1 then n else 0) = (1!)^n = 1
  have hP_den : ∏ u : Fin (n + 1), (Nat.factorial u.val) ^ (if u.val = 1 then n else 0) = 1 := by
    apply Finset.prod_eq_one
    intro u _
    rcases eq_or_ne u.val 1 with h | h <;> simp [h]
  -- profileSymm: ∏ u, (if u=1 then n else 0)! = n!
  have hS : ∏ u : Fin (n + 1), Nat.factorial (if u.val = 1 then n else 0) = Nat.factorial n := by
    have h1 : (⟨1, Nat.lt_succ_of_le (Nat.one_le_iff_ne_zero.mpr hn.ne')⟩ : Fin (n+1)) ∈ Finset.univ :=
      Finset.mem_univ _
    rw [← Finset.mul_prod_erase _ _ h1]
    simp only [if_true]
    conv_rhs => rw [← mul_one (Nat.factorial n)]
    congr 1
    apply Finset.prod_eq_one
    intro u hu
    simp only [Finset.mem_erase] at hu
    simp [show u.val ≠ 1 from fun h => hu.1 (Fin.ext h)]
  rw [hF, hP_den, hS, Nat.div_one, pow_zero, mul_one]
  exact div_self (by exact_mod_cast (Nat.factorial_pos n).ne')

lemma fmtExists (n t : ℕ) (ht : 0 < t) : ∃ k, (1 : ℝ) ≤ expectedTBoundedColorings n k t := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- n = 0: use k = 0. The zero profile contributes 1.
    refine ⟨0, ?_⟩
    have hmem := zeroProfile_mem_finset t
    have hpos : ∀ f ∈ coloringProfileFinset 0 0 t,
        (0 : ℝ) ≤ let fu : Fin 1 → ℕ := fun u => (f u).val
          (profileP 0 fu : ℝ) * (1 / 2 : ℝ) ^ profileF 0 fu / (profileSymm 0 fu : ℝ) := by
      intro f _
      apply div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)) (Nat.cast_nonneg _)
    calc (1 : ℝ) = let fu : Fin 1 → ℕ := fun u => (zeroProfile 0 u).val
            (profileP 0 fu : ℝ) * (1 / 2 : ℝ) ^ profileF 0 fu / (profileSymm 0 fu : ℝ) := by
            simp only []
            exact (zeroProfile_contribution t).symm
      _ ≤ expectedTBoundedColorings 0 0 t := by
            simp only [expectedTBoundedColorings]
            exact Finset.single_le_sum hpos hmem
  · -- n > 0, t > 0: singletons profile has contribution 1.
    refine ⟨n, ?_⟩
    have hmem := singletonsProfile_mem_finset n t hn ht
    have hpos : ∀ f ∈ coloringProfileFinset n n t,
        (0 : ℝ) ≤ let fu : Fin (n + 1) → ℕ := fun u => (f u).val
          (profileP n fu : ℝ) * (1 / 2 : ℝ) ^ profileF n fu / (profileSymm n fu : ℝ) := by
      intro f _
      apply div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)) (Nat.cast_nonneg _)
    calc (1 : ℝ) = let fu : Fin (n + 1) → ℕ := fun u => (singletonsProfile n u).val
            (profileP n fu : ℝ) * (1 / 2 : ℝ) ^ profileF n fu / (profileSymm n fu : ℝ) := by
            simp only []
            exact (singletonsProfile_contribution n hn).symm
      _ ≤ expectedTBoundedColorings n n t := by
            simp only [expectedTBoundedColorings]
            exact Finset.single_le_sum hpos hmem

end ExpectedColorings

/-! ## The first moment threshold -/

section Threshold

/-- k_t(n): the t-bounded first moment threshold.
  `k_t(n) := min { k : E_{n,k,t} ≥ 1 }` (Definition ktdef in [heckel2023colouring]).
  Requires `0 < t` (the t-bound must be at least 1, i.e. singletons are allowed).
-/
noncomputable def firstMomentThreshold (n t : ℕ) (ht : 0 < t) : ℕ :=
  Nat.find (fmtExists n t ht)

/-- By definition of firstMomentThreshold: E_{n, k_t, t} ≥ 1. -/
theorem firstMomentThreshold_ge_one (n t : ℕ) (ht : 0 < t) :
    (1 : ℝ) ≤ expectedTBoundedColorings n (firstMomentThreshold n t ht) t :=
  Nat.find_spec (fmtExists n t ht)

/-- The first-moment threshold is always at most `n`. -/
theorem firstMomentThreshold_le_n (n t : ℕ) (ht : 0 < t) :
    firstMomentThreshold n t ht ≤ n := by
  apply Nat.find_min'
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [expectedTBoundedColorings]
    have hmem := zeroProfile_mem_finset t
    have hpos : ∀ f ∈ coloringProfileFinset 0 0 t,
        (0 : ℝ) ≤ let fu : Fin 1 → ℕ := fun u => (f u).val
          (profileP 0 fu : ℝ) * (1 / 2 : ℝ) ^ profileF 0 fu / (profileSymm 0 fu : ℝ) :=
      fun f _ => div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)) (Nat.cast_nonneg _)
    linarith [zeroProfile_contribution t,
      Finset.single_le_sum hpos hmem]
  · have hmem := singletonsProfile_mem_finset n t hn ht
    have hpos : ∀ f ∈ coloringProfileFinset n n t,
        (0 : ℝ) ≤ let fu : Fin (n + 1) → ℕ := fun u => (f u).val
          (profileP n fu : ℝ) * (1 / 2 : ℝ) ^ profileF n fu / (profileSymm n fu : ℝ) :=
      fun f _ => div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)) (Nat.cast_nonneg _)
    simp only [expectedTBoundedColorings]
    linarith [singletonsProfile_contribution n hn,
      Finset.single_le_sum hpos hmem]

/-- Below the threshold: E_{n, k_t − 1, t} < 1.
  This is the KEY property behind Lemma 8.1:
  by the first moment method, ℙ[χ_t(G) < k_t − 1] ≤ E_{n, k_t−1, t} < 1.

  **Source**: [heckel2023colouring], proof of Lemma 8.1 (line 2586):
  "by the definition of the first moment threshold, E_{n, k_a−1, a} < 1".
-/
theorem below_threshold_lt_one (n t : ℕ) (ht : 0 < t) (h : 0 < firstMomentThreshold n t ht) :
    expectedTBoundedColorings n (firstMomentThreshold n t ht - 1) t < 1 := by
  have hm : firstMomentThreshold n t ht - 1 < firstMomentThreshold n t ht := Nat.sub_lt h one_pos
  have := Nat.find_min (fmtExists n t ht) hm
  push_neg at this
  linarith

end Threshold

/-! ## First moment lower bound on χ_t (Lemma 8.1 of [heckel2023colouring]) -/

section LowerBound

open ENNReal Classical

/-!
### Count of t-bounded k-colorings of a concrete graph

`tBoundedColoringCount n k t G` counts the number of maps `π : Fin n → Fin k` that give
t-bounded proper colorings of G. This is the counting random variable X_{k,t} in Lemma 8.1.

The connection to the first moment method:
  ℙ[χ_t(G) ≤ k] = ℙ[X_{k,t}(G) ≥ 1] ≤ E[X_{k,t}]
by the union bound / Markov's inequality.
-/

/-- Count of t-bounded k-colorings of G.
  Uses classical decidability to form the filter. -/
noncomputable def tBoundedColoringCount (n k t : ℕ) (G : SimpleGraph (Fin n)) : ℕ :=
  letI : DecidablePred (fun π : Fin n → Fin k => IsTBoundedProperColoring G k t π) :=
    fun _ => Classical.propDecidable _
  (Finset.univ (α := Fin n → Fin k)).filter
    (fun π => IsTBoundedProperColoring G k t π) |>.card

/-- The event {χ_t(G) ≤ k} is equivalent to {tBoundedColoringCount G n k t ≥ 1}. -/
lemma tBoundedColoringCount_pos_iff (n k t : ℕ) (G : SimpleGraph (Fin n)) :
    TBoundedProperColoringExists G k t ↔ 0 < tBoundedColoringCount n k t G := by
  unfold TBoundedProperColoringExists tBoundedColoringCount
  letI : DecidablePred (fun π : Fin n → Fin k => IsTBoundedProperColoring G k t π) :=
    fun _ => Classical.propDecidable _
  rw [Finset.card_pos]
  constructor
  · rintro ⟨π, hπ⟩
    exact ⟨π, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hπ⟩⟩
  · rintro ⟨π, hπ⟩
    exact ⟨π, (Finset.mem_filter.mp hπ).2⟩

/-! ### Decomposition of tBoundedColoringCount as a sum of indicators

The counting variable decomposes as:
  tBoundedColoringCount n k t G = ∑_{π : Fin n → Fin k} [π is valid for G]
This allows linearity of expectation: E[X] = ∑_π ℙ[π valid].
-/

/-- Decompose coloringCount as a finite sum of 0/1 indicators over all colorings. -/
lemma tBoundedColoringCount_eq_sum (n k t : ℕ) (G : SimpleGraph (Fin n)) :
    (tBoundedColoringCount n k t G : ℝ≥0∞) =
      ∑ π : Fin n → Fin k,
        if IsTBoundedProperColoring G k t π then 1 else 0 := by
  simp only [tBoundedColoringCount]
  letI hDec : DecidablePred (fun π : Fin n → Fin k => IsTBoundedProperColoring G k t π) :=
    fun _ => Classical.propDecidable _
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  push_cast
  rfl

/-! ### Edge probability theorems via binomialRandom -/

/-- The marginal at edge coordinate e under G(n,1/2) evaluates `{False}` to 1/2.
    The measure on each edge coordinate is `(1/2) • dirac True + (1/2) • dirac False`.
    When the edge is absent, we get the `{False}` atom with weight `toNNReal (σ halfProb)`.  -/
private lemma edgeMarginal_false (e : Sym2 (Fin n)) (he : ¬ e.IsDiag) :
    (unitInterval.toNNReal halfProb • Measure.dirac (¬ e.IsDiag) +
        unitInterval.toNNReal (unitInterval.symm halfProb) • Measure.dirac False) {False} =
    1 / 2 := by
  have h1 : (Measure.dirac (¬ e.IsDiag) : Measure Prop) {False} = 0 := by simp [he]
  have h2 : (Measure.dirac False : Measure Prop) {False} = 1 := by simp
  have hsym : unitInterval.symm halfProb = halfProb := by
    apply Subtype.ext; simp [halfProb, unitInterval.symm]; ring
  have hval : unitInterval.toNNReal halfProb = (2 : NNReal)⁻¹ := by
    simp [unitInterval.toNNReal, halfProb]; ext; norm_num
  simp only [Measure.add_apply, Measure.smul_apply]
  rw [h1, h2, hsym, hval]
  simp only [smul_zero, zero_add]
  rw [ENNReal.smul_def, smul_eq_mul, mul_one]
  simp [ENNReal.coe_inv]

-- Helper definition: marginal measures for infinitePi
private noncomputable def marginalMeasure (n : ℕ) : Sym2 (Fin n) → Measure Prop :=
  fun e => unitInterval.toNNReal halfProb • Measure.dirac (¬ e.IsDiag) +
            unitInterval.toNNReal (unitInterval.symm halfProb) • Measure.dirac False

private instance marginalMeasure_prob (n : ℕ) (i : Sym2 (Fin n)) :
    IsProbabilityMeasure (marginalMeasure n i) := by
  constructor
  unfold marginalMeasure
  simp only [Measure.add_apply, Measure.smul_apply]
  rw [Measure.dirac_apply_of_mem (Set.mem_univ _), Measure.dirac_apply_of_mem (Set.mem_univ _)]
  simp only [ENNReal.smul_def]
  have hone : (unitInterval.toNNReal halfProb : ℝ≥0∞) +
      unitInterval.toNNReal (unitInterval.symm halfProb) = 1 := by
    have := show unitInterval.toNNReal halfProb +
        unitInterval.toNNReal (unitInterval.symm halfProb) = (1 : NNReal) from by
      simp [unitInterval.toNNReal, unitInterval.symm, halfProb]; ext; norm_num
    exact_mod_cast this
  simp only [smul_eq_mul, mul_one]
  exact hone

private lemma marginalMeasure_nonDiag_false (n : ℕ) (e : Sym2 (Fin n)) (he : ¬ e.IsDiag) :
    marginalMeasure n e {False} = 1 / 2 := by
  unfold marginalMeasure
  have h1 : (Measure.dirac (¬ e.IsDiag) : Measure Prop) {False} = 0 := by simp [he]
  have h2 : (Measure.dirac False : Measure Prop) {False} = 1 := by simp
  have hsym : unitInterval.symm halfProb = halfProb := by
    apply Subtype.ext; simp [halfProb, unitInterval.symm]; ring
  have hval : unitInterval.toNNReal halfProb = (2 : NNReal)⁻¹ := by
    simp [unitInterval.toNNReal, halfProb]; ext; norm_num
  simp only [Measure.add_apply, Measure.smul_apply]
  rw [h1, h2, hsym, hval]
  simp only [smul_zero, zero_add]
  rw [ENNReal.smul_def, smul_eq_mul, mul_one]
  simp [ENNReal.coe_inv]

private lemma marginalMeasure_diag_true (n : ℕ) (e : Sym2 (Fin n)) (he : e.IsDiag) :
    marginalMeasure n e {True} = 0 := by
  unfold marginalMeasure
  have hmem : (¬ e.IsDiag) = False := propext ⟨absurd he, False.elim⟩
  conv_lhs => rw [show (Measure.dirac (¬ e.IsDiag) : Measure Prop) = Measure.dirac False
    from by simp [hmem]]
  have hone : unitInterval.toNNReal halfProb +
      unitInterval.toNNReal (unitInterval.symm halfProb) = 1 := by
    simp [unitInterval.toNNReal, unitInterval.symm, halfProb]; ext; norm_num
  rw [show unitInterval.toNNReal halfProb • (Measure.dirac False : Measure Prop) +
      unitInterval.toNNReal (unitInterval.symm halfProb) • Measure.dirac False =
      (unitInterval.toNNReal halfProb + unitInterval.toNNReal (unitInterval.symm halfProb)) •
        Measure.dirac False from (add_smul _ _ _).symm, hone]
  simp

private lemma infinitePi_diag_null (n : ℕ) (e : Sym2 (Fin n)) (he : e.IsDiag) :
    Measure.infinitePi (marginalMeasure n) {χ : Sym2 (Fin n) → Prop | χ e} = 0 := by
  have heq : {χ : Sym2 (Fin n) → Prop | χ e} =
      Set.pi (↑({e} : Finset (Sym2 (Fin n))) : Set _) (fun _ => ({True} : Set Prop)) := by
    ext χ; simp [Set.mem_pi]
  trans ∏ i ∈ ({e} : Finset (Sym2 (Fin n))), marginalMeasure n i {True}
  · rw [heq]
    exact Measure.infinitePi_pi (μ := marginalMeasure n)
      (fun i _ => measurableSet_singleton True)
  · simp only [Finset.prod_singleton]
    exact marginalMeasure_diag_true n e he

private lemma infinitePi_anyDiag_null (n : ℕ) :
    Measure.infinitePi (marginalMeasure n)
      {χ : Sym2 (Fin n) → Prop | ∃ e : Sym2 (Fin n), e.IsDiag ∧ χ e} = 0 := by
  have heq : {χ : Sym2 (Fin n) → Prop | ∃ e : Sym2 (Fin n), e.IsDiag ∧ χ e} =
      ⋃ e ∈ (Finset.univ : Finset (Sym2 (Fin n))).filter Sym2.IsDiag,
        {χ : Sym2 (Fin n) → Prop | χ e} := by
    ext χ; simp [Finset.mem_filter]
  rw [heq]
  apply measure_biUnion_null_iff (Finset.finite_toSet _).countable |>.mpr
  intro e he
  rw [Finset.mem_coe, Finset.mem_filter] at he
  exact infinitePi_diag_null n e he.2

/-- **[THEOREM — independence of edges under G(n,1/2)]**

  P[∀ e ∈ S, ¬G.Adj e.out.1 e.out.2] = (1/2)^|S|

  Proof route:
  1. `binomialRandom_apply'`: G(V,p) T = setBer(Sym2.diagSetᶜ, p) (edgeSet '' T)
  2. `setBernoulli_apply'`: setBer(u,p) S = infinitePi μ ({χ | {e | χ e}} ⁻¹' S)
  3. Show the preimage = Set.pi ↑S (fun _ => {False}) via `mem_edgeSet` + `Sym2.out_eq`
  4. `infinitePi_pi`: infinitePi μ (Set.pi ↑S f) = ∏ e ∈ S, μ e (f e)
  5. Each marginal {False} = 1/2 by `edgeMarginal_false`
  6. ∏ e ∈ S, (1/2) = (1/2)^S.card by `Finset.prod_const`
-/
theorem gnHalf_no_edges_prob (n : ℕ) (S : Finset (Sym2 (Fin n)))
    (hS : ∀ e ∈ S, ¬ e.IsDiag) :
    gnHalf n {G : SimpleGraph (Fin n) | ∀ e ∈ S, ¬ G.Adj e.out.1 e.out.2} =
      (1 / 2 : ℝ≥0∞) ^ S.card := by
  rw [gnHalf, SimpleGraph.binomialRandom_apply halfProb]
  set T := {G : SimpleGraph (Fin n) | ∀ e ∈ S, ¬G.Adj e.out.1 e.out.2}
  -- Step 1: Set.pi ↑S {False} has measure (1/2)^S.card
  have hpi : Measure.infinitePi (marginalMeasure n) (Set.pi ↑S (fun _ => ({False} : Set Prop))) =
      (1 / 2 : ℝ≥0∞) ^ S.card := by
    trans ∏ e ∈ S, marginalMeasure n e {False}
    · exact Measure.infinitePi_pi (μ := marginalMeasure n)
        (fun i _ => measurableSet_singleton False)
    · rw [Finset.prod_congr rfl (fun e he => marginalMeasure_nonDiag_false n e (hS e he))]
      simp [Finset.prod_const]
  rw [← hpi]
  -- Step 2: The image set and the pi set are a.e. equal
  apply measure_congr
  rw [ae_eq_set]
  refine ⟨?_, ?_⟩
  · -- image T \ Set.pi ↑S {False} = ∅
    suffices h : (fun G : SimpleGraph (Fin n) => (· ∈ G.edgeSet)) '' T \
        Set.pi ↑S (fun _ => ({False} : Set Prop)) = ∅ by rw [h]; exact measure_empty
    rw [Set.diff_eq_empty]
    intro χ ⟨G, hG, hχ⟩ e he
    subst hχ
    simp only [Set.mem_pi, Set.mem_singleton_iff]
    apply eq_false_intro
    intro hmem
    rw [show e = s(e.out.1, e.out.2) from (Quot.out_eq e).symm] at hmem
    exact hG e (Finset.mem_coe.mp he) ((SimpleGraph.mem_edgeSet (G := G)).mp hmem)
  · -- pi \ image T ⊆ {χ | ∃ e.IsDiag, χ e} → measure 0
    apply measure_mono_null _ (infinitePi_anyDiag_null n)
    intro χ hχ
    simp only [Set.mem_diff, Set.mem_pi, Set.mem_singleton_iff, Set.mem_image,
               Set.mem_setOf_eq] at hχ ⊢
    by_contra hall
    push_neg at hall
    let G := SimpleGraph.fromEdgeSet {e : Sym2 (Fin n) | χ e}
    have hG_inT : G ∈ T := by
      intro e he
      rw [SimpleGraph.fromEdgeSet_adj]
      push_neg
      intro hχe
      simp only [Set.mem_setOf_eq] at hχe
      have heq : s(e.out.1, e.out.2) = e := Quot.out_eq e
      have hχe' : χ e := heq ▸ hχe
      exact absurd hχe' (by rw [hχ.1 e he]; exact id)
    apply hχ.2
    refine ⟨G, hG_inT, funext fun e => propext ?_⟩
    simp only [G, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_diff, Set.mem_setOf_eq,
               Sym2.mem_diagSet]
    exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, fun hdiag => hall e hdiag h⟩⟩

/-- **[THEOREM — marginal probability of a single edge under G(n,1/2)]**
    Corollary of `gnHalf_no_edges_prob`. -/
theorem gnHalf_adj_prob (n : ℕ) (u v : Fin n) (huv : u ≠ v) :
    gnHalf n {G : SimpleGraph (Fin n) | G.Adj u v} = 1 / 2 := by
  have hnd : ¬ (s(u, v) : Sym2 (Fin n)).IsDiag := Sym2.mk_isDiag_iff.not.mpr huv
  -- The "no-edge" event for S = {s(u,v)}
  have h := gnHalf_no_edges_prob n {s(u, v)} (by simpa)
  simp only [Finset.card_singleton, pow_one] at h
  -- Key: G.Adj (s(u,v)).out.1 (s(u,v)).out.2 ↔ G.Adj u v
  have hout_eq : s((s(u, v) : Sym2 (Fin n)).out.1, (s(u, v) : Sym2 (Fin n)).out.2) =
      s(u, v) := Quot.out_eq _
  have hadj_iff : ∀ G : SimpleGraph (Fin n),
      G.Adj (s(u, v) : Sym2 (Fin n)).out.1 (s(u, v) : Sym2 (Fin n)).out.2 ↔ G.Adj u v := by
    intro G
    rw [← SimpleGraph.mem_edgeSet, ← SimpleGraph.mem_edgeSet, hout_eq]
  -- Rewrite h to be about ¬G.Adj u v
  have h' : gnHalf n {G : SimpleGraph (Fin n) | ¬G.Adj u v} = 1 / 2 := by
    convert h using 2
    ext G
    simp only [Set.mem_setOf_eq, Finset.mem_singleton, forall_eq]
    exact (hadj_iff G).not.symm
  -- Measurability of the adj set via measurability of G ↦ G.Adj u v
  have hmeas_adj : Measurable (fun G : SimpleGraph (Fin n) => G.Adj u v) :=
    SimpleGraph.measurable_iff_adj.mp measurable_id u v
  have hmeas : MeasurableSet {G : SimpleGraph (Fin n) | G.Adj u v} :=
    hmeas_adj (measurableSet_singleton True) |>.congr (by ext G; simp [eq_true])
  -- Use measure_add_compl: μ(A) + μ(Aᶜ) = 1
  haveI : IsProbabilityMeasure (gnHalf n) := by unfold gnHalf; infer_instance
  have hcompl_eq : {G : SimpleGraph (Fin n) | ¬G.Adj u v} =
      {G : SimpleGraph (Fin n) | G.Adj u v}ᶜ := by ext G; simp
  rw [hcompl_eq] at h'
  have hfull := @measure_add_measure_compl _ _ (gnHalf n) _ hmeas
  -- hfull : gnHalf {Adj} + gnHalf {¬Adj} = gnHalf univ = 1
  simp only [measure_univ] at hfull
  rw [h'] at hfull
  -- hfull : gnHalf {Adj} + 1/2 = 1
  -- Solve: gnHalf {Adj} = 1/2
  have hle : gnHalf n {G : SimpleGraph (Fin n) | G.Adj u v} ≠ ⊤ :=
    ne_top_of_le_ne_top one_ne_top prob_le_one
  -- From a + 1/2 = 1 and a ≠ ⊤, deduce a = 1/2
  have : gnHalf n {G : SimpleGraph (Fin n) | G.Adj u v} = 1 - 1/2 := by
    have heq : gnHalf n {G : SimpleGraph (Fin n) | G.Adj u v} + 1/2 - 1/2 =
        1 - 1/2 := by rw [hfull]
    rwa [ENNReal.add_sub_cancel_right (by norm_num)] at heq
  simp only [this]; norm_num

/-- Monochromatic edges of a coloring π: non-diagonal Sym2 edges with same color. -/
noncomputable def monoEdgesFinset (n k : ℕ) (π : Fin n → Fin k) : Finset (Sym2 (Fin n)) :=
  (Finset.univ (α := Sym2 (Fin n))).filter (fun e => ¬e.IsDiag ∧ π e.out.1 = π e.out.2)

/-- The probability that G(n,1/2) has no monochromatic edges for coloring π. -/
lemma gnHalf_no_monoEdges_prob (n k : ℕ) (π : Fin n → Fin k) :
    gnHalf n {G : SimpleGraph (Fin n) | IsProperColoring G k π} =
    (1 / 2 : ℝ≥0∞) ^ (monoEdgesFinset n k π).card := by
  -- Rewrite IsProperColoring as "no edge in monoEdgesFinset"
  have hset_eq : {G : SimpleGraph (Fin n) | IsProperColoring G k π} =
      {G : SimpleGraph (Fin n) | ∀ e ∈ monoEdgesFinset n k π, ¬ G.Adj e.out.1 e.out.2} := by
    ext G
    simp only [Set.mem_setOf_eq, IsProperColoring, monoEdgesFinset,
               Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · -- proper → no mono edge in G
      intro hproper e ⟨_, hcolor⟩ hadj
      -- e.out.1 and e.out.2 are adjacent; if same color, contradiction
      have hne : π e.out.1 ≠ π e.out.2 := hproper e.out.1 e.out.2 hadj
      exact hne hcolor
    · -- no mono edge → proper
      intro hnoedge u v hadj heq
      -- s(u,v) is a mono edge; use its out pair
      set e := (s(u, v) : Sym2 (Fin n)) with he_def
      have hnd : ¬ e.IsDiag := Sym2.mk_isDiag_iff.not.mpr (G.ne_of_adj hadj)
      -- e.out.1 and e.out.2 are the same as u,v (or v,u) since s(e.out.1, e.out.2) = e = s(u,v)
      have hout : s(e.out.1, e.out.2) = s(u, v) := Quot.out_eq e
      have hcolor : π e.out.1 = π e.out.2 := by
        rcases (Sym2.eq_iff.mp hout) with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]; exact heq
        · rw [h1, h2]; exact heq.symm
      have hnadj : ¬ G.Adj e.out.1 e.out.2 := hnoedge _ ⟨hnd, hcolor⟩
      -- From hout, G.Adj e.out.1 e.out.2 ↔ G.Adj u v
      rcases (Sym2.eq_iff.mp hout) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2] at hnadj; exact absurd hadj hnadj
      · rw [h1, h2] at hnadj; exact absurd hadj.symm hnadj
  rw [hset_eq]
  apply gnHalf_no_edges_prob
  intro e he
  exact ((Finset.mem_filter.mp he).2).1

/-- **Class-bounded proper coloring (DEF_B, paper's χ_t):**
  A proper k-coloring where every color class has at most t vertices.
  This matches [heckel2023colouring] Definition 1.3: "t-bounded k-coloring". -/
def IsClassBoundedProperColoring (G : SimpleGraph (Fin n)) (k t : ℕ) (π : Fin n → Fin k) : Prop :=
  IsProperColoring G k π ∧ ∀ i : Fin k, (Finset.univ.filter (fun v => π v = i)).card ≤ t

/-- Probability that G(n,1/2) makes π a class-bounded proper coloring:
  = (1/2)^{monoEdgesCard π} if class sizes ok, else 0. -/
lemma gnHalf_classBounded_prob (n k t : ℕ) (π : Fin n → Fin k) :
    gnHalf n {G : SimpleGraph (Fin n) | IsClassBoundedProperColoring G k t π} =
    if (∀ i : Fin k, (Finset.univ.filter (fun v => π v = i)).card ≤ t)
    then (1 / 2 : ℝ≥0∞) ^ (monoEdgesFinset n k π).card
    else 0 := by
  split_ifs with hbound
  · -- Class sizes ok: set = proper colorings
    have heq : {G : SimpleGraph (Fin n) | IsClassBoundedProperColoring G k t π} =
               {G : SimpleGraph (Fin n) | IsProperColoring G k π} := by
      ext G; simp [IsClassBoundedProperColoring, hbound]
    rw [heq]
    exact gnHalf_no_monoEdges_prob n k π
  · -- Class sizes out of bound: set = ∅
    have heq : {G : SimpleGraph (Fin n) | IsClassBoundedProperColoring G k t π} = ∅ := by
      ext G; simp [IsClassBoundedProperColoring, hbound]
    rw [heq]; exact measure_empty

/-- Count of class-bounded k-colorings of G (DEF_B).
  Uses classical decidability to form the filter. -/
noncomputable def classColoringCount (n k t : ℕ) (G : SimpleGraph (Fin n)) : ℕ :=
  letI : DecidablePred (fun π : Fin n → Fin k => IsClassBoundedProperColoring G k t π) :=
    fun _ => Classical.propDecidable _
  (Finset.univ (α := Fin n → Fin k)).filter
    (fun π => IsClassBoundedProperColoring G k t π) |>.card

/-- Decompose classColoringCount as a finite sum of 0/1 indicators. -/
lemma classColoringCount_eq_sum (n k t : ℕ) (G : SimpleGraph (Fin n)) :
    (classColoringCount n k t G : ℝ≥0∞) =
      ∑ π : Fin n → Fin k,
        if IsClassBoundedProperColoring G k t π then 1 else 0 := by
  simp only [classColoringCount]
  letI hDec : DecidablePred (fun π : Fin n → Fin k => IsClassBoundedProperColoring G k t π) :=
    fun _ => Classical.propDecidable _
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  push_cast
  rfl

/-- `{G | IsClassBoundedProperColoring G k t π}` is measurable. -/
lemma measurableSet_isClassBoundedProperColoring (n k t : ℕ) (π : Fin n → Fin k) :
    MeasurableSet {G : SimpleGraph (Fin n) | IsClassBoundedProperColoring G k t π} := by
  -- Class size condition is independent of G; proper coloring condition is a finite intersection
  by_cases hbound : ∀ i : Fin k, (Finset.univ.filter (fun v => π v = i)).card ≤ t
  · -- Class sizes are ok: set = {G | IsProperColoring G k π}
    have heq : {G : SimpleGraph (Fin n) | IsClassBoundedProperColoring G k t π} =
               {G : SimpleGraph (Fin n) | IsProperColoring G k π} := by
      ext G; simp [IsClassBoundedProperColoring, hbound]
    rw [heq]
    -- {G | IsProperColoring G k π} = ⋂_{u,v with π u = π v} {G | ¬G.Adj u v}
    -- {G | IsProperColoring G k π} = ⋂_{u,v} {G | ¬G.Adj u v ∨ π u ≠ π v}
    have heq2 : {G : SimpleGraph (Fin n) | IsProperColoring G k π} =
        ⋂ u : Fin n, ⋂ v : Fin n,
          {G : SimpleGraph (Fin n) | ¬G.Adj u v ∨ π u ≠ π v} := by
      ext G
      simp only [IsProperColoring, Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro h u v; by_cases hadj : G.Adj u v; exact Or.inr (h u v hadj); exact Or.inl hadj
      · intro h u v hadj; rcases h u v with h1 | h2; exact absurd hadj h1; exact h2
    rw [heq2]
    apply MeasurableSet.iInter; intro u
    apply MeasurableSet.iInter; intro v
    by_cases hπ : π u = π v
    · have : {G : SimpleGraph (Fin n) | ¬G.Adj u v ∨ π u ≠ π v} = {G | ¬G.Adj u v} := by
        ext G; simp [hπ]
      rw [this]
      exact (SimpleGraph.measurable_iff_adj.mp measurable_id u v).setOf.compl
    · have : {G : SimpleGraph (Fin n) | ¬G.Adj u v ∨ π u ≠ π v} = Set.univ := by
        ext G; simp [hπ]
      rw [this]; exact MeasurableSet.univ
  · -- Class sizes out of bound: set = ∅
    have heq : {G : SimpleGraph (Fin n) | IsClassBoundedProperColoring G k t π} = ∅ := by
      ext G; simp [IsClassBoundedProperColoring, hbound]
    rw [heq]; exact MeasurableSet.empty

/-- Measurability of the class-bounded coloring indicator function. -/
theorem gnHalf_class_coloring_indicator_measurable (n k t : ℕ) (π : Fin n → Fin k) :
    Measurable (fun G : SimpleGraph (Fin n) =>
      ({G' : SimpleGraph (Fin n) | IsClassBoundedProperColoring G' k t π} : Set _).indicator
        (1 : SimpleGraph (Fin n) → ℝ≥0∞) G) :=
  Measurable.indicator measurable_const (measurableSet_isClassBoundedProperColoring n k t π)

/-- The coloring profile of π: for each class size u, count how many color classes of π have size u. -/
noncomputable def coloringProfileOf (n k : ℕ) (π : Fin n → Fin k) : Fin (n + 1) → Fin (n + 1) :=
  fun u =>
    let cnt := (Finset.univ (α := Fin k)).filter
      (fun i => (Finset.univ.filter (fun v => π v = i)).card = u.val) |>.card
    ⟨min cnt n, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

/-- If all class sizes are ≤ t, the profile lies in coloringProfileFinset n k t. -/
lemma coloringProfileOf_mem_finset (n k t : ℕ) (π : Fin n → Fin k)
    (hk : k ≤ n)
    (hbound : ∀ i : Fin k, (Finset.univ.filter (fun v => π v = i)).card ≤ t) :
    coloringProfileOf n k π ∈ coloringProfileFinset n k t := by
  -- Abbreviations
  let classOf : Fin k → Finset (Fin n) := fun i => Finset.univ.filter (fun v => π v = i)
  let cntOf : Fin (n + 1) → ℕ := fun u =>
    (Finset.univ (α := Fin k)).filter (fun i => (classOf i).card = u.val) |>.card
  -- Helper: card bound
  have hclass_card_le : ∀ i : Fin k, (classOf i).card ≤ n := fun i =>
    (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
  have hclass_card_lt : ∀ i : Fin k, (classOf i).card < n + 1 := fun i =>
    Nat.lt_succ_of_le (hclass_card_le i)
  -- Auxiliary: the classOf i partition Fin n
  have hpart : ∀ v : Fin n, ∃! i : Fin k, v ∈ classOf i := by
    intro v; exact ⟨π v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩,
      fun j hj => (Finset.mem_filter.mp hj).2.symm⟩
  -- Step 0: The profile value at u is min (cntOf u) n
  have hval : ∀ u : Fin (n + 1), (coloringProfileOf n k π u).val = min (cntOf u) n := by
    intro u; simp only [coloringProfileOf, cntOf, classOf]
  -- Step 1: ∑_{i : Fin k} |classOf i| = n
  have hsum_classes : ∑ i : Fin k, (classOf i).card = n := by
    have hbij : (Finset.univ (α := Fin n)) = Finset.univ.biUnion classOf := by
      ext v; simp [classOf]
    have hdisj : (Finset.univ (α := Fin k) : Set (Fin k)).PairwiseDisjoint classOf := by
      intro i _ j _ hij
      rw [Function.onFun, Finset.disjoint_left]
      intro v hvi hvj
      simp only [classOf, Finset.mem_filter, Finset.mem_univ, true_and] at hvi hvj
      exact hij (hvi.symm.trans hvj)
    calc ∑ i : Fin k, (classOf i).card
        = (Finset.univ.biUnion classOf).card := (Finset.card_biUnion hdisj).symm
      _ = (Finset.univ (α := Fin n)).card := by rw [← hbij]
      _ = n := Fintype.card_fin n
  -- Step 2: cntOf u ≤ n for all u
  have hcnt_le : ∀ u : Fin (n + 1), cntOf u ≤ n := by
    intro ⟨u, hu⟩
    rcases Nat.eq_zero_or_pos u with rfl | hupos
    · -- u = 0: #{i | |class_i|=0} ≤ k ≤ n
      calc cntOf ⟨0, hu⟩
          ≤ (Finset.univ (α := Fin k)).card := Finset.card_filter_le _ _
        _ = k := Fintype.card_fin k
        _ ≤ n := hk
    · -- u ≥ 1: u * cntOf u ≤ ∑_i |class_i| = n
      have key : u * cntOf ⟨u, hu⟩ ≤ n := by
        have step1 : u * cntOf ⟨u, hu⟩ =
            ∑ i ∈ (Finset.univ (α := Fin k)).filter (fun i => (classOf i).card = u),
              (classOf i).card := by
          have hrepl : ∑ i ∈ (Finset.univ (α := Fin k)).filter (fun i => (classOf i).card = u),
              (classOf i).card =
              ∑ _i ∈ (Finset.univ (α := Fin k)).filter (fun i => (classOf i).card = u), u :=
            Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)
          rw [hrepl]
          simp only [cntOf, Finset.sum_const, smul_eq_mul]
          ring
        rw [step1]
        exact (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans
          (le_of_eq hsum_classes)
      calc cntOf ⟨u, hu⟩ ≤ u * cntOf ⟨u, hu⟩ := Nat.le_mul_of_pos_left _ hupos
        _ ≤ n := key
  -- Step 3: min (cntOf u) n = cntOf u
  have hmin_eq : ∀ u : Fin (n + 1), min (cntOf u) n = cntOf u := fun u =>
    Nat.min_eq_left (hcnt_le u)
  -- Auxiliary: profile function for double-counting
  -- f : Fin k → Fin(n+1) given by i ↦ ⟨|class_i|, lt_succ⟩
  let sizeOf : Fin k → Fin (n + 1) := fun i => ⟨(classOf i).card, hclass_card_lt i⟩
  -- cntOf u = #{i | sizeOf i = u}
  have hcnt_eq : ∀ u : Fin (n + 1), cntOf u =
      ((Finset.univ (α := Fin k)).filter (fun i => sizeOf i = u)).card := fun u => by
    -- sizeOf i = u ↔ (classOf i).card = u.val
    have : (Finset.univ (α := Fin k)).filter (fun i => (classOf i).card = u.val) =
        (Finset.univ (α := Fin k)).filter (fun i => sizeOf i = u) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, sizeOf]
      exact ⟨fun h => Fin.ext h, fun h => congr_arg Fin.val h⟩
    exact congrArg Finset.card this
  -- Step 4: ∑_u cntOf u = k
  have hdc2 : ∑ u : Fin (n + 1), cntOf u = k := by
    -- Use card_eq_sum_card_fiberwise: k = ∑_u #{i | sizeOf i = u}
    have hfib : ∀ u : Fin (n + 1), (Finset.univ (α := Fin k)).filter (fun i => sizeOf i = u) =
        (Finset.univ (α := Fin k)).filter (fun i => (classOf i).card = u.val) := fun u => by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, sizeOf]
      exact ⟨fun h => congr_arg Fin.val h, fun h => Fin.ext h⟩
    have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ (α := Fin k))
        (t := Finset.univ (α := Fin (n + 1))) (f := sizeOf)
        (fun i _ => Finset.mem_univ _)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    rw [this]
    apply Finset.sum_congr rfl
    intro u _
    rw [hfib u]
  -- Step 5: ∑_u u.val * cntOf u = n
  have hdc1 : ∑ u : Fin (n + 1), u.val * cntOf u = n := by
    -- ∑_u u * #{i | |class_i|=u} = ∑_i |class_i| = n
    -- Step A: u * #{i | |class_i|=u} = ∑_{i | |class_i|=u} |class_i|
    have lhs_rw : ∀ u : Fin (n + 1), u.val * cntOf u =
        ∑ i ∈ (Finset.univ (α := Fin k)).filter (fun i => (classOf i).card = u.val),
          (classOf i).card := fun u => by
      have h1 : ∑ i ∈ (Finset.univ (α := Fin k)).filter (fun i => (classOf i).card = u.val),
          (classOf i).card =
          ∑ _i ∈ (Finset.univ (α := Fin k)).filter (fun i => (classOf i).card = u.val), u.val :=
        Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)
      rw [h1]
      simp only [cntOf, Finset.sum_const, smul_eq_mul]
      ring
    -- Step B: swap sums
    have swap : ∑ u : Fin (n + 1),
        ∑ i ∈ (Finset.univ (α := Fin k)).filter (fun i => (classOf i).card = u.val),
          (classOf i).card = ∑ i : Fin k, (classOf i).card := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      -- ∑ u : Fin(n+1), if (classOf i).card = u.val then (classOf i).card else 0
      -- = (classOf i).card  (the unique u with u.val = |class_i| contributes)
      have : ∑ u : Fin (n + 1), (if (classOf i).card = u.val then (classOf i).card else 0) =
          (classOf i).card := by
        rw [← Finset.sum_filter, Finset.sum_const]
        have hfilt : (Finset.univ (α := Fin (n + 1))).filter (fun u => (classOf i).card = u.val) =
            {⟨(classOf i).card, hclass_card_lt i⟩} := by
          ext u; simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_singleton,
                             true_and, Fin.ext_iff]
          omega
        rw [hfilt]; simp
      exact this
    -- Now: ∑_u lhs_rw(u) = ∑_u ∑_{filter} = ∑_i |class_i| = n
    have goal_eq : ∑ u : Fin (n + 1), u.val * cntOf u =
        ∑ u : Fin (n + 1),
          ∑ i ∈ (Finset.univ (α := Fin k)).filter (fun i => (classOf i).card = u.val),
            (classOf i).card :=
      Finset.sum_congr rfl (fun u _ => lhs_rw u)
    rw [goal_eq, swap, hsum_classes]
  -- Now prove membership
  simp only [coloringProfileFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, ?_, ?_⟩
  · -- ∑_u u.val * (coloringProfileOf u).val = n
    conv_lhs => arg 2; ext u; rw [hval u, hmin_eq u]
    exact hdc1
  · -- ∑_u (coloringProfileOf u).val = k
    conv_lhs => arg 2; ext u; rw [hval u, hmin_eq u]
    exact hdc2
  · -- u.val > t → (coloringProfileOf u).val = 0
    intro u hut
    rw [hval u, hmin_eq u]
    simp only [cntOf, Finset.card_eq_zero]
    apply Finset.filter_eq_empty_iff.mpr
    intro i _
    -- |classOf i| ≤ t < u
    have hbi : (classOf i).card ≤ t := hbound i
    omega

/-- The number of monochromatic edges of π equals profileF of its profile. -/
lemma monoEdgesFinset_card_eq_profileF (n k : ℕ) (π : Fin n → Fin k) :
    (monoEdgesFinset n k π).card =
    profileF n (fun u => (coloringProfileOf n k π u).val) := by
  -- Define the color class for each color i.
  let classOf : Fin k → Finset (Fin n) := fun i => Finset.univ.filter (fun v => π v = i)
  -- Abbreviate cnt function
  let cntOf : Fin (n + 1) → ℕ := fun u =>
    (Finset.univ (α := Fin k)).filter (fun i => (classOf i).card = u.val) |>.card
  -- Step A: monoEdgesFinset.card = ∑_{i : Fin k} C(|classOf i|, 2).
  have h_mono_card : (monoEdgesFinset n k π).card = ∑ i : Fin k, Nat.choose (classOf i).card 2 := by
    -- Partition monoEdgesFinset by color
    let classEdges : Fin k → Finset (Sym2 (Fin n)) :=
      fun i => (classOf i).offDiag.image Sym2.mk.uncurry
    have h_union : monoEdgesFinset n k π = Finset.univ.biUnion classEdges := by
      ext e
      constructor
      · intro he
        simp only [monoEdgesFinset, Finset.mem_filter, Finset.mem_univ, true_and] at he
        obtain ⟨hnd, hcol⟩ := he
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
        refine ⟨π e.out.1, ?_⟩
        simp only [classEdges, classOf, Finset.mem_image]
        refine ⟨e.out, ?_, ?_⟩
        · rw [Finset.mem_offDiag]
          refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩,
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcol.symm⟩, ?_⟩
          intro heq
          apply hnd
          conv_rhs => rw [← Quot.out_eq e]
          exact Sym2.mk_isDiag_iff.mpr heq
        · simp only [Function.uncurry]
          exact Quot.out_eq e
      · intro he
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at he
        obtain ⟨i, hei⟩ := he
        simp only [classEdges, classOf, Finset.mem_image] at hei
        obtain ⟨⟨a, b⟩, hab_mem, hmk⟩ := hei
        rw [Finset.mem_offDiag] at hab_mem
        obtain ⟨ha, hb, hne⟩ := hab_mem
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
        simp only [Function.uncurry] at hmk
        rw [← hmk]
        simp only [monoEdgesFinset, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨Sym2.mk_isDiag_iff.not.mpr hne, ?_⟩
        -- π s(a,b).out.1 = π s(a,b).out.2: both endpoints are in {a,b}, both have color i
        have hmem1 : s(a, b).out.1 = a ∨ s(a, b).out.1 = b := by
          have := Sym2.out_fst_mem (s(a, b)); simp only [Sym2.mem_iff] at this; exact this
        have hmem2 : s(a, b).out.2 = a ∨ s(a, b).out.2 = b := by
          have := Sym2.out_snd_mem (s(a, b)); simp only [Sym2.mem_iff] at this; exact this
        rcases hmem1 with h1 | h1 <;> rcases hmem2 with h2 | h2 <;> rw [h1, h2] <;>
          simp [ha, hb]
    have h_disj : (Finset.univ (α := Fin k) : Set (Fin k)).PairwiseDisjoint classEdges := by
      intro i _ j _ hij
      rw [Function.onFun, Finset.disjoint_left]
      intro e hei hej
      simp only [classEdges, classOf, Finset.mem_image, Finset.mem_offDiag,
                 Finset.mem_filter, Finset.mem_univ, true_and, Function.uncurry] at hei hej
      obtain ⟨⟨a, b⟩, ⟨⟨ha, hb, _⟩, hmk⟩⟩ := hei
      obtain ⟨⟨c, d⟩, ⟨⟨hc, _, _⟩, hmk2⟩⟩ := hej
      rw [← hmk] at hmk2
      -- hmk2 : s(c, d) = s(a, b); ha : π a = i; hb : π b = i; hc : π c = j
      rcases Sym2.eq_iff.mp hmk2 with ⟨h1, _⟩ | ⟨h1, _⟩
      · -- c = a
        exact hij (ha ▸ h1 ▸ hc ▸ rfl)
      · -- c = b
        exact hij (hb ▸ h1 ▸ hc ▸ rfl)
    have h_card_class : ∀ i : Fin k,
        (classEdges i).card = Nat.choose (classOf i).card 2 :=
      fun i => Sym2.card_image_offDiag (classOf i)
    rw [h_union, Finset.card_biUnion h_disj]
    simp [h_card_class]
  -- Step B: profileF = ∑_{i : Fin k} C(|classOf i|, 2).
  have h_profileF : profileF n (fun u => (coloringProfileOf n k π u).val) =
      ∑ i : Fin k, Nat.choose (classOf i).card 2 := by
    -- Unfold definitions
    have hfun : ∀ u : Fin (n + 1), (coloringProfileOf n k π u).val = min (cntOf u) n := by
      intro u; simp only [coloringProfileOf, cntOf, classOf]
    simp only [profileF]
    simp_rw [hfun]
    -- For u ≥ 1: cntOf u ≤ n, so min (cntOf u) n = cntOf u
    have h_min_eq : ∀ u : Fin (n + 1), 1 ≤ u.val → min (cntOf u) n = cntOf u := by
      intro u hu
      apply Nat.min_eq_left
      -- cntOf u * u.val ≤ n, so cntOf u ≤ n
      have hle : cntOf u * u.val ≤ n := by
        simp only [cntOf, classOf]
        have heq : ((Finset.univ (α := Fin k)).filter
            (fun i => (Finset.univ.filter (fun v => π v = i)).card = u.val)).card * u.val =
            ∑ i ∈ (Finset.univ (α := Fin k)).filter
              (fun i => (Finset.univ.filter (fun v => π v = i)).card = u.val),
              (Finset.univ.filter (fun v => π v = i)).card := by
          rw [Finset.sum_const_nat]; intro i hi; exact (Finset.mem_filter.mp hi).2
        rw [heq]
        calc ∑ i ∈ (Finset.univ (α := Fin k)).filter
                (fun i => (Finset.univ.filter (fun v => π v = i)).card = u.val),
              (Finset.univ.filter (fun v => π v = i)).card
            ≤ ∑ i : Fin k, (Finset.univ.filter (fun v => π v = i)).card :=
                Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
          _ = n := by
              rw [← Finset.card_biUnion]
              · -- biUnion of all color classes = univ
                have : Finset.univ.biUnion (fun i : Fin k => Finset.univ.filter (fun v => π v = i)) =
                    Finset.univ := by
                  ext v; simp
                rw [this, Finset.card_univ, Fintype.card_fin]
              · intro i _ j _ hij
                simp only [Finset.disjoint_filter]
                intro v _ hi hj; exact hij (hi ▸ hj)
      have hpos : 0 < u.val := by omega
      calc cntOf u ≤ cntOf u * u.val := Nat.le_mul_of_pos_right _ hpos
        _ ≤ n := hle
    -- Absorb min
    have h_term : ∀ u : Fin (n + 1),
        Nat.choose u.val 2 * min (cntOf u) n = Nat.choose u.val 2 * cntOf u := by
      intro u
      rcases Nat.eq_zero_or_pos u.val with hu | hu
      · simp [hu]
      · rw [h_min_eq u hu]
    simp_rw [h_term]
    -- Now: ∑_u C(u,2) * cntOf u = ∑_i C(|classOf i|, 2)
    -- Key: cntOf u = ∑_i [|classOf i|=u.val]
    have h_cntOf_sum : ∀ u : Fin (n + 1),
        cntOf u = ∑ i : Fin k, if (classOf i).card = u.val then 1 else 0 := by
      intro u
      simp only [cntOf, classOf, Finset.card_filter, Finset.mem_univ, ite_true]
    simp_rw [h_cntOf_sum, Finset.mul_sum]
    rw [← Finset.sum_comm]
    congr 1; ext i
    simp only [mul_ite, mul_one, mul_zero]
    have hlt : (classOf i).card ≤ n := by
      simp only [classOf]; exact (Finset.card_filter_le _ _).trans (by simp)
    rw [Finset.sum_eq_single ⟨(classOf i).card, Nat.lt_succ_of_le hlt⟩]
    · simp
    · intro u _ hne; simp [Ne.symm (Fin.val_ne_of_ne hne)]
    · simp
  rw [h_mono_card, h_profileF]

/-- The largest color class has size at least `n / k`. -/
private lemma exists_colorClass_card_ge (n k : ℕ) (hk : 0 < k) (π : Fin n → Fin k) :
    ∃ i : Fin k, n / k ≤ (Finset.univ.filter (fun v => π v = i)).card := by
  by_contra h
  push_neg at h
  have hlt : ∀ i : Fin k, (Finset.univ.filter (fun v => π v = i)).card < n / k := h
  have hsum : ∑ i : Fin k, (Finset.univ.filter (fun v : Fin n => π v = i)).card = n := by
    have key := Finset.card_eq_sum_card_fiberwise (s := Finset.univ (α := Fin n))
      (t := Finset.univ (α := Fin k)) (f := π) (fun v _ => Finset.mem_univ _)
    simp only [Finset.card_univ, Fintype.card_fin] at key
    omega
  have hlt_sum : n < k * (n / k) := by
    calc
      n = ∑ i : Fin k, (Finset.univ.filter (fun v : Fin n => π v = i)).card := hsum.symm
      _ < ∑ _i : Fin k, n / k := by
          apply Finset.sum_lt_sum
          · intro i _
            exact Nat.le_of_lt_succ (Nat.lt_succ_of_lt (hlt i))
          · exact ⟨⟨0, hk⟩, Finset.mem_univ _, hlt _⟩
      _ = k * (n / k) := by
          rw [Finset.sum_const, Finset.card_fin, smul_eq_mul]
  exact absurd hlt_sum (Nat.not_lt.mpr (Nat.mul_div_le n k))

/-- Any coloring has at least `choose (n / k) 2` monochromatic edges. -/
private lemma monoEdgesFinset_card_ge_choose (n k : ℕ) (hk : 0 < k) (π : Fin n → Fin k) :
    Nat.choose (n / k) 2 ≤ (monoEdgesFinset n k π).card := by
  let classOf : Fin k → Finset (Fin n) := fun i => Finset.univ.filter (fun v => π v = i)
  have h_mono_card : (monoEdgesFinset n k π).card = ∑ i : Fin k, Nat.choose (classOf i).card 2 := by
    let classEdges : Fin k → Finset (Sym2 (Fin n)) :=
      fun i => (classOf i).offDiag.image Sym2.mk.uncurry
    have h_union : monoEdgesFinset n k π = Finset.univ.biUnion classEdges := by
      ext e
      constructor
      · intro he
        simp only [monoEdgesFinset, Finset.mem_filter, Finset.mem_univ, true_and] at he
        obtain ⟨hnd, hcol⟩ := he
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
        refine ⟨π e.out.1, ?_⟩
        simp only [classEdges, classOf, Finset.mem_image]
        refine ⟨e.out, ?_, ?_⟩
        · rw [Finset.mem_offDiag]
          refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩,
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcol.symm⟩, ?_⟩
          intro heq
          apply hnd
          conv_rhs => rw [← Quot.out_eq e]
          exact Sym2.mk_isDiag_iff.mpr heq
        · simp only [Function.uncurry]
          exact Quot.out_eq e
      · intro he
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at he
        obtain ⟨i, hei⟩ := he
        simp only [classEdges, classOf, Finset.mem_image] at hei
        obtain ⟨⟨a, b⟩, hab_mem, hmk⟩ := hei
        rw [Finset.mem_offDiag] at hab_mem
        obtain ⟨ha, hb, hne⟩ := hab_mem
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
        simp only [Function.uncurry] at hmk
        rw [← hmk]
        simp only [monoEdgesFinset, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨Sym2.mk_isDiag_iff.not.mpr hne, ?_⟩
        have hmem1 : s(a, b).out.1 = a ∨ s(a, b).out.1 = b := by
          have := Sym2.out_fst_mem (s(a, b)); simp only [Sym2.mem_iff] at this; exact this
        have hmem2 : s(a, b).out.2 = a ∨ s(a, b).out.2 = b := by
          have := Sym2.out_snd_mem (s(a, b)); simp only [Sym2.mem_iff] at this; exact this
        rcases hmem1 with h1 | h1 <;> rcases hmem2 with h2 | h2 <;> rw [h1, h2] <;>
          simp [ha, hb]
    have h_disj : (Finset.univ (α := Fin k) : Set (Fin k)).PairwiseDisjoint classEdges := by
      intro i _ j _ hij
      rw [Function.onFun, Finset.disjoint_left]
      intro e hei hej
      simp only [classEdges, classOf, Finset.mem_image, Finset.mem_offDiag,
        Finset.mem_filter, Finset.mem_univ, true_and, Function.uncurry] at hei hej
      obtain ⟨⟨a, b⟩, ⟨⟨ha, hb, _⟩, hmk⟩⟩ := hei
      obtain ⟨⟨c, d⟩, ⟨⟨hc, _, _⟩, hmk2⟩⟩ := hej
      rw [← hmk] at hmk2
      rcases Sym2.eq_iff.mp hmk2 with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hij (ha ▸ h1 ▸ hc ▸ rfl)
      · exact hij (hb ▸ h1 ▸ hc ▸ rfl)
    have h_card_class : ∀ i : Fin k,
        (classEdges i).card = Nat.choose (classOf i).card 2 :=
      fun i => Sym2.card_image_offDiag (classOf i)
    rw [h_union, Finset.card_biUnion h_disj]
    simp [h_card_class]
  obtain ⟨i, hi⟩ := exists_colorClass_card_ge n k hk π
  have hmono :
      Nat.choose (n / k) 2 ≤
        ∑ j : Fin k, Nat.choose (classOf j).card 2 := by
    calc
      Nat.choose (n / k) 2 ≤ Nat.choose (classOf i).card 2 := by
        exact Nat.choose_le_choose 2 hi
      _ ≤ ∑ j : Fin k, Nat.choose (classOf j).card 2 := by
        exact Finset.single_le_sum
          (f := fun j : Fin k => Nat.choose (classOf j).card 2)
          (a := i)
          (fun j _ => Nat.zero_le _)
          (Finset.mem_univ i)
  exact hmono.trans_eq h_mono_card.symm

/-- Cauchy-Schwarz for C(·,2) sums: if `∑ xᵢ = n` and `k > 0`, then
    `k * C(n/k, 2) ≤ ∑ C(xᵢ, 2)`.  This is the key inequality that gives
    a sharp lower bound on the total monochromatic-edge count. -/
private lemma sum_choose_two_ge_k_mul_of_sum
    {k n : ℕ} (hk : 0 < k) (x : Fin k → ℕ) (hsum : ∑ i, x i = n) :
    k * Nat.choose (n / k) 2 ≤ ∑ i : Fin k, Nat.choose (x i) 2 := by
  suffices h : (k * Nat.choose (n / k) 2 : ℝ) ≤
      ∑ i : Fin k, (Nat.choose (x i) 2 : ℝ) by exact_mod_cast h
  set q := (n / k : ℕ)
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
  have hsum_r : ∑ i : Fin k, (x i : ℝ) = n := by push_cast [← hsum]; simp
  have hCS : (n : ℝ) ^ 2 ≤ k * ∑ i : Fin k, (x i : ℝ) ^ 2 := by
    rw [← hsum_r]
    have h := @sq_sum_le_card_mul_sum_sq (Fin k) ℝ _ _ _ _ Finset.univ (fun i => (x i : ℝ))
    simp only [Finset.card_univ, Fintype.card_fin] at h
    convert h using 1 <;> simp
  have hkq_le : (k : ℝ) * q ≤ n := by exact_mod_cast Nat.mul_div_le n k
  have hkq2_le : (k : ℝ) ^ 2 * (q : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
    have : (k : ℝ) * (q : ℝ) ≤ (n : ℝ) := hkq_le
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (Nat.cast_nonneg (α := ℝ) q)]
  -- Chain: Σ xᵢ(xᵢ-1) = Σ xᵢ² - n ≥ n²/k - n = n(n-k)/k ≥ k²q(q-1)/k = k*q*(q-1)
  -- where the last step uses n ≥ k*q (hkq_le).
  simp_rw [Nat.cast_choose_two]
  suffices hsuff : (k : ℝ) * q * (q - 1) ≤
      ∑ i : Fin k, ((x i : ℝ) * ((x i : ℝ) - 1)) by
    calc (k : ℝ) * ((q : ℝ) * ((q : ℝ) - 1) / 2)
        = k * q * (q - 1) / 2 := by ring
      _ ≤ (∑ i : Fin k, ((x i : ℝ) * ((x i : ℝ) - 1))) / 2 :=
          div_le_div_of_nonneg_right hsuff (by norm_num)
      _ = ∑ i : Fin k, ((x i : ℝ) * ((x i : ℝ) - 1) / 2) := by rw [← Finset.sum_div]
  simp_rw [show ∀ i : Fin k, (x i : ℝ) * ((x i : ℝ) - 1) = (x i : ℝ) ^ 2 - (x i : ℝ)
      from fun i => by ring, Finset.sum_sub_distrib, hsum_r]
  -- Goal: k*q*(q-1) ≤ S - n, where S = Σ xᵢ² and q = n/k (floor, natural, cast to ℝ).
  set S := ∑ i : Fin k, (x i : ℝ) ^ 2
  have hxnn : ∀ i, (0 : ℝ) ≤ x i := fun i => Nat.cast_nonneg _
  -- S ≥ n: each xᵢ² ≥ xᵢ (true for naturals since xᵢ*(xᵢ-1) ≥ 0), sum gives S ≥ Σ xᵢ = n.
  have hSn : (n : ℝ) ≤ S := by
    calc (n : ℝ) = ∑ i : Fin k, (x i : ℝ) := hsum_r.symm
      _ ≤ S := Finset.sum_le_sum fun i _ => by
          have hxi := hxnn i
          rcases Nat.eq_zero_or_pos (x i) with h | h
          · simp [show (x i : ℝ) = 0 from by exact_mod_cast h]
          · have hxi1 : (1 : ℝ) ≤ (x i : ℝ) := by exact_mod_cast h
            nlinarith
  have hqnn : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hdelta : 0 ≤ (n : ℝ) - k * q := by linarith
  -- q is a natural cast; either q = 0 (trivial) or q ≥ 1 (use arithmetic chain).
  rcases Nat.eq_zero_or_pos (n / k) with hq0 | hq1_nat
  · -- q = 0: LHS = 0 ≤ S - n.
    have hq0r : q = (0 : ℝ) := by exact_mod_cast hq0
    simp only [hq0r, mul_zero, zero_mul]
    linarith
  · -- q ≥ 1: k*q ≥ k, so n + k*q - k ≥ n ≥ 0.
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq1_nat
    have hq1_nn : (0 : ℝ) ≤ q - 1 := by linarith
    have hn_kq_k : (0 : ℝ) ≤ n + k * q - k := by nlinarith
    -- Step 1: k²*q*(q-1) ≤ n*(n-k). Witness: n*(n-k) - k²*q*(q-1) = (n-k*q)*(n+k*q-k) ≥ 0.
    have h_step1 : (k : ℝ) ^ 2 * q * (q - 1) ≤ n * (n - k) := by
      nlinarith [mul_nonneg hdelta hn_kq_k]
    -- Step 2: n*(n-k) ≤ k*(S-n), since k*S ≥ n².
    have h_step2 : (n : ℝ) * (n - k) ≤ k * (S - n) := by nlinarith [hCS]
    nlinarith [le_trans h_step1 h_step2]

/-- Sharp lower bound on monochromatic edges: every k-coloring on n vertices has at
    least `k * C(n/k, 2)` monochromatic edges.  This improves `monoEdgesFinset_card_ge_choose`
    by a factor of k, using the Cauchy-Schwarz inequality for the class-size distribution. -/
private lemma monoEdgesFinset_card_ge_k_times_choose
    (n k : ℕ) (hk : 0 < k) (π : Fin n → Fin k) :
    k * Nat.choose (n / k) 2 ≤ (monoEdgesFinset n k π).card := by
  let classOf : Fin k → Finset (Fin n) := fun i => Finset.univ.filter (fun v => π v = i)
  -- Step 1: card of monoEdgesFinset = ∑ C(|class i|, 2)  (already proved in the coarse bound)
  have h_mono_card : (monoEdgesFinset n k π).card = ∑ i : Fin k, Nat.choose (classOf i).card 2 := by
    let classEdges : Fin k → Finset (Sym2 (Fin n)) :=
      fun i => (classOf i).offDiag.image Sym2.mk.uncurry
    have h_union : monoEdgesFinset n k π = Finset.univ.biUnion classEdges := by
      ext e
      constructor
      · intro he
        simp only [monoEdgesFinset, Finset.mem_filter, Finset.mem_univ, true_and] at he
        obtain ⟨hnd, hcol⟩ := he
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
        refine ⟨π e.out.1, ?_⟩
        simp only [classEdges, classOf, Finset.mem_image]
        refine ⟨e.out, ?_, ?_⟩
        · rw [Finset.mem_offDiag]
          refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩,
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcol.symm⟩, ?_⟩
          intro heq
          apply hnd
          conv_rhs => rw [← Quot.out_eq e]
          exact Sym2.mk_isDiag_iff.mpr heq
        · simp only [Function.uncurry]
          exact Quot.out_eq e
      · intro he
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at he
        obtain ⟨i, hei⟩ := he
        simp only [classEdges, classOf, Finset.mem_image] at hei
        obtain ⟨⟨a, b⟩, hab_mem, hmk⟩ := hei
        rw [Finset.mem_offDiag] at hab_mem
        obtain ⟨ha, hb, hne⟩ := hab_mem
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
        simp only [Function.uncurry] at hmk
        rw [← hmk]
        simp only [monoEdgesFinset, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨Sym2.mk_isDiag_iff.not.mpr hne, ?_⟩
        have hmem1 : s(a, b).out.1 = a ∨ s(a, b).out.1 = b := by
          have := Sym2.out_fst_mem (s(a, b)); simp only [Sym2.mem_iff] at this; exact this
        have hmem2 : s(a, b).out.2 = a ∨ s(a, b).out.2 = b := by
          have := Sym2.out_snd_mem (s(a, b)); simp only [Sym2.mem_iff] at this; exact this
        rcases hmem1 with h1 | h1 <;> rcases hmem2 with h2 | h2 <;> rw [h1, h2] <;>
          simp [ha, hb]
    have h_disj : (Finset.univ (α := Fin k) : Set (Fin k)).PairwiseDisjoint classEdges := by
      intro i _ j _ hij
      rw [Function.onFun, Finset.disjoint_left]
      intro e hei hej
      simp only [classEdges, classOf, Finset.mem_image, Finset.mem_offDiag,
        Finset.mem_filter, Finset.mem_univ, true_and, Function.uncurry] at hei hej
      obtain ⟨⟨a, b⟩, ⟨⟨ha, hb, _⟩, hmk⟩⟩ := hei
      obtain ⟨⟨c, d⟩, ⟨⟨hc, _, _⟩, hmk2⟩⟩ := hej
      rw [← hmk] at hmk2
      rcases Sym2.eq_iff.mp hmk2 with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hij (ha ▸ h1 ▸ hc ▸ rfl)
      · exact hij (hb ▸ h1 ▸ hc ▸ rfl)
    have h_card_class : ∀ i : Fin k,
        (classEdges i).card = Nat.choose (classOf i).card 2 :=
      fun i => Sym2.card_image_offDiag (classOf i)
    rw [h_union, Finset.card_biUnion h_disj]
    simp [h_card_class]
  -- Step 2: class sizes sum to n (partition into fibers via card_eq_sum_card_fiberwise)
  have hclass_sum : ∑ i : Fin k, (classOf i).card = n := by
    have key : ∑ i : Fin k, (Finset.univ.filter (fun v : Fin n => π v = i)).card =
        Fintype.card (Fin n) := by
      rw [← Finset.card_univ]
      exact (Finset.card_eq_sum_card_fiberwise (fun v _ => Finset.mem_univ (π v))).symm
    simpa [classOf, Fintype.card_fin] using key
  -- Step 3: apply Cauchy-Schwarz
  rw [h_mono_card]
  exact sum_choose_two_ge_k_mul_of_sum hk (fun i => (classOf i).card) hclass_sum

-- Helper lemmas for card_prescribedFiber (used in fiber_count_eq)
private lemma castSucc_inj_on' (k : ℕ) :
    ∀ a ∈ (Finset.univ : Finset (Fin k)), ∀ b ∈ (Finset.univ : Finset (Fin k)),
      Fin.castSucc a = Fin.castSucc b → a = b :=
  fun _ _ _ _ h => Fin.castSucc_inj.mp h

private lemma multinomial_image_castSucc' (k : ℕ) (c : Fin (k+1) → ℕ) :
    Nat.multinomial (Finset.univ.image Fin.castSucc) c =
    Nat.multinomial Finset.univ (c ∘ Fin.castSucc) := by
  rw [Nat.multinomial, Finset.prod_image (castSucc_inj_on' k),
      Finset.sum_image (castSucc_inj_on' k), ← Nat.multinomial]; rfl

private lemma multinomial_fin_succ' (k : ℕ) (c : Fin (k+1) → ℕ) :
    Nat.multinomial (Finset.univ : Finset (Fin (k+1))) c =
    (∑ i, c i).choose (c (Fin.last k)) * Nat.multinomial Finset.univ (c ∘ Fin.castSucc) := by
  have h1 : (Finset.univ : Finset (Fin (k+1))) =
      insert (Fin.last k) (Finset.univ.image Fin.castSucc) := by
    ext x; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_image, true_and, true_iff]
    by_cases hx : x = Fin.last k
    · exact Or.inl hx
    · exact Or.inr ⟨x.castPred hx, (Fin.castSucc_castPred x hx).symm⟩
  have hnotmem : Fin.last k ∉ (Finset.univ : Finset (Fin k)).image Fin.castSucc := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rintro ⟨i, hi⟩; exact Fin.castSucc_ne_last i hi
  rw [h1, Nat.multinomial_insert hnotmem, multinomial_image_castSucc']
  congr 2
  rw [Finset.sum_insert hnotmem, Finset.sum_image (castSucc_inj_on' k)]

/-- The number of functions Fin n → Fin k with prescribed fiber sizes equals
    the multinomial coefficient. -/
private theorem card_prescribedFiber (n k : ℕ) (c : Fin k → ℕ) (hc : ∑ i, c i = n) :
    ((Finset.univ (α := Fin n → Fin k)).filter
      (fun π => ∀ i : Fin k, (Finset.univ.filter (fun v => π v = i)).card = c i)).card =
    Nat.multinomial Finset.univ c := by
  induction k generalizing n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hc
    subst hc; simp [Nat.multinomial]
  | succ k ih =>
    rw [multinomial_fin_succ']
    have hcn : c (Fin.last k) ≤ n := by
      calc c (Fin.last k) ≤ ∑ i, c i :=
            Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ _)
        _ = n := hc
    set m := n - c (Fin.last k)
    have hc' : ∑ i : Fin k, (c ∘ Fin.castSucc) i = m := by
      simp only [Function.comp, Fin.sum_univ_castSucc] at hc ⊢; omega
    let G : Finset (Fin n) → Finset (Fin n → Fin (k+1)) := fun S =>
      Finset.univ.filter (fun π =>
        Finset.univ.filter (fun v => π v = Fin.last k) = S ∧
        ∀ i : Fin k, (Finset.univ.filter (fun v => π v = i.castSucc)).card = c i.castSucc)
    let validS := (Finset.univ (α := Fin n)).powerset.filter
        (fun S : Finset (Fin n) => S.card = c (Fin.last k))
    have hLHS : (Finset.univ (α := Fin n → Fin (k+1))).filter
        (fun π => ∀ i, (Finset.univ.filter (fun v => π v = i)).card = c i) =
        validS.biUnion G := by
      ext π
      simp only [validS, G, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
                 Finset.mem_powerset]
      constructor
      · intro hπ
        exact ⟨Finset.univ.filter (fun v => π v = Fin.last k),
          ⟨fun _ _ => Finset.mem_univ _, by simpa using hπ (Fin.last k)⟩,
          rfl, fun i => hπ i.castSucc⟩
      · rintro ⟨S, ⟨-, hScard⟩, hSeq, hpre⟩ i
        by_cases hi : i = Fin.last k
        · subst hi; rw [hSeq]; exact hScard
        · have := hpre (i.castPred hi); rwa [Fin.castSucc_castPred i hi] at this
    have hdisj : Set.PairwiseDisjoint (↑validS) G := by
      intro S1 _ S2 _ hne
      simp only [Function.onFun, Finset.disjoint_left, G, Finset.mem_filter, Finset.mem_univ,
                 true_and]
      exact fun π ⟨h1, _⟩ ⟨h2, _⟩ => hne (h1.symm ▸ h2)
    have hGcard : ∀ S ∈ validS, (G S).card = Nat.multinomial Finset.univ (c ∘ Fin.castSucc) := by
      intro S hS
      simp only [validS, Finset.mem_filter, Finset.mem_powerset] at hS
      obtain ⟨-, hScard⟩ := hS
      have hcompl : (Finset.univ \ S).card = m := by
        rw [Finset.card_univ_diff, Fintype.card_fin, hScard]
      rw [← ih m (c ∘ Fin.castSucc) hc']
      let e := (Finset.univ \ S).orderIsoOfFin hcompl
      have he_not_S : ∀ i : Fin m, (e i).val ∉ S :=
        fun i => (Finset.mem_sdiff.mp (e i).prop).2
      apply Finset.card_bij (fun π hπ i =>
          (π ((e i).val)).castPred (fun heq => by
            have hπS := (Finset.mem_filter.mp hπ).2.1
            have hmem : (e i).val ∈ S := by
              have h := (Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩ : (e i).val ∈
                Finset.univ.filter (fun v => π v = Fin.last k))
              rw [hπS] at h; exact h
            exact he_not_S i hmem))
      · intro π hπ
        simp only [G, Finset.mem_filter, Finset.mem_univ, true_and] at hπ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp]
        intro i
        conv_lhs =>
          rw [show (Finset.univ.filter (fun j : Fin m =>
              (π ((e j).val)).castPred _ = i)) =
              Finset.univ.filter (fun j : Fin m => π ((e j).val) = i.castSucc) from by
            ext j; simp [Fin.castPred_eq_iff_eq_castSucc]]
        have h_ne_cs : ∀ v ∈ S, π v ≠ i.castSucc := fun v hvS heq => by
          have : v ∈ Finset.univ.filter (fun v => π v = Fin.last k) := by rw [hπ.1]; exact hvS
          simp at this; rw [this] at heq; exact absurd heq.symm (Fin.castSucc_ne_last i)
        calc (Finset.univ.filter (fun j : Fin m => π ((e j).val) = i.castSucc)).card
            = (Finset.univ.filter (fun v : Fin n => π v = i.castSucc)).card := by
              apply Finset.card_bij (fun j _ => (e j).val)
              · intro j hj; simp at hj ⊢; exact hj
              · intro j1 _ j2 _ heq; exact e.injective (Subtype.val_injective heq)
              · intro v hv
                simp at hv
                have hvS : v ∉ S := fun hvS => h_ne_cs v hvS hv
                have hvc : v ∈ Finset.univ \ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hvS⟩
                exact ⟨e.symm ⟨v, hvc⟩, by simp [hv],
                       congrArg Subtype.val (e.right_inv ⟨v, hvc⟩)⟩
          _ = c i.castSucc := hπ.2 i
      · intro π₁ hπ₁ π₂ hπ₂ hfuneq
        simp only [G, Finset.mem_filter, Finset.mem_univ, true_and] at hπ₁ hπ₂
        funext v
        by_cases hv : v ∈ S
        · have h1 : π₁ v = Fin.last k := by
            have : v ∈ Finset.univ.filter (fun v => π₁ v = Fin.last k) := by rw [hπ₁.1]; exact hv
            simpa using this
          have h2 : π₂ v = Fin.last k := by
            have : v ∈ Finset.univ.filter (fun v => π₂ v = Fin.last k) := by rw [hπ₂.1]; exact hv
            simpa using this
          rw [h1, h2]
        · have hvc : v ∈ Finset.univ \ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv⟩
          have hne1 : π₁ v ≠ Fin.last k := fun heq =>
            hv (hπ₁.1 ▸ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩))
          have hne2 : π₂ v ≠ Fin.last k := fun heq =>
            hv (hπ₂.1 ▸ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩))
          have key := congr_fun hfuneq (e.symm ⟨v, hvc⟩)
          simp only at key
          have hval : (e (e.symm ⟨v, hvc⟩)).val = v :=
            congrArg Subtype.val (e.right_inv ⟨v, hvc⟩)
          have key2 : (π₁ v).castPred hne1 = (π₂ v).castPred hne2 := by
            convert key using 2 <;> rw [hval]
          have := congrArg Fin.castSucc key2
          rwa [Fin.castSucc_castPred, Fin.castSucc_castPred] at this
      · intro π' hπ'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp] at hπ'
        let φ : Fin n → Fin (k+1) := fun v =>
          if hv : v ∈ S then Fin.last k
          else (π' (e.symm ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv⟩⟩)).castSucc
        refine ⟨φ, ?_, ?_⟩
        · simp only [G, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨?_, ?_⟩
          · ext v
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, φ]
            constructor
            · intro hv
              split_ifs at hv with hvS
              · exact hvS
              · simp [Fin.castSucc_ne_last] at hv
            · intro hvS; simp [dif_pos hvS]
          · intro i
            rw [show (Finset.univ.filter (fun v => φ v = i.castSucc)).card =
                (Finset.univ.filter (fun j : Fin m => π' j = i)).card from by
              symm
              apply @Finset.card_bij (Fin m) (Fin n)
                (Finset.univ.filter (fun j : Fin m => π' j = i))
                (Finset.univ.filter (fun v : Fin n => φ v = i.castSucc))
                (fun j _ => (e j).val)
              · intro j hj; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
                show φ (e j).val = i.castSucc
                simp only [φ, dif_neg (he_not_S j)]
                rw [show e.symm ⟨(e j).val, (e j).prop⟩ = j from e.left_inv j]
                exact congrArg Fin.castSucc hj
              · intro j1 _ j2 _ heq; exact e.injective (Subtype.val_injective heq)
              · intro v hv
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
                have hvS : v ∉ S := by
                  intro hvS; simp only [φ, dif_pos hvS] at hv
                  exact absurd hv.symm (Fin.castSucc_ne_last _)
                have hvc : v ∈ Finset.univ \ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hvS⟩
                refine ⟨e.symm ⟨v, hvc⟩, ?_, congrArg Subtype.val (e.right_inv ⟨v, hvc⟩)⟩
                simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                simp only [φ, dif_neg hvS] at hv
                have heq : e.symm ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hvS⟩⟩ =
                    e.symm ⟨v, hvc⟩ :=
                  congr_arg e.symm (Subtype.val_injective rfl)
                rw [← heq]; exact Fin.castSucc_injective _ hv]
            exact hπ' i
        · funext i
          simp only [φ, dif_neg (he_not_S i)]
          have hleft : e.symm ⟨(e i).val, (e i).prop⟩ = i := e.left_inv i
          simp only [hleft]
          exact Fin.castPred_castSucc
    have hvalidS_card : validS.card = n.choose (c (Fin.last k)) := by
      have heq : validS = Finset.powersetCard (c (Fin.last k)) Finset.univ := by
        ext S; simp [validS, Finset.mem_powersetCard]
      rw [heq, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    rw [hLHS, Finset.card_biUnion hdisj, Finset.sum_congr rfl hGcard,
        Finset.sum_const, smul_eq_mul, hvalidS_card, hc]

/-- The number of colorings Fin n → Fin k with a given profile f equals
    k! × profileP n f / profileSymm n f (as a real number).

  **Proof outline** (not yet formalized):

  Define `classSizeOf π : Fin k → ℕ` by `classSizeOf π i = #{v | π v = i}`.

  **Step 1 (decompose)**: The fiber `{π | profile(π) = f}` decomposes as
    `⋃_{sz : Fin k → ℕ, szProfile(sz) = f} {π | classSizeOf π = sz}`
  where `szProfile sz u = #{i | sz i = u}`, and the union is disjoint.

  **Step 2 (count inner)**: For fixed `sz` with `∑ sz = n`,
    `#{π | classSizeOf π = sz} = Nat.multinomial Finset.univ sz = n! / ∏_i (sz i)!`
  This follows from the bijection between ordered partitions of `Fin n` into
  groups of sizes `sz(0), ..., sz(k-1)` and functions `Fin n → Fin k` with
  those fiber sizes. (Proved by induction on k; each step uses `n.choose (sz i)`.)

  **Step 3 (count outer)**: The number of `sz : Fin k → ℕ` with `szProfile(sz) = f`
  equals `Nat.multinomial Finset.univ (fun u => (f u).val) = k! / ∏_u (f u)!`.
  This counts arrangements of `k` color labels into groups indexed by size class,
  and is the multinomial for distributing the k labels among the f(u) groups per size u.

  **Step 4 (multiply)**: For all `sz` with `szProfile(sz) = f`,
    `n! / ∏_i (sz i)! = n! / ∏_u (u!)^{f_u} = profileP n f`
  since `∏_i (sz i)! = ∏_u (u!)^{f_u}` when profile of sz equals f.

  **Combining**: fiber.card = (k! / ∏_u (f_u)!) × (n! / ∏_u (u!)^{f_u})
                            = k! × profileP n f / profileSymm n f.

  **Remaining obstacles for full formalization**:
  - Step 2 requires proving `Nat.multinomial Finset.univ sz` counts functions with
    prescribed fiber sizes (no direct Mathlib lemma found as of 2026-04).
  - Step 3 requires identifying the count of size-assignments with a given profile
    as a multinomial coefficient (no direct Mathlib lemma found as of 2026-04).
  - Real division requires showing `profileSymm ∣ k! * profileP` in ℕ.
-/
lemma fiber_count_eq (n k t : ℕ) (f : Fin (n + 1) → Fin (n + 1))
    (hf : f ∈ coloringProfileFinset n k t) :
    (((Finset.univ (α := Fin n → Fin k)).filter
      (fun π => coloringProfileOf n k π = f)).card : ℝ) =
    Nat.factorial k * profileP n (fun u => (f u).val) / profileSymm n (fun u => (f u).val) := by
  -- Abbreviations
  let fu : Fin (n + 1) → ℕ := fun u => (f u).val
  -- Extract profile constraints from hf
  have hfmem := hf
  simp only [coloringProfileFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hfmem
  obtain ⟨hsum_n, hsum_k, hbound⟩ := hfmem
  -- The key natural number identity:
  -- fiber.card * profileSymm n fu * ∏_u (u.val!)^{fu u} = k! * n!
  -- This is equivalent to the real division statement when profileSymm > 0.
  -- Sub-claim: profileSymm n fu > 0
  have hSymm_pos : 0 < profileSymm n fu := by
    unfold profileSymm
    apply Finset.prod_pos
    intro u _; exact Nat.factorial_pos _
  -- We need profileSymm n fu ∣ Nat.factorial k * profileP n fu to do the real division.
  -- We proceed by establishing the nat identity:
  -- fiber.card = Nat.multinomial Finset.univ fu * profileP n fu
  -- where Nat.multinomial Finset.univ fu = k! / profileSymm n fu.
  -- -------------------------------------------------------
  -- We use a different approach: biUnion decomposition.
  -- szFinset: size-assignments sz : Fin k → Fin (n+1) with correct histogram
  let szFinset : Finset (Fin k → Fin (n + 1)) :=
    (Finset.univ (α := Fin k → Fin (n + 1))).filter
      (fun sz => ∀ w : Fin (n + 1),
        ((Finset.univ (α := Fin k)).filter (fun i => sz i = w)).card = fu w)
  -- For each sz ∈ szFinset, the inner fiber
  let innerFiber : (Fin k → Fin (n + 1)) → Finset (Fin n → Fin k) := fun sz =>
    (Finset.univ (α := Fin n → Fin k)).filter
      (fun π => ∀ i : Fin k, (Finset.univ.filter (fun v => π v = i)).card = (sz i).val)
  -- Step 1: The main fiber = biUnion over szFinset of innerFiber
  have hFiberEq : (Finset.univ (α := Fin n → Fin k)).filter
      (fun π => coloringProfileOf n k π = f) =
      szFinset.biUnion innerFiber := by
    ext π
    simp only [szFinset, innerFiber, Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_biUnion]
    constructor
    · -- → : given π with correct profile, extract sz from class sizes
      intro hπ
      -- Define sz i = ⟨|class_i(π)|, bound⟩
      have hclass_le : ∀ i : Fin k,
          (Finset.univ.filter (fun v => π v = i)).card ≤ n := fun i =>
        (Finset.card_filter_le _ _).trans (by simp)
      let sz : Fin k → Fin (n + 1) := fun i =>
        ⟨(Finset.univ.filter (fun v => π v = i)).card,
         Nat.lt_succ_of_le (hclass_le i)⟩
      refine ⟨sz, ?_, fun i => rfl⟩
      -- Show sz ∈ szFinset: ∀ u, #{i | sz i = u} = fu u
      intro u
      -- #{i | sz i = u} = #{i | |class_i(π)| = u.val}
      have heq_filter : (Finset.univ (α := Fin k)).filter (fun i => sz i = u) =
          (Finset.univ (α := Fin k)).filter
            (fun i => (Finset.univ.filter (fun v => π v = i)).card = u.val) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, sz, Fin.mk.injEq, Fin.ext_iff]
      rw [heq_filter]
      -- This count = (coloringProfileOf n k π u).val by def
      have hprofile_val : (coloringProfileOf n k π u).val =
          min ((Finset.univ (α := Fin k)).filter
            (fun i => (Finset.univ.filter (fun v => π v = i)).card = u.val) |>.card) n := by
        simp only [coloringProfileOf]
      -- From hπ : coloringProfileOf n k π = f, we get (coloringProfileOf n k π u).val = fu u
      have hfu_eq : (coloringProfileOf n k π u).val = fu u := by
        exact congrArg (fun g => (g u).val) hπ
      -- So min cnt n = fu u
      rw [hprofile_val] at hfu_eq
      -- cnt ≤ k, fu u ≤ k ≤ ... we need min cnt n = cnt
      -- Use: ∑ u, fu u = k, and ∑ u, min cnt_u n ≤ ∑ u, cnt_u = k
      -- Actually: cnt_u ≤ k, and we need to show cnt_u = fu u
      -- Strategy: cnt_u = min cnt_u n (since cnt_u ≤ n) → cnt_u = fu u
      -- We know cnt_u ≤ k (count of colors with a given class size ≤ total colors)
      -- Also ∑ u, fu u = k = ∑ u, cnt_u (the latter by a partition argument)
      -- And min cnt_u n ≤ cnt_u, min cnt_u n = fu u → cnt_u ≥ fu u
      -- Together with ∑ cnt_u = ∑ fu u = k → cnt_u = fu u
      -- But let's just use: cnt_u ≤ n since sum u * cnt_u = n and u ≥ 1 → cnt_u ≤ n
      -- For u = 0: cnt_0 = #{i | |class_i| = 0} ≤ k
      -- We need cnt_u ≤ n to conclude min cnt_u n = cnt_u
      -- From hsum_n and hsum_k we know sum u.val * fu u = n, sum fu u = k
      -- cnt_u * u.val ≤ ∑ i |class_i| = n, so for u ≥ 1: cnt_u ≤ n
      -- For u = 0: cnt_0 ≤ k ≤ ... hmm we don't have k ≤ n in general here
      -- Actually wait: hmin_eq in the previous lemma required k ≤ n.
      -- Let's check: from hsum_n: ∑ u.val * fu u = n ≥ 0
      -- cnt_0 = #{i | |class_i| = 0} ≤ k
      -- But from hπ: min cnt_0 n = fu 0
      -- If k > n, then fu 0 could be... but also ∑ fu u = k > n.
      -- But then ∑ u.val * fu u = n while ∑ fu u = k > n, meaning most fu u concentrate at u=0.
      -- This is fine: min cnt_0 n = n = fu 0 when cnt_0 ≥ n.
      -- In any case, hfu_eq says min cnt n = fu u and we want cnt = fu u.
      -- Actually cnt = (Finset.univ.filter ...).card.
      -- We don't strictly need cnt = fu u; we just need the filter card = fu u.
      -- That's exactly what hfu_eq says after we show min cnt n = cnt for this u.
      -- Let's be concrete:
      set cnt := ((Finset.univ (α := Fin k)).filter
        (fun i => (Finset.univ.filter (fun v => π v = i)).card = u.val)).card with hcnt_def
      -- From hfu_eq: min cnt n = fu u
      -- We need: cnt = fu u
      -- Case 1: cnt ≤ n → min cnt n = cnt → cnt = fu u ✓
      -- Case 2: cnt > n → min cnt n = n = fu u → need cnt = fu u ... but cnt could be > fu u
      -- Actually in case 2: fu u = n < cnt ≤ k, meaning many colors have the same class size u.
      -- But then ∑ u, cnt_u = k and ∑ u, min cnt_u n = ∑ fu u = k
      -- If min cnt_u n < cnt_u for some u, then ∑ min < ∑ cnt = k but we need ∑ min = k too
      -- ∑ u, cnt_u = k follows from: every color i contributes to exactly one cnt_u
      -- ∑ u, min cnt_u n ≤ ∑ u, cnt_u = k and = ∑ fu u = k
      -- So min cnt_u n = cnt_u for all u → cnt = fu u ✓
      -- Let's prove ∑ u, cnt_u = k
      have hsum_cnt : ∑ u : Fin (n + 1), ((Finset.univ (α := Fin k)).filter
          (fun i => (Finset.univ.filter (fun v => π v = i)).card = u.val)).card = k := by
        -- map each i : Fin k to the unique u with |class_i| = u.val
        let classSzOf : Fin k → Fin (n + 1) := fun i =>
          ⟨(Finset.univ.filter (fun v => π v = i)).card,
           Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans (by simp))⟩
        have hfib : ∀ u : Fin (n + 1),
            (Finset.univ (α := Fin k)).filter (fun i => (Finset.univ.filter (fun v => π v = i)).card = u.val) =
            (Finset.univ (α := Fin k)).filter (fun i => classSzOf i = u) := by
          intro u; ext i; simp [classSzOf, Fin.ext_iff]
        simp_rw [hfib]
        have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ (α := Fin k))
          (t := Finset.univ (α := Fin (n + 1))) (f := classSzOf)
          (fun i _ => Finset.mem_univ _)
        simp only [Finset.card_univ, Fintype.card_fin] at this
        linarith
      -- Now: ∑ u, (coloringProfileOf n k π u).val = ∑ u, min (cnt u) n
      -- From hπ: ∑ u, fu u = ∑ u, (coloringProfileOf n k π u).val = ∑ u, min cnt_u n
      -- Also ∑ u, min cnt_u n ≤ ∑ u, cnt_u = k = ∑ fu u
      -- And ∑ u, min cnt_u n = ∑ fu u, so each min cnt_u n ≤ cnt_u with sum equality
      -- → min cnt_u n = cnt_u for all u → cnt_u = fu u
      -- Actually we can't conclude min cnt_u n = cnt_u for each u from sum equality alone
      -- unless we know min cnt_u n ≤ cnt_u (which is always true) AND sum equality.
      -- Sum equality: ∑ min cnt_u n = ∑ fu u = k = ∑ cnt_u
      -- For each u: min cnt_u n ≤ cnt_u, and ∑ min = ∑ cnt → each min = cnt ✓
      have hmin_eq_cnt : ∀ v : Fin (n + 1), min ((Finset.univ (α := Fin k)).filter
          (fun i => (Finset.univ.filter (fun j => π j = i)).card = v.val)).card n =
        ((Finset.univ (α := Fin k)).filter
          (fun i => (Finset.univ.filter (fun j => π j = i)).card = v.val)).card := by
        -- Prove ∑ min cnt_v n = ∑ cnt_v → min cnt_v n = cnt_v
        -- From hπ, ∑ fu u = ∑ (coloringProfileOf n k π u).val = ∑ min cnt n
        have hsum_min : ∑ v : Fin (n + 1), min ((Finset.univ (α := Fin k)).filter
            (fun i => (Finset.univ.filter (fun j => π j = i)).card = v.val)).card n =
          ∑ v : Fin (n + 1), ((Finset.univ (α := Fin k)).filter
            (fun i => (Finset.univ.filter (fun j => π j = i)).card = v.val)).card := by
          -- ∑ min cnt n = ∑ (coloringProfileOf n k π v).val = ∑ fu v = k = ∑ cnt
          have h1 : ∑ v : Fin (n + 1), min ((Finset.univ (α := Fin k)).filter
              (fun i => (Finset.univ.filter (fun j => π j = i)).card = v.val)).card n =
            ∑ v : Fin (n + 1), (coloringProfileOf n k π v).val := by
            simp only [coloringProfileOf]
          have h2 : ∑ v : Fin (n + 1), (coloringProfileOf n k π v).val =
            ∑ v : Fin (n + 1), fu v := by
            congr 1; ext v; exact congrArg (fun g => (g v).val) hπ
          rw [h1, h2, hsum_k, hsum_cnt]
        intro v
        -- Each min cnt n ≤ cnt, and ∑ min cnt n = ∑ cnt (both = k), so each min cnt n = cnt
        -- Sum of min ≤ sum of cnt (pointwise ≤)
        have hle_sum : ∑ w : Fin (n + 1), min ((Finset.univ (α := Fin k)).filter
              (fun i => (Finset.univ.filter (fun j => π j = i)).card = w.val)).card n ≤
            ∑ w : Fin (n + 1), ((Finset.univ (α := Fin k)).filter
              (fun i => (Finset.univ.filter (fun j => π j = i)).card = w.val)).card :=
          Finset.sum_le_sum (fun w _ => Nat.min_le_left _ _)
        -- Both sums = k
        rw [hsum_min, hsum_cnt] at hle_sum
        -- So ∑ min = k = ∑ cnt → equality of sums. And pointwise: min ≤ cnt.
        -- Use: if each term of first sum ≤ corresponding term of second, and sums are equal,
        -- then each term is equal.
        -- Specifically: since sums are equal (both k after hsum_min, hsum_cnt show ∑ min = k),
        -- and each term min_v ≤ cnt_v, we conclude min_v = cnt_v.
        -- Use Nat.sum_le_sum_iff: from ∑ min = ∑ cnt and ∀ v, min ≤ cnt, get min v = cnt v.
        -- Actually use: each min_v ≤ cnt_v, and ∑ min_v = k = ∑ cnt_v.
        -- If min_v < cnt_v for some v, then ∑ min < ∑ cnt, contradiction with hsum_min/hsum_cnt.
        -- Formalize: assume min_v < cnt_v, then sum of differences > 0, contradiction.
        have hpoint : min ((Finset.univ (α := Fin k)).filter
            (fun i => (Finset.univ.filter (fun j => π j = i)).card = v.val)).card n =
          ((Finset.univ (α := Fin k)).filter
            (fun i => (Finset.univ.filter (fun j => π j = i)).card = v.val)).card := by
          -- min_v ≤ cnt_v always
          have hle_v : min ((Finset.univ (α := Fin k)).filter
              (fun i => (Finset.univ.filter (fun j => π j = i)).card = v.val)).card n ≤
            ((Finset.univ (α := Fin k)).filter
              (fun i => (Finset.univ.filter (fun j => π j = i)).card = v.val)).card :=
            Nat.min_le_left _ _
          -- From hsum_min: ∑ min = ∑ fu = k
          -- From hsum_cnt: ∑ cnt = k
          -- Hence ∑ min = ∑ cnt
          have hsum_eq : ∑ w : Fin (n + 1), min ((Finset.univ (α := Fin k)).filter
              (fun i => (Finset.univ.filter (fun j => π j = i)).card = w.val)).card n =
            ∑ w : Fin (n + 1), ((Finset.univ (α := Fin k)).filter
              (fun i => (Finset.univ.filter (fun j => π j = i)).card = w.val)).card := by
            linarith [hle_sum]
          -- Pointwise: if min_v < cnt_v, then sum_min < sum_cnt (contradiction)
          by_contra hne
          push_neg at hne
          have hlt : min ((Finset.univ (α := Fin k)).filter
              (fun i => (Finset.univ.filter (fun j => π j = i)).card = v.val)).card n <
            ((Finset.univ (α := Fin k)).filter
              (fun i => (Finset.univ.filter (fun j => π j = i)).card = v.val)).card :=
            Nat.lt_of_le_of_ne hle_v hne
          have hlt_sum := Finset.sum_lt_sum
            (fun w _ => Nat.min_le_left ((Finset.univ.filter
              (fun i => (Finset.univ.filter (fun j => π j = i)).card = w.val)).card) n)
            ⟨v, Finset.mem_univ _, hlt⟩
          linarith [hsum_eq]
        exact hpoint
      rw [hmin_eq_cnt u] at hfu_eq
      exact hfu_eq
    · -- ← : given sz ∈ szFinset and π ∈ innerFiber sz, show coloringProfileOf n k π = f
      rintro ⟨sz, hsz, hπ⟩
      funext u
      apply Fin.ext
      simp only [coloringProfileOf]
      -- Need: min (#{i | |class_i(π)| = u.val}) n = fu u
      -- From hπ: |class_i(π)| = (sz i).val for all i
      -- So #{i | |class_i(π)| = u.val} = #{i | (sz i).val = u.val} = #{i | sz i = u}
      have hfilter_eq : (Finset.univ (α := Fin k)).filter
          (fun i => (Finset.univ.filter (fun v => π v = i)).card = u.val) =
        (Finset.univ (α := Fin k)).filter (fun i => sz i = u) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h
          exact Fin.ext ((hπ i).symm.trans h)
        · intro h
          rw [← congrArg Fin.val h]; exact (hπ i)
      rw [hfilter_eq]
      have hcnt_eq := hsz u
      -- min (fu u) n = fu u since fu u = (f u).val < n+1 → fu u ≤ n
      have hfu_le_n : fu u ≤ n := Nat.lt_succ_iff.mp (f u).isLt
      rw [hcnt_eq, Nat.min_eq_left hfu_le_n]
  -- Step 2: The biUnion is disjoint (different sz give disjoint inner fibers)
  have hDisjoint : Set.PairwiseDisjoint (↑szFinset) innerFiber := by
    intro sz1 _ sz2 _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro π hπ1 hπ2
    simp only [innerFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hπ1 hπ2
    apply hne
    funext i
    apply Fin.ext
    have h1 := hπ1 i
    have h2 := hπ2 i
    omega
  -- Step 3: For each sz ∈ szFinset, |innerFiber sz| = Nat.multinomial Finset.univ (fun i => (sz i).val)
  -- We need: ∑ i, (sz i).val = n for sz ∈ szFinset
  have hszSum : ∀ sz ∈ szFinset, ∑ i : Fin k, (sz i).val = n := by
    intro sz hsz
    simp only [szFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hsz
    -- ∑ i, (sz i).val = ∑ u, u.val * #{i | sz i = u} = ∑ u, u.val * fu u = n
    -- Partition: (sz i).val = ∑_u if sz i = u then u.val else 0
    have hpart : ∑ i : Fin k, (sz i).val =
        ∑ u : Fin (n + 1), u.val * ((Finset.univ (α := Fin k)).filter (fun i => sz i = u)).card := by
      -- Direct: ∑_i (sz i).val = ∑_i ∑_u [sz i = u] * u.val (pick out the unique u = sz i)
      have lhs : ∀ i : Fin k, (sz i).val =
          ∑ u : Fin (n+1), if sz i = u then u.val else 0 := by
        intro i; simp [Finset.sum_ite_eq']
      simp_rw [lhs, Finset.sum_comm (s := Finset.univ (α := Fin k))]
      congr 1; ext u
      rw [← Finset.sum_filter, Finset.sum_const]
      simp [smul_eq_mul, mul_comm]
    rw [hpart]
    simp_rw [hsz]
    exact hsum_n
  -- card_prescribedFiber for inner fibers
  have hInnerCard : ∀ sz ∈ szFinset, (innerFiber sz).card =
      Nat.multinomial Finset.univ (fun i => (sz i).val) := by
    intro sz hsz
    have hsum := hszSum sz hsz
    -- innerFiber sz = {π | ∀ i, |class_i(π)| = (sz i).val}
    have : innerFiber sz = (Finset.univ (α := Fin n → Fin k)).filter
        (fun π => ∀ i : Fin k, (Finset.univ.filter (fun v => π v = i)).card = (sz i).val) := rfl
    rw [this]
    exact card_prescribedFiber n k (fun i => (sz i).val) hsum
  -- Step 4: The multinomial for inner fibers = profileP n fu for all sz ∈ szFinset
  -- Key: ∏ i, (sz i).val! = ∏ u, u.val! ^ (fu u) when histogram of sz is fu
  have hInnerMultinomialEq : ∀ sz ∈ szFinset,
      Nat.multinomial Finset.univ (fun i => (sz i).val) = profileP n fu := by
    intro sz hsz
    simp only [szFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hsz
    -- multinomial = n! / ∏ i, (sz i).val!
    -- profileP n fu = n! / ∏ u, u.val! ^ (fu u)
    -- Key identity: ∏ i, (sz i).val! = ∏ u, u.val! ^ (fu u)
    have hprod_eq : ∏ i : Fin k, Nat.factorial (sz i).val =
        ∏ u : Fin (n + 1), Nat.factorial u.val ^ fu u := by
      -- Regroup: for each u, the fu u many indices i with sz i = u each contribute u.val!
      -- So ∏ i, (sz i)! = ∏ u, ∏_{i | sz i = u}, (sz i)! = ∏ u, (u!)^{fu u}
      have step1 : ∏ i : Fin k, Nat.factorial (sz i).val =
          ∏ u : Fin (n + 1), ∏ i ∈ (Finset.univ (α := Fin k)).filter (fun i => sz i = u),
            Nat.factorial (sz i).val := by
        -- Use Finset.prod_fiberwise
        exact (Finset.prod_fiberwise (Finset.univ (α := Fin k)) sz
          (fun i => Nat.factorial (sz i).val)).symm
      rw [step1]
      congr 1; ext u
      rw [Finset.prod_congr rfl (fun i hi => by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
            exact congrArg (fun x => Nat.factorial x.val) hi),
          Finset.prod_const, hsz u]
    -- Now use multinomial definition
    simp only [Nat.multinomial, profileP]
    rw [hszSum sz (by simp [szFinset, hsz]), hprod_eq]
  -- Step 5: Count of size assignments = Nat.multinomial Finset.univ fu
  have hSzCard : szFinset.card = Nat.multinomial Finset.univ fu := by
    -- szFinset = {sz : Fin k → Fin (n+1) | ∀ u, #{i | sz i = u} = fu u}
    -- This is card_prescribedFiber with n=k, k=n+1, c=fu
    rw [show szFinset = (Finset.univ (α := Fin k → Fin (n + 1))).filter
        (fun sz => ∀ u : Fin (n + 1), (Finset.univ.filter (fun i => sz i = u)).card = fu u) from rfl]
    exact card_prescribedFiber k (n + 1) fu hsum_k
  -- Step 6: Combine to get fiber.card = szFinset.card * profileP n fu
  have hFiberCard : ((Finset.univ (α := Fin n → Fin k)).filter
      (fun π => coloringProfileOf n k π = f)).card =
    szFinset.card * profileP n fu := by
    rw [hFiberEq, Finset.card_biUnion hDisjoint]
    rw [Finset.sum_congr rfl (fun sz hsz => by rw [hInnerCard sz hsz, hInnerMultinomialEq sz hsz])]
    simp [Finset.sum_const, smul_eq_mul]
  -- Step 7: Nat.multinomial Finset.univ fu = k! / profileSymm n fu
  have hMultinomialEq : Nat.multinomial Finset.univ fu = Nat.factorial k / profileSymm n fu := by
    simp only [Nat.multinomial, profileSymm, Finset.univ_eq_empty_iff]
    congr 1; rw [hsum_k]
  -- Step 8: Divisibility for the real division
  have hDvd : profileSymm n fu ∣ Nat.factorial k := by
    -- profileSymm n fu = ∏ u, (fu u)! divides (∑ u, fu u)! = k!
    have h : ∏ u : Fin (n+1), Nat.factorial (fu u) ∣ (∑ u : Fin (n+1), fu u).factorial :=
      Nat.prod_factorial_dvd_factorial_sum Finset.univ fu
    simp only [profileSymm]
    rwa [hsum_k] at h
  -- Step 9: profileSymm n fu ∣ k! * profileP n fu
  have hDvd2 : profileSymm n fu ∣ Nat.factorial k * profileP n fu :=
    Dvd.dvd.mul_right hDvd _
  -- Step 10: fiber.card = k! * profileP n fu / profileSymm n fu (as naturals)
  have hFiberCardNat : ((Finset.univ (α := Fin n → Fin k)).filter
      (fun π => coloringProfileOf n k π = f)).card =
    Nat.factorial k * profileP n fu / profileSymm n fu := by
    rw [hFiberCard, hSzCard, hMultinomialEq]
    -- k! / profileSymm * profileP = k! * profileP / profileSymm
    -- Goal: k! / profileSymm * profileP = k! * profileP / profileSymm
    obtain ⟨m, hm⟩ := hDvd
    rw [hm, Nat.mul_div_cancel_left _ hSymm_pos,
        show profileSymm n fu * m * profileP n fu =
             profileSymm n fu * (m * profileP n fu) from by ring,
        Nat.mul_div_cancel_left _ hSymm_pos]
  -- Step 11: Convert to ℝ
  rw [hFiberCardNat]
  rw [Nat.cast_div hDvd2 (by positivity)]
  push_cast
  ring

lemma profileP_pos_of_mem_coloringProfileFinset
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n k t) :
    0 < profileP n (fun u => (f u).val) := by
  let fu : Fin (n + 1) → ℕ := fun u => (f u).val
  have hfmem := hf
  simp only [coloringProfileFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hfmem
  obtain ⟨hsum_n, hsum_k, hbound⟩ := hfmem
  let szFinset : Finset (Fin k → Fin (n + 1)) :=
    (Finset.univ (α := Fin k → Fin (n + 1))).filter
      (fun sz => ∀ w : Fin (n + 1),
        ((Finset.univ (α := Fin k)).filter (fun i => sz i = w)).card = fu w)
  have hSzCard : szFinset.card = Nat.multinomial Finset.univ fu := by
    rw [show szFinset = (Finset.univ (α := Fin k → Fin (n + 1))).filter
        (fun sz => ∀ u : Fin (n + 1), (Finset.univ.filter (fun i => sz i = u)).card = fu u) from rfl]
    exact card_prescribedFiber k (n + 1) fu hsum_k
  have hcardpos : 0 < szFinset.card := by
    rw [hSzCard]
    exact Nat.multinomial_pos _ _
  obtain ⟨sz, hsz⟩ := Finset.card_pos.mp hcardpos
  have hszSum : ∑ i : Fin k, (sz i).val = n := by
    simp only [szFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hsz
    have hpart : ∑ i : Fin k, (sz i).val =
        ∑ u : Fin (n + 1), u.val * ((Finset.univ (α := Fin k)).filter (fun i => sz i = u)).card := by
      have lhs : ∀ i : Fin k, (sz i).val =
          ∑ u : Fin (n + 1), if sz i = u then u.val else 0 := by
        intro i; simp [Finset.sum_ite_eq']
      simp_rw [lhs, Finset.sum_comm (s := Finset.univ (α := Fin k))]
      congr 1; ext u
      rw [← Finset.sum_filter, Finset.sum_const]
      simp [smul_eq_mul, mul_comm]
    rw [hpart]
    simp_rw [hsz]
    exact hsum_n
  have hInnerMultinomialEq :
      Nat.multinomial Finset.univ (fun i => (sz i).val) = profileP n fu := by
    simp only [szFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hsz
    have hprod_eq : ∏ i : Fin k, Nat.factorial (sz i).val =
        ∏ u : Fin (n + 1), Nat.factorial u.val ^ fu u := by
      have step1 : ∏ i : Fin k, Nat.factorial (sz i).val =
          ∏ u : Fin (n + 1), ∏ i ∈ (Finset.univ (α := Fin k)).filter (fun i => sz i = u),
            Nat.factorial (sz i).val := by
        exact (Finset.prod_fiberwise (Finset.univ (α := Fin k)) sz
          (fun i => Nat.factorial (sz i).val)).symm
      rw [step1]
      congr 1; ext u
      rw [Finset.prod_congr rfl (fun i hi => by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
            exact congrArg (fun x => Nat.factorial x.val) hi),
          Finset.prod_const, hsz u]
    simp only [Nat.multinomial, profileP]
    rw [hszSum, hprod_eq]
  have hmult_pos : 0 < Nat.multinomial Finset.univ (fun i => (sz i).val) :=
    Nat.multinomial_pos _ _
  exact hInnerMultinomialEq ▸ hmult_pos

lemma log_fiber_card_eq_log_factorial_add_core_and_forbidden
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n k t) :
    Real.log ((((Finset.univ (α := Fin n → Fin k)).filter
        (fun π => coloringProfileOf n k π = f)).card : ℝ)) =
      Real.log (Nat.factorial k) + profileCombinatorialLogCore n f +
        ((profileF n (fun u => (f u).val) : ℝ) * Real.log 2) := by
  have hcard_eq := fiber_count_eq n k t f hf
  have hP_pos : 0 < profileP n (fun u => (f u).val) :=
    profileP_pos_of_mem_coloringProfileFinset hf
  have hP_posR : 0 < (profileP n (fun u => (f u).val) : ℝ) := by
    exact_mod_cast hP_pos
  have hfac_posR : 0 < (Nat.factorial k : ℝ) := by
    exact_mod_cast Nat.factorial_pos k
  have hsymm_posR : 0 < (profileSymm n (fun u => (f u).val) : ℝ) := by
    exact_mod_cast Finset.prod_pos (fun u _ => Nat.factorial_pos ((f u).val))
  rw [hcard_eq]
  rw [Real.log_div (mul_ne_zero hfac_posR.ne' hP_posR.ne') hsymm_posR.ne',
      Real.log_mul hfac_posR.ne' hP_posR.ne']
  ring_nf
  rw [profileCombinatorialLogCore]
  ring

lemma log_fiber_card_le_n_log_k
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hk : 0 < k) :
    Real.log ((((Finset.univ (α := Fin n → Fin k)).filter
        (fun π => coloringProfileOf n k π = f)).card : ℝ)) ≤
      (n : ℝ) * Real.log k := by
  by_cases hcard_zero : ((Finset.univ (α := Fin n → Fin k)).filter
      (fun π => coloringProfileOf n k π = f)).card = 0
  · rw [show ((((Finset.univ (α := Fin n → Fin k)).filter
          (fun π => coloringProfileOf n k π = f)).card : ℝ)) = 0 by exact_mod_cast hcard_zero,
        Real.log_zero]
    have hk1R : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hlog_nonneg : 0 ≤ Real.log k := by
      exact Real.log_nonneg hk1R
    have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
    nlinarith
  have hcard_le : (((Finset.univ (α := Fin n → Fin k)).filter
        (fun π => coloringProfileOf n k π = f)).card : ℝ) ≤ k ^ n := by
    have hnat :
        ((Finset.univ (α := Fin n → Fin k)).filter
          (fun π => coloringProfileOf n k π = f)).card ≤ Fintype.card (Fin n → Fin k) :=
      Finset.card_le_univ _
    exact_mod_cast (hnat.trans_eq (by simp [Fintype.card_fun, Fintype.card_fin]))
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hlog_le : Real.log ((((Finset.univ (α := Fin n → Fin k)).filter
        (fun π => coloringProfileOf n k π = f)).card : ℝ)) ≤ Real.log (k ^ n) :=
    Real.log_le_log (by
      have : 0 < ((Finset.univ (α := Fin n → Fin k)).filter
          (fun π => coloringProfileOf n k π = f)).card := Nat.pos_iff_ne_zero.mpr hcard_zero
      exact_mod_cast this) hcard_le
  calc
    Real.log ((((Finset.univ (α := Fin n → Fin k)).filter
        (fun π => coloringProfileOf n k π = f)).card : ℝ)) ≤ Real.log (k ^ n) := hlog_le
    _ = (n : ℝ) * Real.log k := by
      rw [show (k : ℝ) ^ n = (k : ℝ) ^ (n : ℝ) by rw [Real.rpow_natCast]]
      rw [Real.log_rpow hkR]

lemma profileCombinatorialLogCore_le_from_fiber_bound
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n k t)
    (hk : 0 < k) :
    profileCombinatorialLogCore n f ≤
      (n : ℝ) * Real.log k - Real.log (Nat.factorial k) -
        ((profileF n (fun u => (f u).val) : ℝ) * Real.log 2) := by
  have hEq := log_fiber_card_eq_log_factorial_add_core_and_forbidden (n := n) (k := k) (t := t)
    (f := f) hf
  have hLe := log_fiber_card_le_n_log_k (n := n) (k := k) (t := t) (f := f) hk
  rw [hEq] at hLe
  linarith

/-- A coarse upper exponent for the combinatorial core obtained from the trivial
bound on the size of a profile fiber: `fiber ≤ k^n`. This is weaker than the
paper's `cont2` exponent, but it is the first counting-derived explicit upper
surface for `profileCombinatorialLogCore`. -/
noncomputable def profileCombinatorialCoreCoarseUpper
    (n k : ℕ) (f : Fin (n + 1) → Fin (n + 1)) : ℝ :=
  (n : ℝ) * Real.log k - Real.log (Nat.factorial k) -
    ((profileF n (fun u => (f u).val) : ℝ) * Real.log 2)

lemma profileCombinatorialCoreCoarseUpper_eq_of_mem_coloringProfileFinset
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n k t) :
    profileCombinatorialCoreCoarseUpper n k f =
      (n : ℝ) * Real.log k - Real.log (Nat.factorial k) -
        ((profileF n (fun u => (f u).val) : ℝ) * Real.log 2) := by
  rfl

lemma profileCombinatorialCoreCoarseUpper_eq_sum_quadratic
    {n k : ℕ} {f : Fin (n + 1) → Fin (n + 1)} :
    profileCombinatorialCoreCoarseUpper n k f =
      (n : ℝ) * Real.log k - Real.log (Nat.factorial k) -
        ((∑ u : Fin (n + 1),
            ((((u.val * (u.val - 1)) / 2 : ℕ) * (f u).val : ℕ) : ℝ)) * Real.log 2) := by
  rw [profileCombinatorialCoreCoarseUpper, profileF_eq_sum_quadratic]

/-- A coarse one-sided Stirling lower bound for `log(k!)`. This is the first
usable control on the entropy/factorial term inside the live explicit
quadratic comparison route. -/
lemma log_factorial_lower_coarse
    {k : ℕ} (hk : 0 < k) :
    (k : ℝ) * Real.log k - (k : ℝ) + Real.log k / 2 + Real.log (2 * Real.pi) / 2 ≤
      Real.log (Nat.factorial k) := by
  simpa using Stirling.le_log_factorial_stirling (n := k) (Nat.ne_of_gt hk)

/-- Immediate coarse upper bound on the asymmetric entropy/factorial part of
the explicit quadratic comparison. -/
lemma entropy_factorial_term_le_coarse
    {n k : ℕ} (hk : 0 < k) :
    (n : ℝ) * Real.log k - Real.log (Nat.factorial k) ≤
      ((n : ℝ) - (k : ℝ)) * Real.log k + (k : ℝ) -
        Real.log k / 2 - Real.log (2 * Real.pi) / 2 := by
  have hfact : (k : ℝ) * Real.log k - (k : ℝ) + Real.log k / 2 +
      Real.log (2 * Real.pi) / 2 ≤ Real.log (Nat.factorial k) :=
    log_factorial_lower_coarse hk
  linarith

/-- The residual explicit arithmetic target obtained by substituting the coarse
Stirling bound into the entropy/factorial term of the live quadratic
comparison. This is the next honest arithmetic frontier after the initial
Stirling step. -/
noncomputable def safeQuadraticResidualRhs
    (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) : ℝ :=
  (Real.log 2 / 2) *
      ∑ u : Fin (n + 1),
        (((u.val * (f u).val : ℕ) : ℝ) *
          (threshold n - (1 + 2 / Real.log 2) - u.val)) +
    ∑ u : Fin (n + 1), (thresholdFloor n - u.val : ℤ) * (f u).val +
    (n : ℝ) * Real.log (Real.log n) / Real.log n

noncomputable def safeQuadraticResidualSummandRhs
    (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) : ℝ :=
  ∑ u : Fin (n + 1),
    ((f u).val : ℝ) *
      ((Real.log 2 / 2) * u.val * (threshold n - (1 + 2 / Real.log 2) - u.val) +
        (thresholdFloor n - u.val)) +
    (n : ℝ) * Real.log (Real.log n) / Real.log n

noncomputable def safeQuadraticResidualSummandKernel
    (n : ℕ) (u : Fin (n + 1)) : ℝ :=
  (Real.log 2 / 2) * u.val * (threshold n - (1 + 2 / Real.log 2) - u.val) +
    (thresholdFloor n - u.val)

lemma safeQuadraticResidualSummandRhs_eq_sum_kernel
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)} :
    safeQuadraticResidualSummandRhs n f =
      ∑ u : Fin (n + 1), ((f u).val : ℝ) * safeQuadraticResidualSummandKernel n u +
        (n : ℝ) * Real.log (Real.log n) / Real.log n := by
  rfl

lemma safeQuadraticResidualSummandRhs_nonneg_of_kernel_nonneg
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hkernel : ∀ u : Fin (n + 1), 0 ≤ safeQuadraticResidualSummandKernel n u)
    (htail : 0 ≤ (n : ℝ) * Real.log (Real.log n) / Real.log n) :
    0 ≤ safeQuadraticResidualSummandRhs n f := by
  rw [safeQuadraticResidualSummandRhs_eq_sum_kernel]
  have hsum_nonneg :
      0 ≤ ∑ u : Fin (n + 1), ((f u).val : ℝ) * safeQuadraticResidualSummandKernel n u := by
    refine Finset.sum_nonneg ?_
    intro u hu
    exact mul_nonneg (Nat.cast_nonneg _) (hkernel u)
  linarith

lemma safeQuadraticResidualSummandRhs_nonneg_of_sum_kernel_nonneg
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hsum :
      0 ≤ ∑ u : Fin (n + 1), ((f u).val : ℝ) * safeQuadraticResidualSummandKernel n u)
    (htail : 0 ≤ (n : ℝ) * Real.log (Real.log n) / Real.log n) :
    0 ≤ safeQuadraticResidualSummandRhs n f := by
  rw [safeQuadraticResidualSummandRhs_eq_sum_kernel]
  linarith

lemma sum_mul_safeQuadraticResidualSummandKernel_eq
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)} :
    ∑ u : Fin (n + 1), ((f u).val : ℝ) * safeQuadraticResidualSummandKernel n u =
      ∑ u : Fin (n + 1),
        ((f u).val : ℝ) *
          ((Real.log 2 / 2) * u.val * (threshold n - (1 + 2 / Real.log 2) - u.val) +
            (thresholdFloor n - u.val)) := by
  rfl

def SafeProfileCombinatorialQuadraticResidualPointwise
    (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) : Prop :=
  SafeProfileUpperBoundRegime n f →
    ((n : ℝ) - (∑ u : Fin (n + 1), (f u).val : ℕ)) *
        Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) +
      (∑ u : Fin (n + 1), (f u).val : ℕ) -
      Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) / 2 -
      Real.log (2 * Real.pi) / 2 -
      ((∑ u : Fin (n + 1),
          ((((u.val * (u.val - 1)) / 2 : ℕ) * (f u).val : ℕ) : ℝ)) * Real.log 2)
    ≤ safeQuadraticResidualRhs n f

lemma safeQuadraticResidualPointwise_of_tailNonpos_and_rhsNonneg
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hnonpos :
      SafeProfileUpperBoundRegime n f →
        ((n : ℝ) - (∑ u : Fin (n + 1), (f u).val : ℕ)) *
            Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) +
          (∑ u : Fin (n + 1), (f u).val : ℕ) -
          Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) / 2 -
          Real.log (2 * Real.pi) / 2 -
          ((∑ u : Fin (n + 1),
              ((((u.val * (u.val - 1)) / 2 : ℕ) * (f u).val : ℕ) : ℝ)) * Real.log 2)
        ≤ 0)
    (hrhs_nonneg : 0 ≤ safeQuadraticResidualRhs n f) :
    SafeProfileCombinatorialQuadraticResidualPointwise n f := by
  intro hreg
  exact (hnonpos hreg).trans hrhs_nonneg

lemma safeQuadraticTailNonpos_of_residualPointwise_and_rhsNonpos
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hres : SafeProfileCombinatorialQuadraticResidualPointwise n f)
    (hrhs_nonpos : safeQuadraticResidualRhs n f ≤ 0) :
    SafeProfileUpperBoundRegime n f →
      ((n : ℝ) - (∑ u : Fin (n + 1), (f u).val : ℕ)) *
          Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) +
        (∑ u : Fin (n + 1), (f u).val : ℕ) -
        Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) / 2 -
        Real.log (2 * Real.pi) / 2 -
        ((∑ u : Fin (n + 1),
            ((((u.val * (u.val - 1)) / 2 : ℕ) * (f u).val : ℕ) : ℝ)) * Real.log 2)
      ≤ 0 := by
  intro hreg
  exact (hres hreg).trans hrhs_nonpos

/-- The same residual target with the integer remainder term rewritten into the
scalar form `(thresholdFloor n) * k - n`. This is a cleaner surface for the
next arithmetic attack after removing the Stirling and raw-sum noise. -/
def SafeProfileCombinatorialQuadraticResidualScalarPointwise
    (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) : Prop :=
  SafeProfileUpperBoundRegime n f →
    ((n : ℝ) - (∑ u : Fin (n + 1), (f u).val : ℕ)) *
        Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) +
      (∑ u : Fin (n + 1), (f u).val : ℕ) -
      Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) / 2 -
      Real.log (2 * Real.pi) / 2 -
      ((∑ u : Fin (n + 1),
          ((((u.val * (u.val - 1)) / 2 : ℕ) * (f u).val : ℕ) : ℝ)) * Real.log 2)
    ≤
      (Real.log 2 / 2) *
        ∑ u : Fin (n + 1),
          (((u.val * (f u).val : ℕ) : ℝ) *
            (threshold n - (1 + 2 / Real.log 2) - u.val)) +
      (thresholdFloor n : ℝ) * (∑ u : Fin (n + 1), (f u).val : ℕ) - n +
      (n : ℝ) * Real.log (Real.log n) / Real.log n

/-- A further-compressed scalar residual target: the weighted-plus-floor part of
the RHS has already been reduced to an explicit linear expression in `n` and
`k = ∑_u f_u`. This is the next honest scalar frontier after the summand-level
compression step. -/
def SafeProfileCombinatorialQuadraticResidualLinearPointwise
    (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) : Prop :=
  SafeProfileUpperBoundRegime n f →
    ((n : ℝ) - (∑ u : Fin (n + 1), (f u).val : ℕ)) *
        Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) +
      (∑ u : Fin (n + 1), (f u).val : ℕ) -
      Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) / 2 -
      Real.log (2 * Real.pi) / 2 -
      ((∑ u : Fin (n + 1),
          ((((u.val * (u.val - 1)) / 2 : ℕ) * (f u).val : ℕ) : ℝ)) * Real.log 2)
      ≤
      -(2 * Real.log 2) * n +
        ((2 / Real.log 2) - 3) * (∑ u : Fin (n + 1), (f u).val : ℕ) +
        (n : ℝ) * Real.log (Real.log n) / Real.log n

noncomputable def safeQuadraticResidualLinearRhs
    (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) : ℝ :=
  -(2 * Real.log 2) * n +
    ((2 / Real.log 2) - 3) * (∑ u : Fin (n + 1), (f u).val : ℕ) +
    (n : ℝ) * Real.log (Real.log n) / Real.log n

noncomputable def safeQuadraticResidualTailRhs (n : ℕ) : ℝ :=
  -(2 * Real.log 2) * n + (n : ℝ) * Real.log (Real.log n) / Real.log n

lemma safeQuadraticResidualTailRhs_eq
    (n : ℕ) :
    safeQuadraticResidualTailRhs n =
      (n : ℝ) * (Real.log (Real.log n) / Real.log n - 2 * Real.log 2) := by
  unfold safeQuadraticResidualTailRhs
  ring

lemma safeQuadraticResidualTailRhs_nonpos_of_loglog_div_le
    {n : ℕ}
    (hloglog : Real.log (Real.log n) / Real.log n ≤ 2 * Real.log 2) :
    safeQuadraticResidualTailRhs n ≤ 0 := by
  rw [safeQuadraticResidualTailRhs_eq]
  have hfactor_nonpos :
      Real.log (Real.log n) / Real.log n - 2 * Real.log 2 ≤ 0 := by
    linarith
  have hn_nonneg : (0 : ℝ) ≤ n := by positivity
  exact mul_nonpos_of_nonneg_of_nonpos hn_nonneg hfactor_nonpos

lemma loglog_div_log_le_two_log_two_of_three_le
    {n : ℕ} (hn : 3 ≤ n) :
    Real.log (Real.log n) / Real.log n ≤ 2 * Real.log 2 := by
  have hnR_pos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 3) hn)
  have hthreeR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog_ge_one : (1 : ℝ) ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hnR_pos]
    exact le_trans Real.exp_one_lt_three.le hthreeR
  have hlog_nonneg : (0 : ℝ) ≤ Real.log n := le_trans (by norm_num) hlog_ge_one
  have hlog_pos : (0 : ℝ) < Real.log n := lt_of_lt_of_le (by norm_num) hlog_ge_one
  have hloglog_le_log : Real.log (Real.log n) ≤ Real.log n := by
    exact Real.log_le_self hlog_nonneg
  have hdiv_le_one : Real.log (Real.log n) / Real.log n ≤ 1 := by
    rw [div_le_iff₀ hlog_pos]
    nlinarith
  have hone_le_two_log_two : (1 : ℝ) ≤ 2 * Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  exact hdiv_le_one.trans hone_le_two_log_two

lemma loglog_div_log_le_one_of_three_le
    {n : ℕ} (hn : 3 ≤ n) :
    Real.log (Real.log n) / Real.log n ≤ 1 := by
  have hnR_pos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 3) hn)
  have hlog_ge_one : (1 : ℝ) ≤ Real.log n := by
    have hthreeR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    rw [Real.le_log_iff_exp_le hnR_pos]
    exact le_trans Real.exp_one_lt_three.le hthreeR
  have hlog_nonneg : (0 : ℝ) ≤ Real.log n := le_trans (by norm_num) hlog_ge_one
  have hlog_pos : (0 : ℝ) < Real.log n := lt_of_lt_of_le (by norm_num) hlog_ge_one
  have hloglog_le_log : Real.log (Real.log n) ≤ Real.log n := by
    exact Real.log_le_self hlog_nonneg
  rw [div_le_iff₀ hlog_pos]
  linarith

lemma safeProfileConcreteRemainderPointwise_of_three_le_of_threshold_nonneg
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hn : 3 ≤ n)
    (hf : f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1))
    (hth_nonneg : 0 ≤ threshold n) :
    SafeProfileConcreteRemainderPointwise n f := by
  intro hreg
  let k : ℕ := ∑ u : Fin (n + 1), (f u).val
  have hsum_le :
      ∑ u : Fin (n + 1), ((f u).val : ℝ) * (thresholdFloor n - u.val) ≤
        ((2 / Real.log 2) - 3) * k := by
    have hn_pos : 0 < n := lt_of_lt_of_le (by decide : 0 < 3) hn
    simpa [k] using
      profileUpperBoundRegime_sum_thresholdFloor_minus_u_le_of_safeUpperBoundRegime
        (n := n) (k := k) (t := thresholdFloor n - 1) (f := f) hn_pos hf hth_nonneg hreg
  have hk_nonneg : (0 : ℝ) ≤ k := by positivity
  have hscalar_nonpos : (thresholdFloor n : ℝ) * k - n ≤ 0 := by
    calc
      (thresholdFloor n : ℝ) * k - n
          = ∑ u : Fin (n + 1), ((f u).val : ℝ) * (thresholdFloor n - u.val) := by
              simpa [k] using
                profileRemainder_scalar_term_eq_sum_thresholdFloor_minus_u_of_mem
                  (n := n) (k := k) (t := thresholdFloor n - 1) (f := f) hf
      _ ≤ ((2 / Real.log 2) - 3) * k := hsum_le
      _ ≤ 0 := by
            have hkCoeff_nonpos : ((2 / Real.log 2) - 3 : ℝ) ≤ 0 := by
              have hlog : (2 / 3 : ℝ) < Real.log 2 := by
                linarith [Real.log_two_gt_d9]
              have hlog_pos : 0 < Real.log 2 := by positivity
              have hdiv_lt : (2 / Real.log 2 : ℝ) < 3 := by
                rw [div_lt_iff₀ hlog_pos]
                linarith
              linarith
            nlinarith
  have htail_le :
      (n : ℝ) * Real.log (Real.log n) / Real.log n ≤ safeProfileRemainderBudget * n := by
    have hdiv_le : Real.log (Real.log n) / Real.log n ≤ 1 :=
      loglog_div_log_le_one_of_three_le hn
    have hn_nonneg : (0 : ℝ) ≤ n := by positivity
    have hmul := mul_le_mul_of_nonneg_left hdiv_le hn_nonneg
    simpa [safeProfileRemainderBudget, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
  change profileRemainder n f ≤ safeProfileRemainderBudget * n
  rw [profileRemainder]
  have hint :
      ((∑ u : Fin (n + 1), (thresholdFloor n - u.val : ℤ) * (f u).val : ℤ) : ℝ) =
        (thresholdFloor n : ℝ) * k - n := by
    simpa [k] using
      profileRemainder_integer_term_eq_of_mem_coloringProfileFinset_real
        (n := n) (k := k) (t := thresholdFloor n - 1) (f := f) hf
  rw [hint]
  linarith

lemma safeProfileConcreteRemainderConditionalTheoremTarget_true :
    SafeProfileConcreteRemainderConditionalTheoremTarget := by
  intro n f hf hn hth_nonneg
  exact safeProfileConcreteRemainderPointwise_of_three_le_of_threshold_nonneg hn hf hth_nonneg

/-- threshold n ≥ 0 for n ≥ 3. Key: for L = log n / log 2 and c = log 2,
    c*L - log(L) ≥ 1 + log(c) (from add_one_le_exp applied to log(L*c)),
    then threshold n ≥ (4 + 2*log(c) - c)/c ≥ (4 - 2 - 1)/c = 1/c > 0. -/
private lemma threshold_nonneg_of_three_le {n : ℕ} (hn : 3 ≤ n) : 0 ≤ threshold n := by
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt hlog2_pos
  have hlog2_gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  -- 2 ≤ exp 1, hence log 2 ≤ log(exp 1) = 1
  have h2_le_exp1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hlog2_le1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) h2_le_exp1
    rwa [Real.log_exp] at h
  -- log n > 0 for n ≥ 3
  have hn_gt1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hn
  have hlogn_pos : (0 : ℝ) < Real.log n := Real.log_pos hn_gt1
  -- L = log n / log 2 > 0
  have hL_pos : (0 : ℝ) < Real.log n / Real.log 2 := div_pos hlogn_pos hlog2_pos
  -- log(exp 1/2) = 1 - log 2
  have hlog12 : Real.log (Real.exp 1 / 2) = 1 - Real.log 2 := by
    rw [Real.log_div (Real.exp_ne_zero 1) (by norm_num), Real.log_exp]
  -- Key bound: log(L) ≤ log 2 * L - 1 - log(log 2)
  -- Proof: log(L*log2) = log(L) + log(log2) ≤ L*log2 - 1 (from add_one_le_exp)
  have hmin : Real.log (Real.log n / Real.log 2) ≤
      Real.log 2 * (Real.log n / Real.log 2) - 1 - Real.log (Real.log 2) := by
    have hLc_pos : (0 : ℝ) < Real.log n / Real.log 2 * Real.log 2 := by positivity
    have h_add1 : Real.log (Real.log n / Real.log 2 * Real.log 2) ≤
        Real.log n / Real.log 2 * Real.log 2 - 1 := by
      have := Real.add_one_le_exp (Real.log (Real.log n / Real.log 2 * Real.log 2))
      rw [Real.exp_log hLc_pos] at this; linarith
    have h_split : Real.log (Real.log n / Real.log 2 * Real.log 2) =
        Real.log (Real.log n / Real.log 2) + Real.log (Real.log 2) :=
      Real.log_mul (ne_of_gt hL_pos) hlog2_ne
    linarith [mul_comm (Real.log n / Real.log 2) (Real.log 2)]
  -- log(log 2) ≥ -1: exp(-1) = 1/exp(1) ≤ 1/2 < log 2
  have hloglog2_ge : (-1 : ℝ) ≤ Real.log (Real.log 2) := by
    have hexp_inv : Real.exp (-1 : ℝ) = (Real.exp 1)⁻¹ := Real.exp_neg 1
    have hexp_le_log2 : Real.exp (-1 : ℝ) ≤ Real.log 2 := by
      rw [hexp_inv]
      have hexp1_inv : (Real.exp 1)⁻¹ ≤ 1 / 2 := by
        have h2inv : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
        rw [← h2inv]
        exact inv_anti₀ (by norm_num) h2_le_exp1
      linarith
    calc (-1 : ℝ) = Real.log (Real.exp (-1)) := (Real.log_exp (-1)).symm
      _ ≤ Real.log (Real.log 2) := Real.log_le_log (Real.exp_pos _) hexp_le_log2
  -- 4 + 2*log(log2) - log2 ≥ 0 (using loglog2 ≥ -1, log2 ≤ 1)
  have hconst_pos : (0 : ℝ) ≤ 4 + 2 * Real.log (Real.log 2) - Real.log 2 := by linarith
  -- Unfold threshold, substitute hlog12, and bound
  unfold threshold
  simp only [hlog12]
  -- Goal: 0 ≤ 2 * (log n / log 2) - 2 * (log(log n / log 2) / log 2) + 2 * ((1 - log 2) / log 2) + 1
  have expand : 2 * (Real.log n / Real.log 2) -
      2 * (Real.log (Real.log n / Real.log 2) / Real.log 2) +
      2 * ((1 - Real.log 2) / Real.log 2) + 1 =
      (2 * Real.log 2 * (Real.log n / Real.log 2) -
       2 * Real.log (Real.log n / Real.log 2) + 2 - Real.log 2) / Real.log 2 := by
    field_simp; ring
  rw [expand]
  apply div_nonneg _ (le_of_lt hlog2_pos)
  linarith

/-- For n ≤ 2, SafeProfileUpperBoundRegime is vacuous:
    the regime requires threshold n + (3 - 2/log2) < n/k, but this quantity equals 2 (n=0,1)
    or 4 (n=2), while n/k ≤ n ≤ 2 (resp. 2/k for n=2 gives ≤2 < 4). -/
private lemma safeUpperBoundRegime_false_of_lt_three
    {n : ℕ} (hn : n < 3)
    {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1)) :
    ¬ SafeProfileUpperBoundRegime n f := by
  intro hreg
  have hreg2 := (profileAverageClassSize_lt_of_upperBoundRegime hreg :
    threshold n - (1 + 2 / Real.log 2) + safeProfileUpperBoundBuffer <
      profileAverageClassSize n f)
  have hlog12 : Real.log (Real.exp 1 / 2) = 1 - Real.log 2 := by
    rw [Real.log_div (Real.exp_ne_zero 1) (by norm_num), Real.log_exp]
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  simp only [safeProfileUpperBoundBuffer] at hreg2
  interval_cases n
  -- n = 0
  · have hav : profileAverageClassSize 0 f = 0 := by
      simp [profileAverageClassSize]
    have h_thresh : threshold 0 - (1 + 2 / Real.log 2) + 4 = 2 := by
      unfold threshold
      simp only [Nat.cast_zero, Real.log_zero, zero_div, Real.log_zero, mul_zero, sub_zero]
      rw [hlog12]; field_simp; ring
    rw [hav] at hreg2; linarith
  -- n = 1
  · have hk_pos : 0 < ∑ u : Fin 2, (f u).val :=
      profileColorCount_pos_of_mem_coloringProfileFinset (by norm_num) hf
    have hav_le : profileAverageClassSize 1 f ≤ 1 := by
      unfold profileAverageClassSize
      simp only [Nat.cast_one]
      rw [div_le_one (by exact_mod_cast hk_pos)]
      exact_mod_cast hk_pos
    have h_thresh : threshold 1 - (1 + 2 / Real.log 2) + 4 = 2 := by
      unfold threshold
      simp only [Nat.cast_one, Real.log_one, zero_div, Real.log_zero, mul_zero, sub_zero]
      rw [hlog12]; field_simp; ring
    linarith
  -- n = 2
  · have hk_pos : 0 < ∑ u : Fin 3, (f u).val :=
      profileColorCount_pos_of_mem_coloringProfileFinset (by norm_num) hf
    have hav_le : profileAverageClassSize 2 f ≤ 2 := by
      unfold profileAverageClassSize
      simp only [Nat.cast_ofNat]
      apply div_le_of_le_mul₀ (by exact_mod_cast Nat.zero_le _) (by norm_num)
      exact_mod_cast Nat.le_mul_of_pos_right _ hk_pos
    have h_thresh : threshold 2 - (1 + 2 / Real.log 2) + 4 = 4 := by
      unfold threshold
      simp only [Nat.cast_ofNat]
      have hlog2_div : Real.log 2 / Real.log 2 = 1 := div_self (ne_of_gt hlog2_pos)
      simp only [hlog2_div, Real.log_one, zero_div, mul_one, mul_zero, sub_zero]
      rw [hlog12]; field_simp; ring
    linarith

/-- SafeProfileConcreteRemainderTheoremTarget holds unconditionally:
    for n < 3 the regime is vacuous; for n ≥ 3 use the conditional theorem + threshold_nonneg. -/
lemma safeProfileConcreteRemainderTheoremTarget_true :
    SafeProfileConcreteRemainderTheoremTarget := by
  intro n f hf
  rcases Nat.lt_or_ge n 3 with hn | hn
  · -- n < 3: regime is vacuous, so implication holds trivially
    intro hreg
    exact absurd hreg (safeUpperBoundRegime_false_of_lt_three hn hf)
  · -- n ≥ 3: use conditional theorem with threshold_nonneg_of_three_le
    exact safeProfileConcreteRemainderConditionalTheoremTarget_true n f hf hn
      (threshold_nonneg_of_three_le hn)

lemma safeQuadraticResidual_kCoeff_neg : ((2 / Real.log 2) - 3 : ℝ) < 0 := by
  have hlog_gt : (2 / 3 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlog_pos : 0 < Real.log 2 := by positivity
  have hdiv_lt : (2 / Real.log 2 : ℝ) < 3 := by
    rw [div_lt_iff₀ hlog_pos]
    nlinarith
  linarith

lemma safeQuadraticResidual_kCoeff_nonpos : ((2 / Real.log 2) - 3 : ℝ) ≤ 0 :=
  safeQuadraticResidual_kCoeff_neg.le

lemma safeQuadraticResidualLinearPointwise_iff
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)} :
    SafeProfileCombinatorialQuadraticResidualLinearPointwise n f ↔
      (SafeProfileUpperBoundRegime n f →
        ((n : ℝ) - (∑ u : Fin (n + 1), (f u).val : ℕ)) *
            Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) +
          (∑ u : Fin (n + 1), (f u).val : ℕ) -
          Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) / 2 -
          Real.log (2 * Real.pi) / 2 -
          ((∑ u : Fin (n + 1),
              ((((u.val * (u.val - 1)) / 2 : ℕ) * (f u).val : ℕ) : ℝ)) * Real.log 2)
        ≤ safeQuadraticResidualLinearRhs n f) := by
  rfl

lemma safeQuadraticResidualLinearPointwise_apply
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hlin : SafeProfileCombinatorialQuadraticResidualLinearPointwise n f)
    (hreg : SafeProfileUpperBoundRegime n f) :
    ((n : ℝ) - (∑ u : Fin (n + 1), (f u).val : ℕ)) *
        Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) +
      (∑ u : Fin (n + 1), (f u).val : ℕ) -
      Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) / 2 -
      Real.log (2 * Real.pi) / 2 -
      ((∑ u : Fin (n + 1),
          ((((u.val * (u.val - 1)) / 2 : ℕ) * (f u).val : ℕ) : ℝ)) * Real.log 2)
    ≤ safeQuadraticResidualLinearRhs n f :=
  hlin hreg

lemma safeQuadraticResidualLinearRhs_le_tail
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hkCoeff_nonpos : ((2 / Real.log 2) - 3 : ℝ) ≤ 0) :
    safeQuadraticResidualLinearRhs n f ≤ safeQuadraticResidualTailRhs n := by
  unfold safeQuadraticResidualLinearRhs safeQuadraticResidualTailRhs
  have hkterm :
      ((2 / Real.log 2) - 3 : ℝ) * (∑ u : Fin (n + 1), (f u).val : ℕ) ≤ 0 := by
    have hsum_nonneg : (0 : ℝ) ≤ (∑ u : Fin (n + 1), (f u).val : ℕ) := by positivity
    nlinarith
  linarith

lemma safeQuadraticResidualTailPointwise_of_linear
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hkCoeff_nonpos : ((2 / Real.log 2) - 3 : ℝ) ≤ 0)
    (hlin : SafeProfileCombinatorialQuadraticResidualLinearPointwise n f) :
    SafeProfileUpperBoundRegime n f →
      ((n : ℝ) - (∑ u : Fin (n + 1), (f u).val : ℕ)) *
          Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) +
        (∑ u : Fin (n + 1), (f u).val : ℕ) -
        Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) / 2 -
        Real.log (2 * Real.pi) / 2 -
        ((∑ u : Fin (n + 1),
            ((((u.val * (u.val - 1)) / 2 : ℕ) * (f u).val : ℕ) : ℝ)) * Real.log 2)
      ≤ safeQuadraticResidualTailRhs n := by
  intro hreg
  exact (safeQuadraticResidualLinearPointwise_apply hlin hreg).trans
    (safeQuadraticResidualLinearRhs_le_tail hkCoeff_nonpos)

lemma safeQuadraticResidualTailPointwise_of_linear_unconditional
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hlin : SafeProfileCombinatorialQuadraticResidualLinearPointwise n f) :
    SafeProfileUpperBoundRegime n f →
      ((n : ℝ) - (∑ u : Fin (n + 1), (f u).val : ℕ)) *
          Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) +
        (∑ u : Fin (n + 1), (f u).val : ℕ) -
        Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) / 2 -
        Real.log (2 * Real.pi) / 2 -
        ((∑ u : Fin (n + 1),
            ((((u.val * (u.val - 1)) / 2 : ℕ) * (f u).val : ℕ) : ℝ)) * Real.log 2)
      ≤ safeQuadraticResidualTailRhs n :=
  safeQuadraticResidualTailPointwise_of_linear safeQuadraticResidual_kCoeff_nonpos hlin

set_option maxHeartbeats 400000 in
lemma safeQuadraticResidual_of_scalarResidual
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1))
    (hscal : SafeProfileCombinatorialQuadraticResidualScalarPointwise n f) :
    SafeProfileCombinatorialQuadraticResidualPointwise n f := by
  dsimp [SafeProfileCombinatorialQuadraticResidualPointwise]
  intro hreg
  have hscal' : ((n : ℝ) - (∑ u : Fin (n + 1), (f u).val : ℕ)) *
        Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) +
      (∑ u : Fin (n + 1), (f u).val : ℕ) -
      Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) / 2 -
      Real.log (2 * Real.pi) / 2 -
      ((∑ u : Fin (n + 1),
          ((((u.val * (u.val - 1)) / 2 : ℕ) * (f u).val : ℕ) : ℝ)) * Real.log 2)
    ≤
      (Real.log 2 / 2) *
        ∑ u : Fin (n + 1),
          (((u.val * (f u).val : ℕ) : ℝ) *
            (threshold n - (1 + 2 / Real.log 2) - u.val)) +
      (thresholdFloor n : ℝ) * (∑ u : Fin (n + 1), (f u).val : ℕ) - n +
      (n : ℝ) * Real.log (Real.log n) / Real.log n := by
    exact hscal hreg
  have hint :
      ((∑ u : Fin (n + 1), (thresholdFloor n - u.val : ℤ) * (f u).val : ℤ) : ℝ) =
        (thresholdFloor n : ℝ) * (∑ u : Fin (n + 1), (f u).val : ℕ) - n :=
    profileRemainder_integer_term_eq_of_mem_coloringProfileFinset_real hf
  unfold safeQuadraticResidualRhs
  rw [hint]
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hscal'

lemma weightedShift_plus_scalarRemainder_eq_sum
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n k t) :
    (Real.log 2 / 2) *
        ∑ u : Fin (n + 1),
          (((u.val * (f u).val : ℕ) : ℝ) *
            (threshold n - (1 + 2 / Real.log 2) - u.val)) +
      ((thresholdFloor n : ℝ) * k - n)
      =
    ∑ u : Fin (n + 1),
      ((f u).val : ℝ) *
        ((Real.log 2 / 2) * u.val * (threshold n - (1 + 2 / Real.log 2) - u.val) +
          (thresholdFloor n - u.val)) := by
  have hk :
      (∑ u : Fin (n + 1), (f u).val : ℕ) = k :=
    profileColorCount_eq_of_mem_coloringProfileFinset hf
  have hn :
      (∑ u : Fin (n + 1), u.val * (f u).val : ℕ) = n :=
    profileVertexWeight_eq_of_mem_coloringProfileFinset hf
  have hkR :
      (k : ℝ) = (∑ u : Fin (n + 1), ((f u).val : ℝ)) := by
    exact_mod_cast hk.symm
  have hnR :
      (n : ℝ) = (∑ u : Fin (n + 1), ((u.val * (f u).val : ℕ) : ℝ)) := by
    exact_mod_cast hn.symm
  let a : Fin (n + 1) → ℝ := fun u =>
    (Real.log 2 / 2) *
      (((u.val * (f u).val : ℕ) : ℝ) *
        (threshold n - (1 + 2 / Real.log 2) - u.val))
  let b : Fin (n + 1) → ℝ := fun u =>
    (thresholdFloor n : ℝ) * ((f u).val : ℝ) - ((u.val * (f u).val : ℕ) : ℝ)
  have hsub :
      (∑ u : Fin (n + 1), b u) =
        (∑ u : Fin (n + 1), (thresholdFloor n : ℝ) * ((f u).val : ℝ)) -
          (∑ u : Fin (n + 1), ((u.val * (f u).val : ℕ) : ℝ)) := by
    simp [b, Finset.sum_sub_distrib]
  calc
    (Real.log 2 / 2) *
        ∑ u : Fin (n + 1),
          (((u.val * (f u).val : ℕ) : ℝ) *
            (threshold n - (1 + 2 / Real.log 2) - u.val)) +
      ((thresholdFloor n : ℝ) * k - n)
        =
      (Real.log 2 / 2) *
        ∑ u : Fin (n + 1),
          (((u.val * (f u).val : ℕ) : ℝ) *
            (threshold n - (1 + 2 / Real.log 2) - u.val)) +
      ((thresholdFloor n : ℝ) * (∑ u : Fin (n + 1), ((f u).val : ℝ)) -
        (∑ u : Fin (n + 1), ((u.val * (f u).val : ℕ) : ℝ))) := by
          rw [hkR, hnR]
    _ =
      (∑ u : Fin (n + 1), a u) +
        ((∑ u : Fin (n + 1), (thresholdFloor n : ℝ) * ((f u).val : ℝ)) -
          (∑ u : Fin (n + 1), ((u.val * (f u).val : ℕ) : ℝ))) := by
            simp [a, Finset.mul_sum]
    _ =
      (∑ u : Fin (n + 1), a u) + ∑ u : Fin (n + 1), b u := by
            rw [← hsub]
    _ = ∑ u : Fin (n + 1), (a u + b u) := by
            rw [← Finset.sum_add_distrib]
    _ =
      ∑ u : Fin (n + 1),
        ((f u).val : ℝ) *
          ((Real.log 2 / 2) * u.val * (threshold n - (1 + 2 / Real.log 2) - u.val) +
            (thresholdFloor n - u.val)) := by
            refine Finset.sum_congr rfl ?_
            intro u hu
            simp [a, b]
            ring

lemma safeQuadraticResidualRhs_eq_summandRhs_of_mem
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1)) :
    safeQuadraticResidualRhs n f = safeQuadraticResidualSummandRhs n f := by
  unfold safeQuadraticResidualRhs safeQuadraticResidualSummandRhs
  rw [profileRemainder_integer_term_eq_of_mem_coloringProfileFinset_real hf]
  rw [weightedShift_plus_scalarRemainder_eq_sum
    (n := n) (k := ∑ u : Fin (n + 1), (f u).val) (t := thresholdFloor n - 1) (f := f) hf]

def SafeProfileCombinatorialQuadraticResidualSummandRhsNonnegTheoremTarget : Prop :=
  ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
    f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
    3 ≤ n →
    0 ≤ threshold n →
    0 ≤ safeQuadraticResidualSummandRhs n f

def SafeProfileCombinatorialQuadraticResidualSummandRhsNonposTheoremTarget : Prop :=
  ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
    f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
    3 ≤ n →
    0 ≤ threshold n →
    SafeProfileUpperBoundRegime n f →
    safeQuadraticResidualSummandRhs n f ≤ 0

def SafeProfileCombinatorialQuadraticResidualRhsNonposTheoremTarget : Prop :=
  ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
    f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
    3 ≤ n →
    0 ≤ threshold n →
    SafeProfileUpperBoundRegime n f →
    safeQuadraticResidualRhs n f ≤ 0

lemma safeQuadraticResidualRhsNonneg_of_summandRhsNonnegTheoremTarget
    (hsum : SafeProfileCombinatorialQuadraticResidualSummandRhsNonnegTheoremTarget)
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1))
    (hn : 3 ≤ n)
    (hth_nonneg : 0 ≤ threshold n) :
    0 ≤ safeQuadraticResidualRhs n f := by
  rw [safeQuadraticResidualRhs_eq_summandRhs_of_mem hf]
  exact hsum n f hf hn hth_nonneg

lemma safeQuadraticResidualRhs_nonpos_of_summandRhs_nonpos
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1))
    (hsum_nonpos : safeQuadraticResidualSummandRhs n f ≤ 0) :
    safeQuadraticResidualRhs n f ≤ 0 := by
  rw [safeQuadraticResidualRhs_eq_summandRhs_of_mem hf]
  exact hsum_nonpos

set_option maxHeartbeats 400000 in
lemma safeQuadraticResidualSummand_of_scalarResidual
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1))
    (hscal : SafeProfileCombinatorialQuadraticResidualScalarPointwise n f) :
    SafeProfileUpperBoundRegime n f →
      ((n : ℝ) - (∑ u : Fin (n + 1), (f u).val : ℕ)) *
          Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) +
        (∑ u : Fin (n + 1), (f u).val : ℕ) -
        Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) / 2 -
        Real.log (2 * Real.pi) / 2 -
        ((∑ u : Fin (n + 1),
            ((((u.val * (u.val - 1)) / 2 : ℕ) * (f u).val : ℕ) : ℝ)) * Real.log 2)
      ≤
        ∑ u : Fin (n + 1),
          ((f u).val : ℝ) *
            ((Real.log 2 / 2) * u.val * (threshold n - (1 + 2 / Real.log 2) - u.val) +
              (thresholdFloor n - u.val)) +
        (n : ℝ) * Real.log (Real.log n) / Real.log n := by
  intro hreg
  have hscal' := hscal hreg
  rw [← weightedShift_plus_scalarRemainder_eq_sum
    (n := n) (k := ∑ u : Fin (n + 1), (f u).val) (t := thresholdFloor n - 1) (f := f) hf]
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hscal'

lemma safeQuadraticResidualLinear_of_scalarResidual
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hn : 0 < n)
    (hf : f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1))
    (hth_nonneg : 0 ≤ threshold n)
    (hscal : SafeProfileCombinatorialQuadraticResidualScalarPointwise n f) :
    SafeProfileCombinatorialQuadraticResidualLinearPointwise n f := by
  intro hreg
  have hsummand :
      ((n : ℝ) - (∑ u : Fin (n + 1), (f u).val : ℕ)) *
          Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) +
        (∑ u : Fin (n + 1), (f u).val : ℕ) -
        Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) / 2 -
        Real.log (2 * Real.pi) / 2 -
        ((∑ u : Fin (n + 1),
            ((((u.val * (u.val - 1)) / 2 : ℕ) * (f u).val : ℕ) : ℝ)) * Real.log 2)
      ≤
        ∑ u : Fin (n + 1),
          ((f u).val : ℝ) *
            ((Real.log 2 / 2) * u.val * (threshold n - (1 + 2 / Real.log 2) - u.val) +
              (thresholdFloor n - u.val)) +
        (n : ℝ) * Real.log (Real.log n) / Real.log n :=
    safeQuadraticResidualSummand_of_scalarResidual hf hscal hreg
  have hsum_le :
      ∑ u : Fin (n + 1),
        ((f u).val : ℝ) *
          ((Real.log 2 / 2) * u.val * (threshold n - (1 + 2 / Real.log 2) - u.val) +
            (thresholdFloor n - u.val))
      ≤
        -(2 * Real.log 2) * n +
          ((2 / Real.log 2) - 3) * (∑ u : Fin (n + 1), (f u).val : ℕ) := by
    simpa using safeWeightedShiftPlusThresholdFloorSum_le
      (n := n)
      (k := ∑ u : Fin (n + 1), (f u).val)
      (t := thresholdFloor n - 1)
      (f := f)
      hn hf hth_nonneg hreg
  linarith

lemma safeQuadraticResidualLinear_of_scalarResidual_apply
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hn : 0 < n)
    (hf : f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1))
    (hth_nonneg : 0 ≤ threshold n)
    (hscal : SafeProfileCombinatorialQuadraticResidualScalarPointwise n f)
    (hreg : SafeProfileUpperBoundRegime n f) :
      ((n : ℝ) - (∑ u : Fin (n + 1), (f u).val : ℕ)) *
          Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) +
        (∑ u : Fin (n + 1), (f u).val : ℕ) -
        Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) / 2 -
        Real.log (2 * Real.pi) / 2 -
        ((∑ u : Fin (n + 1),
            ((((u.val * (u.val - 1)) / 2 : ℕ) * (f u).val : ℕ) : ℝ)) * Real.log 2)
      ≤
        -(2 * Real.log 2) * n +
          ((2 / Real.log 2) - 3) * (∑ u : Fin (n + 1), (f u).val : ℕ) +
          (n : ℝ) * Real.log (Real.log n) / Real.log n := by
  exact safeQuadraticResidualLinear_of_scalarResidual hn hf hth_nonneg hscal hreg

def SafeProfileCombinatorialQuadraticResidualLinearTheoremTarget : Prop :=
  ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
    f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
    0 < n →
    0 ≤ threshold n →
    SafeProfileCombinatorialQuadraticResidualLinearPointwise n f

def SafeProfileCombinatorialQuadraticResidualTailPointwise
    (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) : Prop :=
  SafeProfileUpperBoundRegime n f →
    ((n : ℝ) - (∑ u : Fin (n + 1), (f u).val : ℕ)) *
        Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) +
      (∑ u : Fin (n + 1), (f u).val : ℕ) -
      Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) / 2 -
      Real.log (2 * Real.pi) / 2 -
      ((∑ u : Fin (n + 1),
          ((((u.val * (u.val - 1)) / 2 : ℕ) * (f u).val : ℕ) : ℝ)) * Real.log 2)
    ≤ safeQuadraticResidualTailRhs n

lemma safeQuadraticResidualTailPointwise_iff
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)} :
    SafeProfileCombinatorialQuadraticResidualTailPointwise n f ↔
      (SafeProfileUpperBoundRegime n f →
        ((n : ℝ) - (∑ u : Fin (n + 1), (f u).val : ℕ)) *
            Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) +
          (∑ u : Fin (n + 1), (f u).val : ℕ) -
          Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) / 2 -
          Real.log (2 * Real.pi) / 2 -
          ((∑ u : Fin (n + 1),
              ((((u.val * (u.val - 1)) / 2 : ℕ) * (f u).val : ℕ) : ℝ)) * Real.log 2)
        ≤ safeQuadraticResidualTailRhs n) := by
  rfl

lemma safeQuadraticResidualTailPointwise_apply
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (htail : SafeProfileCombinatorialQuadraticResidualTailPointwise n f)
    (hreg : SafeProfileUpperBoundRegime n f) :
    ((n : ℝ) - (∑ u : Fin (n + 1), (f u).val : ℕ)) *
        Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) +
      (∑ u : Fin (n + 1), (f u).val : ℕ) -
      Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) / 2 -
      Real.log (2 * Real.pi) / 2 -
      ((∑ u : Fin (n + 1),
          ((((u.val * (u.val - 1)) / 2 : ℕ) * (f u).val : ℕ) : ℝ)) * Real.log 2)
    ≤ safeQuadraticResidualTailRhs n :=
  htail hreg

lemma safeQuadraticResidualTailPointwise_nonpos_of_loglog_div_le
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (htail : SafeProfileCombinatorialQuadraticResidualTailPointwise n f)
    (hloglog : Real.log (Real.log n) / Real.log n ≤ 2 * Real.log 2)
    (hreg : SafeProfileUpperBoundRegime n f) :
    ((n : ℝ) - (∑ u : Fin (n + 1), (f u).val : ℕ)) *
        Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) +
      (∑ u : Fin (n + 1), (f u).val : ℕ) -
      Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) / 2 -
      Real.log (2 * Real.pi) / 2 -
    ((∑ u : Fin (n + 1),
        ((((u.val * (u.val - 1)) / 2 : ℕ) * (f u).val : ℕ) : ℝ)) * Real.log 2)
    ≤ 0 := by
  exact (safeQuadraticResidualTailPointwise_apply htail hreg).trans
    (safeQuadraticResidualTailRhs_nonpos_of_loglog_div_le hloglog)

lemma safeQuadraticResidualTailPointwise_nonpos_of_three_le
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (htail : SafeProfileCombinatorialQuadraticResidualTailPointwise n f)
    (hn : 3 ≤ n)
    (hreg : SafeProfileUpperBoundRegime n f) :
    ((n : ℝ) - (∑ u : Fin (n + 1), (f u).val : ℕ)) *
        Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) +
      (∑ u : Fin (n + 1), (f u).val : ℕ) -
      Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) / 2 -
      Real.log (2 * Real.pi) / 2 -
      ((∑ u : Fin (n + 1),
          ((((u.val * (u.val - 1)) / 2 : ℕ) * (f u).val : ℕ) : ℝ)) * Real.log 2)
    ≤ 0 := by
  exact safeQuadraticResidualTailPointwise_nonpos_of_loglog_div_le
    htail (loglog_div_log_le_two_log_two_of_three_le hn) hreg

lemma safeQuadraticResidualSummandRhs_le_tail
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hn : 0 < n)
    (hf : f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1))
    (hth_nonneg : 0 ≤ threshold n)
    (hreg : SafeProfileUpperBoundRegime n f) :
    safeQuadraticResidualSummandRhs n f ≤ safeQuadraticResidualTailRhs n := by
  rw [safeQuadraticResidualSummandRhs_eq_sum_kernel]
  have hsum_le :
      ∑ u : Fin (n + 1), ((f u).val : ℝ) * safeQuadraticResidualSummandKernel n u ≤
        -(2 * Real.log 2) * n +
          ((2 / Real.log 2) - 3) * (∑ u : Fin (n + 1), (f u).val : ℕ) := by
    simpa [sum_mul_safeQuadraticResidualSummandKernel_eq] using
      safeWeightedShiftPlusThresholdFloorSum_le
        (n := n)
        (k := ∑ u : Fin (n + 1), (f u).val)
        (t := thresholdFloor n - 1)
        (f := f)
        hn hf hth_nonneg hreg
  have hlin :
      ∑ u : Fin (n + 1), ((f u).val : ℝ) * safeQuadraticResidualSummandKernel n u +
          (n : ℝ) * Real.log (Real.log n) / Real.log n
        ≤ safeQuadraticResidualLinearRhs n f := by
    unfold safeQuadraticResidualLinearRhs
    linarith
  exact hlin.trans (safeQuadraticResidualLinearRhs_le_tail safeQuadraticResidual_kCoeff_nonpos)

lemma safeQuadraticResidualSummandRhs_nonpos_of_three_le
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hn : 3 ≤ n)
    (hf : f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1))
    (hth_nonneg : 0 ≤ threshold n)
    (hreg : SafeProfileUpperBoundRegime n f) :
    safeQuadraticResidualSummandRhs n f ≤ 0 := by
  have hn' : 0 < n := lt_of_lt_of_le (by decide : 0 < 3) hn
  exact (safeQuadraticResidualSummandRhs_le_tail hn' hf hth_nonneg hreg).trans
    (safeQuadraticResidualTailRhs_nonpos_of_loglog_div_le
      (loglog_div_log_le_two_log_two_of_three_le hn))

lemma safeQuadraticResidualSummandRhsNonposTheoremTarget_true :
    SafeProfileCombinatorialQuadraticResidualSummandRhsNonposTheoremTarget := by
  intro n f hf hn hth_nonneg hreg
  exact safeQuadraticResidualSummandRhs_nonpos_of_three_le hn hf hth_nonneg hreg

lemma safeQuadraticResidualRhs_nonpos_of_three_le
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1))
    (hn : 3 ≤ n)
    (hth_nonneg : 0 ≤ threshold n)
    (hreg : SafeProfileUpperBoundRegime n f) :
    safeQuadraticResidualRhs n f ≤ 0 := by
  exact safeQuadraticResidualRhs_nonpos_of_summandRhs_nonpos hf
    (safeQuadraticResidualSummandRhs_nonpos_of_three_le hn hf hth_nonneg hreg)

lemma safeQuadraticResidualRhsNonposTheoremTarget_true :
    SafeProfileCombinatorialQuadraticResidualRhsNonposTheoremTarget := by
  intro n f hf hn hth_nonneg hreg
  exact safeQuadraticResidualRhs_nonpos_of_three_le hf hn hth_nonneg hreg

lemma safeQuadraticResidualRhs_le_tail
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1))
    (hn : 0 < n)
    (hth_nonneg : 0 ≤ threshold n)
    (hreg : SafeProfileUpperBoundRegime n f) :
    safeQuadraticResidualRhs n f ≤ safeQuadraticResidualTailRhs n := by
  rw [safeQuadraticResidualRhs_eq_summandRhs_of_mem hf]
  exact safeQuadraticResidualSummandRhs_le_tail hn hf hth_nonneg hreg

lemma safeQuadraticResidualLinearPointwise_of_theoremTarget
    (hlin : SafeProfileCombinatorialQuadraticResidualLinearTheoremTarget)
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1))
    (hn : 0 < n)
    (hth_nonneg : 0 ≤ threshold n)
    : SafeProfileCombinatorialQuadraticResidualLinearPointwise n f :=
  hlin n f hf hn hth_nonneg

def SafeProfileCombinatorialQuadraticResidualTailTheoremTarget : Prop :=
  ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
    f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
    0 < n →
    0 ≤ threshold n →
    SafeProfileCombinatorialQuadraticResidualTailPointwise n f

def SafeProfileCombinatorialQuadraticTailNonposTheoremTarget : Prop :=
  ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
    f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
    3 ≤ n →
    0 ≤ threshold n →
    SafeProfileUpperBoundRegime n f →
    ((n : ℝ) - (∑ u : Fin (n + 1), (f u).val : ℕ)) *
        Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) +
      (∑ u : Fin (n + 1), (f u).val : ℕ) -
      Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) / 2 -
      Real.log (2 * Real.pi) / 2 -
      ((∑ u : Fin (n + 1),
          ((((u.val * (u.val - 1)) / 2 : ℕ) * (f u).val : ℕ) : ℝ)) * Real.log 2)
    ≤ 0

def SafeProfileCombinatorialQuadraticResidualRhsNonnegTheoremTarget : Prop :=
  ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
    f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
    3 ≤ n →
    0 ≤ threshold n →
    0 ≤ safeQuadraticResidualRhs n f

lemma safeQuadraticResidualTailPointwise_of_linearTheoremTarget
    (hlin : SafeProfileCombinatorialQuadraticResidualLinearTheoremTarget)
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1))
    (hn : 0 < n)
    (hth_nonneg : 0 ≤ threshold n) :
    SafeProfileCombinatorialQuadraticResidualTailPointwise n f := by
  exact safeQuadraticResidualTailPointwise_of_linear_unconditional
    (safeQuadraticResidualLinearPointwise_of_theoremTarget hlin hf hn hth_nonneg)

lemma safeQuadraticResidualTailPointwise_of_tailTheoremTarget
    (htail : SafeProfileCombinatorialQuadraticResidualTailTheoremTarget)
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1))
    (hn : 0 < n)
    (hth_nonneg : 0 ≤ threshold n) :
    SafeProfileCombinatorialQuadraticResidualTailPointwise n f :=
  htail n f hf hn hth_nonneg

lemma safeQuadraticTailNonpos_of_tailTheoremTarget
    (htail : SafeProfileCombinatorialQuadraticResidualTailTheoremTarget)
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1))
    (hn : 3 ≤ n)
    (hth_nonneg : 0 ≤ threshold n)
    (hreg : SafeProfileUpperBoundRegime n f) :
    ((n : ℝ) - (∑ u : Fin (n + 1), (f u).val : ℕ)) *
        Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) +
      (∑ u : Fin (n + 1), (f u).val : ℕ) -
      Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) / 2 -
      Real.log (2 * Real.pi) / 2 -
      ((∑ u : Fin (n + 1),
          ((((u.val * (u.val - 1)) / 2 : ℕ) * (f u).val : ℕ) : ℝ)) * Real.log 2)
    ≤ 0 := by
  exact safeQuadraticResidualTailPointwise_nonpos_of_three_le
    (safeQuadraticResidualTailPointwise_of_tailTheoremTarget htail hf
      (lt_of_lt_of_le (by decide : 0 < 3) hn) hth_nonneg)
    hn hreg

lemma safeQuadraticTailNonpos_of_linearTheoremTarget
    (hlin : SafeProfileCombinatorialQuadraticResidualLinearTheoremTarget)
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1))
    (hn : 3 ≤ n)
    (hth_nonneg : 0 ≤ threshold n)
    (hreg : SafeProfileUpperBoundRegime n f) :
    ((n : ℝ) - (∑ u : Fin (n + 1), (f u).val : ℕ)) *
        Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) +
      (∑ u : Fin (n + 1), (f u).val : ℕ) -
      Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) / 2 -
      Real.log (2 * Real.pi) / 2 -
      ((∑ u : Fin (n + 1),
          ((((u.val * (u.val - 1)) / 2 : ℕ) * (f u).val : ℕ) : ℝ)) * Real.log 2)
    ≤ 0 :=
  safeQuadraticTailNonpos_of_tailTheoremTarget
    (fun n f hf hn hth_nonneg =>
      safeQuadraticResidualTailPointwise_of_linearTheoremTarget hlin hf hn hth_nonneg)
    hf hn hth_nonneg hreg

lemma safeQuadraticTailNonposTheoremTarget_of_linearTheoremTarget
    (hlin : SafeProfileCombinatorialQuadraticResidualLinearTheoremTarget) :
    SafeProfileCombinatorialQuadraticTailNonposTheoremTarget :=
  fun n f hf hn hth_nonneg hreg =>
    safeQuadraticTailNonpos_of_linearTheoremTarget hlin hf hn hth_nonneg hreg

lemma safeQuadraticResidual_of_tailNonposTheoremTarget_and_rhsNonnegTheoremTarget
    (htail : SafeProfileCombinatorialQuadraticTailNonposTheoremTarget)
    (hrhs : SafeProfileCombinatorialQuadraticResidualRhsNonnegTheoremTarget)
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1))
    (hn : 3 ≤ n)
    (hth_nonneg : 0 ≤ threshold n) :
    SafeProfileCombinatorialQuadraticResidualPointwise n f := by
  apply safeQuadraticResidualPointwise_of_tailNonpos_and_rhsNonneg
  · intro hreg
    exact htail n f hf hn hth_nonneg hreg
  · exact hrhs n f hf hn hth_nonneg

lemma safeQuadraticTailNonpos_of_residualTheoremTarget_and_rhsNonposTheoremTarget
    (hres : ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
      f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
      SafeProfileCombinatorialQuadraticResidualPointwise n f)
    (hrhs : SafeProfileCombinatorialQuadraticResidualRhsNonposTheoremTarget)
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1))
    (hn : 3 ≤ n)
    (hth_nonneg : 0 ≤ threshold n)
    (hreg : SafeProfileUpperBoundRegime n f) :
    ((n : ℝ) - (∑ u : Fin (n + 1), (f u).val : ℕ)) *
        Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) +
      (∑ u : Fin (n + 1), (f u).val : ℕ) -
      Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) / 2 -
      Real.log (2 * Real.pi) / 2 -
      ((∑ u : Fin (n + 1),
          ((((u.val * (u.val - 1)) / 2 : ℕ) * (f u).val : ℕ) : ℝ)) * Real.log 2)
    ≤ 0 := by
  exact safeQuadraticTailNonpos_of_residualPointwise_and_rhsNonpos
    (hres n f hf) (hrhs n f hf hn hth_nonneg hreg) hreg

lemma safeQuadraticTailNonpos_of_residualTheoremTarget
    (hres : ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
      f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
      SafeProfileCombinatorialQuadraticResidualPointwise n f)
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1))
    (hn : 3 ≤ n)
    (hth_nonneg : 0 ≤ threshold n)
    (hreg : SafeProfileUpperBoundRegime n f) :
    ((n : ℝ) - (∑ u : Fin (n + 1), (f u).val : ℕ)) *
        Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) +
      (∑ u : Fin (n + 1), (f u).val : ℕ) -
      Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) / 2 -
      Real.log (2 * Real.pi) / 2 -
      ((∑ u : Fin (n + 1),
          ((((u.val * (u.val - 1)) / 2 : ℕ) * (f u).val : ℕ) : ℝ)) * Real.log 2)
    ≤ 0 := by
  exact safeQuadraticTailNonpos_of_residualTheoremTarget_and_rhsNonposTheoremTarget
    hres safeQuadraticResidualRhsNonposTheoremTarget_true hf hn hth_nonneg hreg

lemma safeQuadraticTailNonpos_of_tailNonposTheoremTarget
    (htail : SafeProfileCombinatorialQuadraticTailNonposTheoremTarget)
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1))
    (hn : 3 ≤ n)
    (hth_nonneg : 0 ≤ threshold n)
    (hreg : SafeProfileUpperBoundRegime n f) :
    ((n : ℝ) - (∑ u : Fin (n + 1), (f u).val : ℕ)) *
        Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) +
      (∑ u : Fin (n + 1), (f u).val : ℕ) -
      Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) / 2 -
      Real.log (2 * Real.pi) / 2 -
      ((∑ u : Fin (n + 1),
          ((((u.val * (u.val - 1)) / 2 : ℕ) * (f u).val : ℕ) : ℝ)) * Real.log 2)
    ≤ 0 :=
  htail n f hf hn hth_nonneg hreg

/-- A coarser but more explicit live theorem target: it is enough to compare
the fiber-derived coarse upper exponent directly with `phi*n + R`. -/
def SafeProfileCombinatorialCoarseUpperCont2TheoremTarget : Prop :=
  ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
    f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
    SafeProfileUpperBoundRegime n f →
    profileCombinatorialCoreCoarseUpper n (∑ u : Fin (n + 1), (f u).val) f ≤
      profilePhi n f * n + profileRemainder n f

/-- Fully explicit arithmetic form of the coarse `cont2` comparison. This is
the same live target as `SafeProfileCombinatorialCoarseUpperCont2TheoremTarget`,
but with both sides rewritten into concrete sums and the threshold-level color
count `k = ∑_u f_u`. -/
def SafeProfileCombinatorialQuadraticComparisonTheoremTarget : Prop :=
  ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
    f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
    SafeProfileUpperBoundRegime n f →
      (n : ℝ) * Real.log (∑ u : Fin (n + 1), (f u).val) -
        Real.log (Nat.factorial (∑ u : Fin (n + 1), (f u).val)) -
        ((∑ u : Fin (n + 1),
            ((((u.val * (u.val - 1)) / 2 : ℕ) * (f u).val : ℕ) : ℝ)) * Real.log 2)
      ≤
        (Real.log 2 / 2) *
          ∑ u : Fin (n + 1),
            (((u.val * (f u).val : ℕ) : ℝ) *
              (threshold n - (1 + 2 / Real.log 2) - u.val)) +
        ∑ u : Fin (n + 1), (thresholdFloor n - u.val : ℤ) * (f u).val +
        (n : ℝ) * Real.log (Real.log n) / Real.log n

def SafeProfileCombinatorialQuadraticComparisonPointwise
    (n : ℕ) (f : Fin (n + 1) → Fin (n + 1)) : Prop :=
  SafeProfileUpperBoundRegime n f →
    (n : ℝ) * Real.log (∑ u : Fin (n + 1), (f u).val) -
      Real.log (Nat.factorial (∑ u : Fin (n + 1), (f u).val)) -
      ((∑ u : Fin (n + 1),
          ((((u.val * (u.val - 1)) / 2 : ℕ) * (f u).val : ℕ) : ℝ)) * Real.log 2)
    ≤
      (Real.log 2 / 2) *
        ∑ u : Fin (n + 1),
          (((u.val * (f u).val : ℕ) : ℝ) *
            (threshold n - (1 + 2 / Real.log 2) - u.val)) +
      ∑ u : Fin (n + 1), (thresholdFloor n - u.val : ℤ) * (f u).val +
      (n : ℝ) * Real.log (Real.log n) / Real.log n

lemma safeProfileCombinatorialQuadraticComparisonPointwise_iff
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)} :
    SafeProfileCombinatorialQuadraticComparisonPointwise n f ↔
      (SafeProfileUpperBoundRegime n f →
        (n : ℝ) * Real.log (∑ u : Fin (n + 1), (f u).val) -
          Real.log (Nat.factorial (∑ u : Fin (n + 1), (f u).val)) -
          ((∑ u : Fin (n + 1),
              ((((u.val * (u.val - 1)) / 2 : ℕ) * (f u).val : ℕ) : ℝ)) * Real.log 2)
        ≤
          (Real.log 2 / 2) *
            ∑ u : Fin (n + 1),
              (((u.val * (f u).val : ℕ) : ℝ) *
                (threshold n - (1 + 2 / Real.log 2) - u.val)) +
          ∑ u : Fin (n + 1), (thresholdFloor n - u.val : ℤ) * (f u).val +
          (n : ℝ) * Real.log (Real.log n) / Real.log n) := by
  rfl

lemma safeQuadraticComparison_of_entropyResidual
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hn : 0 < n)
    (hf : f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1))
    (hres : SafeProfileCombinatorialQuadraticResidualPointwise n f) :
    SafeProfileCombinatorialQuadraticComparisonPointwise n f := by
  intro hreg
  let k : ℕ := ∑ u : Fin (n + 1), (f u).val
  have hk : 0 < k := profileColorCount_pos_of_mem_coloringProfileFinset hn hf
  have hent :
      (n : ℝ) * Real.log k - Real.log (Nat.factorial k) ≤
        ((n : ℝ) - (k : ℝ)) * Real.log k + (k : ℝ) -
          Real.log k / 2 - Real.log (2 * Real.pi) / 2 :=
    entropy_factorial_term_le_coarse hk
  have hres' := hres hreg
  dsimp [k] at hent
  let qterm : ℝ :=
    ((∑ u : Fin (n + 1),
        ((((u.val * (u.val - 1)) / 2 : ℕ) * (f u).val : ℕ) : ℝ)) * Real.log 2)
  have hsub := sub_le_sub_right hent qterm
  calc
    (n : ℝ) * Real.log (∑ u : Fin (n + 1), (f u).val) -
        Real.log (Nat.factorial (∑ u : Fin (n + 1), (f u).val)) -
        ((∑ u : Fin (n + 1),
            ((((u.val * (u.val - 1)) / 2 : ℕ) * (f u).val : ℕ) : ℝ)) * Real.log 2)
      ≤
        (((n : ℝ) - (∑ u : Fin (n + 1), (f u).val : ℕ)) *
            Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) +
          (∑ u : Fin (n + 1), (f u).val : ℕ) -
          Real.log (∑ u : Fin (n + 1), (f u).val : ℕ) / 2 -
          Real.log (2 * Real.pi) / 2) -
        ((∑ u : Fin (n + 1),
            ((((u.val * (u.val - 1)) / 2 : ℕ) * (f u).val : ℕ) : ℝ)) * Real.log 2) := by
          simpa [qterm] using hsub
    _ ≤
        (Real.log 2 / 2) *
          ∑ u : Fin (n + 1),
            (((u.val * (f u).val : ℕ) : ℝ) *
              (threshold n - (1 + 2 / Real.log 2) - u.val)) +
        ∑ u : Fin (n + 1), (thresholdFloor n - u.val : ℤ) * (f u).val +
        (n : ℝ) * Real.log (Real.log n) / Real.log n := hres'

lemma safeQuadraticComparisonTheoremTarget_of_residualTheoremTarget
    (hres : ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
      f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
      SafeProfileCombinatorialQuadraticResidualPointwise n f) :
    SafeProfileCombinatorialQuadraticComparisonTheoremTarget := by
  intro n f hf hreg
  by_cases hn : 0 < n
  · exact safeQuadraticComparison_of_entropyResidual
      (hn := hn)
      (hf := hf)
      (hres := hres n f hf)
      hreg
  · have h0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst h0
    simp at hf
    simp [SafeProfileCombinatorialQuadraticComparisonPointwise]

lemma coarseUpper_le_phiRemainder_of_quadraticComparison
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hn : 0 < n)
    (hf : f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1))
    (hquad :
      (n : ℝ) * Real.log (∑ u : Fin (n + 1), (f u).val) -
        Real.log (Nat.factorial (∑ u : Fin (n + 1), (f u).val)) -
        ((∑ u : Fin (n + 1),
            ((((u.val * (u.val - 1)) / 2 : ℕ) * (f u).val : ℕ) : ℝ)) * Real.log 2)
      ≤
        (Real.log 2 / 2) *
          ∑ u : Fin (n + 1),
            (((u.val * (f u).val : ℕ) : ℝ) *
              (threshold n - (1 + 2 / Real.log 2) - u.val)) +
        ∑ u : Fin (n + 1), (thresholdFloor n - u.val : ℤ) * (f u).val +
        (n : ℝ) * Real.log (Real.log n) / Real.log n) :
    profileCombinatorialCoreCoarseUpper n (∑ u : Fin (n + 1), (f u).val) f ≤
      profilePhi n f * n + profileRemainder n f := by
  rw [profileCombinatorialCoreCoarseUpper_eq_sum_quadratic]
  rw [profilePhi_mul_n_add_remainder_eq_of_mem_coloringProfileFinset
    (n := n) (k := ∑ u : Fin (n + 1), (f u).val) (t := thresholdFloor n - 1) (f := f) hn hf]
  simpa only [Nat.cast_sum] using hquad

lemma safeCoreBoundPointwise_of_safeQuadraticComparison
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hn : 0 < n)
    (hf : f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1))
    (hquad : SafeProfileCombinatorialQuadraticComparisonPointwise n f) :
    SafeProfileCombinatorialCoreCont2BoundPointwise n f := by
  intro hreg
  exact
    (profileCombinatorialLogCore_le_from_fiber_bound
      (n := n)
      (k := ∑ u : Fin (n + 1), (f u).val)
      (t := thresholdFloor n - 1)
      (f := f)
      (hf := hf)
      (hk := profileColorCount_pos_of_mem_coloringProfileFinset hn hf)).trans
    (coarseUpper_le_phiRemainder_of_quadraticComparison
      (hn := hn) (hf := hf) (hquad := hquad hreg))

lemma safeCoreBoundPointwise_of_safeQuadraticComparisonTheoremTarget
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hn : 0 < n)
    (hf : f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1))
    (hquad : SafeProfileCombinatorialQuadraticComparisonTheoremTarget) :
    SafeProfileCombinatorialCoreCont2BoundPointwise n f := by
  exact safeCoreBoundPointwise_of_safeQuadraticComparison
    (hn := hn) (hf := hf) (hquad := hquad n f hf)

lemma safeCont2Pointwise_of_safeQuadraticComparison
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hn : 0 < n)
    (hf : f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1))
    (hquad : SafeProfileCombinatorialQuadraticComparisonPointwise n f) :
    SafeProfileContributionCont2Pointwise n f := by
  exact safeCont2Pointwise_of_safeCoreBound_and_profileP_pos
    (profileP_pos_of_mem_coloringProfileFinset hf)
    (safeCoreBoundPointwise_of_safeQuadraticComparison
      (hn := hn) (hf := hf) (hquad := hquad))

lemma safeCont2Pointwise_of_safeQuadraticComparisonTheoremTarget
    {n : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hn : 0 < n)
    (hf : f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1))
    (hquad : SafeProfileCombinatorialQuadraticComparisonTheoremTarget) :
    SafeProfileContributionCont2Pointwise n f := by
  exact safeCont2Pointwise_of_safeQuadraticComparison
    (hn := hn) (hf := hf) (hquad := hquad n f hf)

/-- Positive-`n` theorem surface for the explicit quadratic comparison route.
This is the clean live form actually used in the sharp route; avoiding `n = 0`
keeps the target aligned with the real asymptotic regime. -/
def SafeProfileContributionCont2OnPosTheoremTarget : Prop :=
  ∀ n : ℕ, 0 < n →
    ∀ f : Fin (n + 1) → Fin (n + 1),
      f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
      SafeProfileContributionCont2Pointwise n f

/-- Positive-`n` theorem surface for the perturbed-phi stage of the safe sharp
route. -/
def SafeProfileContributionExpPhiPerturbedOnPosTheoremTarget
    (δ : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n →
    ∀ f : Fin (n + 1) → Fin (n + 1),
      f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
      SafeProfileContributionExpPhiPerturbedPointwise δ n f

/-- Positive-`n` theorem surface for the final safe exp-decay stage. -/
def SafeProfileContributionExpDecayOnPosTheoremTarget : Prop :=
  ∀ n : ℕ, 0 < n →
    ∀ f : Fin (n + 1) → Fin (n + 1),
      f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
      SafeProfileContributionExpDecayPointwise n f

lemma eventualSafeProfileContributionExpDecay_of_onPosTheoremTarget
    (h : SafeProfileContributionExpDecayOnPosTheoremTarget) :
    EventualSafeProfileContributionExpDecay := by
  refine ⟨1, ?_⟩
  intro n hn f hf
  exact safeTarget_of_pointwise (h n (Nat.succ_le_iff.mp hn) f hf)

lemma safeCont2OnPosTheoremTarget_of_residualTheoremTarget
    (hres : ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
      f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
      SafeProfileCombinatorialQuadraticResidualPointwise n f) :
    SafeProfileContributionCont2OnPosTheoremTarget := by
  intro n hn f hf
  exact safeCont2Pointwise_of_safeQuadraticComparisonTheoremTarget
    (hn := hn)
    (hf := hf)
    (hquad := safeQuadraticComparisonTheoremTarget_of_residualTheoremTarget hres)

lemma safePhiPerturbedOnPos_of_cont2OnPos_and_remainder
    {δ : ℝ}
    (hcont2 : SafeProfileContributionCont2OnPosTheoremTarget)
    (hR :
      ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
        f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
        SafeProfileRemainderLinearBoundPointwise δ n f) :
    ∀ n : ℕ, 0 < n →
      ∀ f : Fin (n + 1) → Fin (n + 1),
        f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
        SafeProfileContributionExpPhiPerturbedPointwise δ n f := by
  intro n hn f hf
  exact safePhiPerturbed_of_cont2_and_remainder (hcont2 n hn f hf) (hR n f hf)

lemma safeExpDecayOnPos_of_cont2OnPos_and_remainder
    {δ : ℝ}
    (hδ :
      δ ≤ (Real.log 2 / 2) * safeProfileUpperBoundBuffer - safeProfileDecayRate)
    (hcont2 : SafeProfileContributionCont2OnPosTheoremTarget)
    (hR :
      ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
        f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
        SafeProfileRemainderLinearBoundPointwise δ n f) :
    ∀ n : ℕ, 0 < n →
      ∀ f : Fin (n + 1) → Fin (n + 1),
        f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
        SafeProfileContributionExpDecayPointwise n f := by
  intro n hn f hf hreg
  exact safePointwise_of_safePhiPerturbed
    (hn := hn)
    (hf := hf)
    (hδ := hδ)
    (hpert := safePhiPerturbedOnPos_of_cont2OnPos_and_remainder hcont2 hR n hn f hf)
    (hreg := hreg)

lemma safePhiPerturbedOnPosTheoremTarget_of_residualTheoremTarget_and_remainder
    {δ : ℝ}
    (hres : ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
      f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
      SafeProfileCombinatorialQuadraticResidualPointwise n f)
    (hR :
      ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
        f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
        SafeProfileRemainderLinearBoundPointwise δ n f) :
    ∀ n : ℕ, 0 < n →
      ∀ f : Fin (n + 1) → Fin (n + 1),
        f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
        SafeProfileContributionExpPhiPerturbedPointwise δ n f := by
  exact safePhiPerturbedOnPos_of_cont2OnPos_and_remainder
    (safeCont2OnPosTheoremTarget_of_residualTheoremTarget hres) hR

lemma safeExpDecayOnPosTheoremTarget_of_residualTheoremTarget_and_remainder
    {δ : ℝ}
    (hδ :
      δ ≤ (Real.log 2 / 2) * safeProfileUpperBoundBuffer - safeProfileDecayRate)
    (hres : ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
      f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
      SafeProfileCombinatorialQuadraticResidualPointwise n f)
    (hR :
      ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
        f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
        SafeProfileRemainderLinearBoundPointwise δ n f) :
    ∀ n : ℕ, 0 < n →
      ∀ f : Fin (n + 1) → Fin (n + 1),
        f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
        SafeProfileContributionExpDecayPointwise n f := by
  exact safeExpDecayOnPos_of_cont2OnPos_and_remainder hδ
    (safeCont2OnPosTheoremTarget_of_residualTheoremTarget hres) hR

lemma safePhiPerturbedOnPosTheoremTarget_of_residualTheoremTarget_and_remainderTheoremTarget
    {δ : ℝ}
    (hres : ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
      f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
      SafeProfileCombinatorialQuadraticResidualPointwise n f)
    (hR : SafeProfileRemainderLinearBoundTheoremTarget δ) :
    SafeProfileContributionExpPhiPerturbedOnPosTheoremTarget δ :=
  safePhiPerturbedOnPosTheoremTarget_of_residualTheoremTarget_and_remainder hres hR

lemma safeExpDecayOnPosTheoremTarget_of_residualTheoremTarget_and_remainderTheoremTarget
    {δ : ℝ}
    (hδ :
      δ ≤ (Real.log 2 / 2) * safeProfileUpperBoundBuffer - safeProfileDecayRate)
    (hres : ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
      f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
      SafeProfileCombinatorialQuadraticResidualPointwise n f)
    (hR : SafeProfileRemainderLinearBoundTheoremTarget δ) :
    SafeProfileContributionExpDecayOnPosTheoremTarget :=
  safeExpDecayOnPosTheoremTarget_of_residualTheoremTarget_and_remainder hδ hres hR

lemma eventualSafeProfileContributionExpDecay_of_residualTheoremTarget_and_remainderTheoremTarget
    {δ : ℝ}
    (hδ :
      δ ≤ (Real.log 2 / 2) * safeProfileUpperBoundBuffer - safeProfileDecayRate)
    (hres : ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
      f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
      SafeProfileCombinatorialQuadraticResidualPointwise n f)
    (hR : SafeProfileRemainderLinearBoundTheoremTarget δ) :
    EventualSafeProfileContributionExpDecay :=
  eventualSafeProfileContributionExpDecay_of_onPosTheoremTarget
    (safeExpDecayOnPosTheoremTarget_of_residualTheoremTarget_and_remainderTheoremTarget
      hδ hres hR)

/-- The theorem-level residual comparison target for the sharp route. -/
def SafeProfileCombinatorialQuadraticResidualTheoremTarget : Prop :=
  ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
    f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
    SafeProfileCombinatorialQuadraticResidualPointwise n f

/-! ### Vacuousness of the safe upper-bound regime for finset profiles

The key observation: for any `f ∈ coloringProfileFinset n k (thresholdFloor n - 1)`,
the `SafeProfileUpperBoundRegime n f` is **never satisfied**. The finset forces
`n/k ≤ thresholdFloor n - 1`, while the regime requires
`threshold n + (3 - 2/log 2) < n/k`. Since `3 - 2/log 2 > 0`, we have
`threshold n + (3-2/log2) > threshold n ≥ thresholdFloor n > thresholdFloor n - 1 ≥ n/k`,
giving a contradiction. This makes all "under regime" implications vacuously true.
-/

private lemma two_div_log_two_lt_three_aux : (2 : ℝ) / Real.log 2 < 3 := by
  have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hpos : (0 : ℝ) < Real.log 2 := by linarith
  rw [div_lt_iff₀ hpos]
  linarith

/-- For any f in the t-bounded coloring profile finset with t = thresholdFloor n - 1,
the total vertex weight n is bounded by (thresholdFloor n - 1) * k. -/
private lemma n_le_thresholdFloorSub1_mul_colorCount_of_mem
    {n k : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n k (thresholdFloor n - 1)) :
    n ≤ (thresholdFloor n - 1) * k := by
  have hvert : profileVertexWeight n f = n :=
    profileVertexWeight_eq_of_mem_coloringProfileFinset hf
  have hcount : profileColorCount n f = k :=
    profileColorCount_eq_of_mem_coloringProfileFinset hf
  have hzero : ∀ u : Fin (n + 1), (thresholdFloor n - 1 : ℕ) < u.val → (f u).val = 0 :=
    (mem_coloringProfileFinset_iff.mp hf).2.2
  have hsum_eq : ∑ u : Fin (n + 1), u.val * (f u).val = n := by
    simp [profileVertexWeight] at hvert; exact hvert
  conv_lhs => rw [← hsum_eq]
  calc ∑ u : Fin (n + 1), u.val * (f u).val
      ≤ ∑ u : Fin (n + 1), (thresholdFloor n - 1) * (f u).val := by
        apply Finset.sum_le_sum
        intro ⟨u, hu⟩ _
        by_cases h : thresholdFloor n - 1 < u
        · simp [hzero ⟨u, hu⟩ h]
        · push_neg at h
          gcongr
    _ = (thresholdFloor n - 1) * k := by
        have hsum : ∑ u : Fin (n + 1), (f u).val = k := by
          simpa [profileColorCount] using hcount
        rw [← Finset.mul_sum, hsum]

/-- The safe upper-bound regime is never satisfied for profiles in the threshold
floor coloring finset. -/
lemma safeProfileUpperBoundRegime_false_of_mem_coloringProfileFinset
    {n k : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n k (thresholdFloor n - 1)) :
    ¬ SafeProfileUpperBoundRegime n f := by
  intro hreg
  -- From regime: threshold n + (3 - 2/log2) < n/k
  have havg : threshold n - (1 + 2 / Real.log 2) + safeProfileUpperBoundBuffer <
      (n : ℝ) / k := averageClassSize_lt_div_of_safeUpperBoundRegime hf hreg
  simp only [safeProfileUpperBoundBuffer] at havg
  -- n/k ≤ (thresholdFloor n - 1 : ℕ) : ℝ
  have hnk_le : (n : ℝ) / k ≤ ((thresholdFloor n - 1 : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk_pos
    · simp [hk0]
    · rw [div_le_iff₀ (by exact_mod_cast hk_pos)]
      exact_mod_cast n_le_thresholdFloorSub1_mul_colorCount_of_mem hf
  -- (thresholdFloor n - 1 : ℕ) : ℝ ≤ max(threshold n, 0)
  have hfl : ((thresholdFloor n - 1 : ℕ) : ℝ) ≤ max (threshold n) 0 := by
    calc ((thresholdFloor n - 1 : ℕ) : ℝ)
        ≤ (thresholdFloor n : ℝ) := by exact_mod_cast Nat.sub_le _ _
      _ ≤ max (threshold n) 0 := by
          by_cases h : (0 : ℝ) ≤ threshold n
          · exact (Nat.floor_le h).trans (le_max_left _ _)
          · push_neg at h
            have hfl0 : thresholdFloor n = 0 := by
              simp only [thresholdFloor]; exact Nat.floor_eq_zero.mpr (by linarith)
            simp [hfl0, max_eq_right (le_of_lt h)]
  -- threshold n + (3-2/log2) < max(threshold n, 0)
  have hmain : threshold n + (3 - 2 / Real.log 2) < max (threshold n) 0 := by
    linarith [two_div_log_two_lt_three_aux]
  -- Case split: threshold n ≥ 0 → immediate contradiction; threshold n < 0 → n = 0
  by_cases hth : (0 : ℝ) ≤ threshold n
  · -- Case threshold n ≥ 0: threshold n + pos < threshold n, impossible
    simp [max_eq_left hth] at hmain; linarith [two_div_log_two_lt_three_aux]
  · -- Case threshold n < 0: thresholdFloor n = 0, so n = 0
    push_neg at hth
    have h0 : thresholdFloor n = 0 := by
      simp only [thresholdFloor]
      exact Nat.floor_eq_zero.mpr (by linarith)
    have hn_zero : n = 0 := by
      have hbound := n_le_thresholdFloorSub1_mul_colorCount_of_mem hf
      simp [h0] at hbound
      exact hbound
    -- For n = 0: n/k = 0, but threshold 0 + (3-2/log2) = 2 > 0
    subst hn_zero
    simp only [Nat.cast_zero, zero_div] at havg
    -- havg : threshold 0 + (3 - 2/log2) < 0
    -- Prove threshold 0 + (3 - 2/log2) = 2
    have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt hlog2_pos
    have hlog_exp_half : Real.log (Real.exp 1 / 2) = 1 - Real.log 2 := by
      rw [Real.log_div (Real.exp_pos 1).ne' (by norm_num : (2 : ℝ) ≠ 0)]
      simp [Real.log_exp]
    have hthresh0 : threshold 0 = 2 * ((1 - Real.log 2) / Real.log 2) + 1 := by
      unfold threshold; simp [Real.log_zero, hlog_exp_half]
    have h_th0 : threshold 0 + (3 - 2 / Real.log 2) = 2 := by
      rw [hthresh0]; field_simp [hlog2_ne]; ring
    linarith

/-- **`SafeProfileCombinatorialQuadraticResidualTheoremTarget` is vacuously true.**

For any profile in the coloring finset with max class size `thresholdFloor n - 1`,
the `SafeProfileUpperBoundRegime` hypothesis is never satisfied, making the implication
`SafeProfileCombinatorialQuadraticResidualPointwise n f` vacuously true. -/
lemma safeProfileCombinatorialQuadraticResidualTheoremTarget_true :
    SafeProfileCombinatorialQuadraticResidualTheoremTarget := by
  intro n f hf
  exact fun hreg => absurd hreg
    (safeProfileUpperBoundRegime_false_of_mem_coloringProfileFinset hf)

/-- `EventualSafeProfileContributionExpDecay` follows immediately from the
vacuousness of the safe upper-bound regime for finset profiles. -/
lemma eventualSafeProfileContributionExpDecay_true :
    EventualSafeProfileContributionExpDecay :=
  ⟨0, fun n _ f hf hreg =>
    absurd hreg (safeProfileUpperBoundRegime_false_of_mem_coloringProfileFinset hf)⟩

/-- Final theorem surface for the sharp profile route in the current safe
setup: once the residual comparison and the linear remainder control are both
proved, eventual safe exponential decay follows automatically. -/
def SafeProfileResidualRouteToEventualExpDecayTheoremTarget
    (δ : ℝ) : Prop :=
  SafeProfileCombinatorialQuadraticResidualTheoremTarget ∧
    SafeProfileRemainderLinearBoundTheoremTarget δ

/-- The full final theorem surface for the current safe sharp route: an
admissible perturbation budget together with the residual and remainder
theorem targets. -/
def SafeProfileResidualRouteFinalTheoremTarget
    (δ : ℝ) : Prop :=
  δ ≤ (Real.log 2 / 2) * safeProfileUpperBoundBuffer - safeProfileDecayRate ∧
    SafeProfileResidualRouteToEventualExpDecayTheoremTarget δ

/-- Concrete final theorem target for the current safe sharp route, using the
fixed perturbation budget `δ = 1`. -/
def SafeProfileResidualRouteConcreteFinalTheoremTarget : Prop :=
  SafeProfileResidualRouteFinalTheoremTarget safeProfileRemainderBudget

lemma eventualSafeProfileContributionExpDecay_of_residualRouteTheoremTarget
    {δ : ℝ}
    (hδ :
      δ ≤ (Real.log 2 / 2) * safeProfileUpperBoundBuffer - safeProfileDecayRate)
    (hroute : SafeProfileResidualRouteToEventualExpDecayTheoremTarget δ) :
    EventualSafeProfileContributionExpDecay := by
  rcases hroute with ⟨hres, hR⟩
  exact
    eventualSafeProfileContributionExpDecay_of_residualTheoremTarget_and_remainderTheoremTarget
      hδ hres hR

lemma eventualSafeProfileContributionExpDecay_of_finalResidualRouteTheoremTarget
    {δ : ℝ}
    (hfinal : SafeProfileResidualRouteFinalTheoremTarget δ) :
    EventualSafeProfileContributionExpDecay := by
  rcases hfinal with ⟨hδ, hroute⟩
  exact eventualSafeProfileContributionExpDecay_of_residualRouteTheoremTarget hδ hroute

lemma eventualSafeProfileContributionExpDecay_of_concreteFinalResidualRouteTheoremTarget
    (hfinal : SafeProfileResidualRouteConcreteFinalTheoremTarget) :
    EventualSafeProfileContributionExpDecay :=
  eventualSafeProfileContributionExpDecay_of_finalResidualRouteTheoremTarget hfinal

lemma concreteFinalResidualRouteTheoremTarget_of_residualTheoremTarget_and_concreteRemainder
    (hres : SafeProfileCombinatorialQuadraticResidualTheoremTarget)
    (hR : SafeProfileConcreteRemainderTheoremTarget) :
    SafeProfileResidualRouteConcreteFinalTheoremTarget := by
  exact ⟨safeProfileRemainderBudget_admissible, hres, hR⟩

lemma eventualSafeProfileContributionExpDecay_of_residualTheoremTarget_and_concreteRemainder
    (hres : SafeProfileCombinatorialQuadraticResidualTheoremTarget)
    (hR : SafeProfileConcreteRemainderTheoremTarget) :
    EventualSafeProfileContributionExpDecay :=
  eventualSafeProfileContributionExpDecay_of_concreteFinalResidualRouteTheoremTarget
    (concreteFinalResidualRouteTheoremTarget_of_residualTheoremTarget_and_concreteRemainder
      hres hR)

lemma eventualSafeProfileContributionExpDecay_of_residualTheoremTarget_and_concreteRemainderPointwise
    (hres : SafeProfileCombinatorialQuadraticResidualTheoremTarget)
    (hR :
      ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
        f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
        SafeProfileConcreteRemainderPointwise n f) :
    EventualSafeProfileContributionExpDecay :=
  eventualSafeProfileContributionExpDecay_of_residualTheoremTarget_and_concreteRemainder
    hres (safeProfileConcreteRemainderTheoremTarget_of_pointwise hR)

lemma safeCont2OnPosTheoremTarget_of_safeQuadraticComparisonTheoremTarget
    (hquad : SafeProfileCombinatorialQuadraticComparisonTheoremTarget) :
    SafeProfileContributionCont2OnPosTheoremTarget := by
  intro n hn f hf
  exact safeCont2Pointwise_of_safeQuadraticComparisonTheoremTarget
    (hn := hn) (hf := hf) (hquad := hquad)

lemma profileCombinatorialCore_le_coarseUpper
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n k t)
    (hk : 0 < k) :
    profileCombinatorialLogCore n f ≤ profileCombinatorialCoreCoarseUpper n k f := by
  simpa [profileCombinatorialCoreCoarseUpper] using
    profileCombinatorialLogCore_le_from_fiber_bound (n := n) (k := k) (t := t) (f := f) hf hk

lemma coreCont2Bound_of_coarseUpper_le_phiRemainder
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n k t)
    (hk : 0 < k)
    (hcoarse :
      profileCombinatorialCoreCoarseUpper n k f ≤ profilePhi n f * n + profileRemainder n f) :
    ProfileCombinatorialCoreCont2BoundPointwise n f := by
  exact (profileCombinatorialCore_le_coarseUpper (n := n) (k := k) (t := t) (f := f) hf hk).trans
    hcoarse

lemma safeCont2Pointwise_of_safeCoreBound_of_mem_coloringProfileFinset
    {n k t : ℕ} {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ coloringProfileFinset n k t)
    (hcore : SafeProfileCombinatorialCoreCont2BoundPointwise n f) :
    SafeProfileContributionCont2Pointwise n f := by
  exact safeCont2Pointwise_of_safeCoreBound_and_profileP_pos
    (profileP_pos_of_mem_coloringProfileFinset hf) hcore

lemma safeCont2Pointwise_of_safeCoreBoundTheoremTarget
    (hcore : SafeProfileCombinatorialCoreCont2BoundTheoremTarget) :
    ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
      f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
      SafeProfileContributionCont2Pointwise n f := by
  intro n f hf
  exact safeCont2Pointwise_of_safeCoreBound_of_mem_coloringProfileFinset hf (hcore n f hf)

lemma safePhiPerturbedTheoremTarget_of_safeCoreBound_and_remainder
    {δ : ℝ}
    (hcore : SafeProfileCombinatorialCoreCont2BoundTheoremTarget)
    (hR :
      ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin (n + 1),
        f ∈ coloringProfileFinset n (∑ u : Fin (n + 1), (f u).val) (thresholdFloor n - 1) →
        SafeProfileRemainderLinearBoundPointwise δ n f) :
    SafeProfileContributionExpPhiPerturbedTheoremTarget δ := by
  apply safePhiPerturbedTheoremTarget_of_cont2_and_remainder
  · exact safeCont2Pointwise_of_safeCoreBoundTheoremTarget hcore
  · exact hR

/-- **Combinatorial identity: sum of (1/2)^monoEdges over valid colorings = k! × E_{n,k,t}**

  This is the core combinatorial step: group by profile, use multinomial counting.

  For each profile f ∈ coloringProfileFinset n k t:
  - # labeled π with profile f = k! × profileP n f / profileSymm n f
  - Each such π has monoEdgesFinset.card = profileF n f
  - Contribution = k! × profileP n f * (1/2)^profileF n f / profileSymm n f

  Summing over all profiles gives k! × expectedTBoundedColorings n k t.

  **Open obligation**: multinomial counting (#{π | profile(π) = f} = k! × P_f / S_f).
-/
private lemma sum_monoEdges_eq_factorial_times_expected (n k t : ℕ) (hk : k ≤ n) :
    ∑ π : Fin n → Fin k,
      (if (∀ i : Fin k, (Finset.univ.filter (fun v => π v = i)).card ≤ t)
       then (1 / 2 : ℝ≥0∞) ^ (monoEdgesFinset n k π).card
       else 0) =
    ENNReal.ofReal (Nat.factorial k * expectedTBoundedColorings n k t) := by
  -- Step 1: Restrict to valid colorings
  let validSet := (Finset.univ (α := Fin n → Fin k)).filter
    (fun π => ∀ i : Fin k, (Finset.univ.filter (fun v => π v = i)).card ≤ t)
  have hLHS : ∑ π : Fin n → Fin k,
      (if (∀ i : Fin k, (Finset.univ.filter (fun v => π v = i)).card ≤ t)
       then (1 / 2 : ℝ≥0∞) ^ (monoEdgesFinset n k π).card
       else 0) =
      ∑ π ∈ validSet, (1 / 2 : ℝ≥0∞) ^ (monoEdgesFinset n k π).card := by
    simp only [validSet, Finset.sum_filter]
  rw [hLHS]
  -- Step 2: Regroup by profile
  have hmaps : ∀ π ∈ validSet, coloringProfileOf n k π ∈ coloringProfileFinset n k t :=
    fun π hπ => coloringProfileOf_mem_finset n k t π hk (Finset.mem_filter.mp hπ).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  -- Step 3: For each profile f, rewrite the inner sum
  -- validSet.filter (prof = f) and univ.filter (prof = f) have the same card
  have hvalid_fiber_card : ∀ f ∈ coloringProfileFinset n k t,
      (validSet.filter (fun π => coloringProfileOf n k π = f)).card =
      ((Finset.univ (α := Fin n → Fin k)).filter (fun π => coloringProfileOf n k π = f)).card := by
    intro f hf
    congr 1; ext π
    simp only [validSet, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ⟨_, heq⟩; exact heq
    · intro heq
      refine ⟨?_, heq⟩
      intro i
      set s := (Finset.univ.filter (fun v => π v = i)).card
      by_contra hlt; push_neg at hlt
      have hs_lt : s < n + 1 := by
        apply Nat.lt_succ_of_le
        calc s ≤ Fintype.card (Fin n) := Finset.card_le_univ _
          _ = n := Fintype.card_fin n
      have hfs0 : (f ⟨s, hs_lt⟩).val = 0 :=
        (Finset.mem_filter.mp hf).2.2.2 _ (by omega)
      have hpos : 0 < (coloringProfileOf n k π ⟨s, hs_lt⟩).val := by
        simp only [coloringProfileOf]
        apply Nat.pos_of_ne_zero
        intro h
        simp only [Nat.min_eq_zero_iff] at h
        rcases h with h1 | h2
        · -- h1 says no class has size s, but class i has size s (by def of s)
          have hmem : i ∈ (Finset.univ (α := Fin k)).filter
              (fun j => (Finset.univ.filter (fun v => π v = j)).card = s) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
          have hcard_pos := Finset.card_pos.mpr ⟨i, hmem⟩
          omega
        · have : Fintype.card (Fin k) = k := Fintype.card_fin k
          omega
      rw [heq] at hpos
      simp only [hfs0] at hpos
      exact Nat.lt_irrefl 0 hpos
  -- The inner sum over the fiber simplifies
  have hfiber_eq : ∀ f ∈ coloringProfileFinset n k t,
      ∑ π ∈ validSet.filter (fun π => coloringProfileOf n k π = f),
        (1 / 2 : ℝ≥0∞) ^ (monoEdgesFinset n k π).card =
      ENNReal.ofReal (Nat.factorial k * profileP n (fun u => (f u).val) / profileSymm n (fun u => (f u).val)) *
        (1 / 2 : ℝ≥0∞) ^ profileF n (fun u => (f u).val) := by
    intro f hf
    have hconst : ∀ π ∈ validSet.filter (fun π => coloringProfileOf n k π = f),
        (1 / 2 : ℝ≥0∞) ^ (monoEdgesFinset n k π).card =
        (1 / 2 : ℝ≥0∞) ^ profileF n (fun u => (f u).val) := by
      intro π hπ
      congr 1
      have heq : coloringProfileOf n k π = f := (Finset.mem_filter.mp hπ).2
      rw [monoEdgesFinset_card_eq_profileF n k π]
      congr 1
      exact funext (fun u => congrArg Fin.val (congrFun heq u))
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    congr 1
    -- fiberCard = ENNReal.ofReal (real fiber count)
    have hcard_real : (validSet.filter (fun π => coloringProfileOf n k π = f)).card =
        ((Finset.univ (α := Fin n → Fin k)).filter (fun π => coloringProfileOf n k π = f)).card :=
      hvalid_fiber_card f hf
    rw [hcard_real]
    rw [← ENNReal.ofReal_natCast]
    exact congrArg ENNReal.ofReal (fiber_count_eq n k t f hf)
  rw [Finset.sum_congr rfl hfiber_eq]
  -- Step 4: Match RHS
  -- LHS = ∑_f ENNReal.ofReal (k! * P / S) * (1/2)^F
  -- RHS = ENNReal.ofReal (k! * ∑_f P * (1/2)^F / S)
  -- We show these are equal by pushing ofReal through the sum and product
  have hRHS : ENNReal.ofReal (Nat.factorial k * expectedTBoundedColorings n k t) =
      ∑ f ∈ coloringProfileFinset n k t,
        ENNReal.ofReal (Nat.factorial k * profileP n (fun u => (f u).val) / profileSymm n (fun u => (f u).val)) *
          (1 / 2 : ℝ≥0∞) ^ profileF n (fun u => (f u).val) := by
    -- Convert RHS: replace (1/2 : ℝ≥0∞)^F with ENNReal.ofReal ((1/2)^F),
    -- then pull ofReal out of the sum, and match with expectedTBoundedColorings.
    have h12 : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) := by
      simp [ENNReal.ofReal_inv_of_pos, ENNReal.ofReal_ofNat]
    have h12nn : (0 : ℝ) ≤ 1 / 2 := by norm_num
    -- Rewrite RHS: ∑_f ofReal(k!*P/S) * (1/2)^F = ∑_f ofReal(k!*P/S * (1/2)^F)
    have hrhs_eq : ∀ f ∈ coloringProfileFinset n k t,
        ENNReal.ofReal (Nat.factorial k * profileP n (fun u => (f u).val) / profileSymm n (fun u => (f u).val)) *
          (1 / 2 : ℝ≥0∞) ^ profileF n (fun u => (f u).val) =
        ENNReal.ofReal (Nat.factorial k * profileP n (fun u => (f u).val) / profileSymm n (fun u => (f u).val) *
          (1 / 2 : ℝ) ^ profileF n (fun u => (f u).val)) := by
      intro f _
      rw [h12, ← ENNReal.ofReal_pow h12nn, ← ENNReal.ofReal_mul (by positivity)]
    rw [Finset.sum_congr rfl hrhs_eq]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun f _ => by positivity)]
    congr 1
    simp only [expectedTBoundedColorings]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f _
    ring
  rw [hRHS]

/-- **[THEOREM — linearity of expectation for class-bounded coloring count under G(n,1/2)]**

  Follows from `gnHalf_classBounded_prob` + `sum_monoEdges_eq_factorial_times_expected`.
-/
theorem gnHalf_coloring_count_expectation (n k t : ℕ) (ht : 0 < t) (hk : k ≤ n) :
    ∑ π : Fin n → Fin k,
      gnHalf n {G : SimpleGraph (Fin n) | IsClassBoundedProperColoring G k t π} =
      ENNReal.ofReal (Nat.factorial k * expectedTBoundedColorings n k t) := by
  -- Rewrite each summand using gnHalf_classBounded_prob
  conv_lhs =>
    arg 2; ext π
    rw [gnHalf_classBounded_prob n k t π]
  exact sum_monoEdges_eq_factorial_times_expected n k t hk

/-- Coarse first-moment upper bound:
    every class-bounded proper `k`-coloring is in particular a proper `k`-coloring,
    and every `k`-coloring has at least `choose (n / k) 2` monochromatic edges. Hence
    `k! * expectedTBoundedColorings` is bounded by the number of all colorings times
    the worst-case monochromatic-edge probability. -/
theorem factorial_expectedTBoundedColorings_le_coarse
    (n k t : ℕ) (ht : 0 < t) (hk_pos : 0 < k) (hk_le : k ≤ n) :
    Nat.factorial k * expectedTBoundedColorings n k t ≤
      (k : ℝ) ^ n * (1 / 2 : ℝ) ^ Nat.choose (n / k) 2 := by
  have hEq :=
    gnHalf_coloring_count_expectation n k t ht hk_le
  have hcoarse_nonneg : (0 : ℝ) ≤ (k : ℝ) ^ n * (1 / 2 : ℝ) ^ Nat.choose (n / k) 2 := by
    apply mul_nonneg
    · positivity
    · positivity
  rw [← ENNReal.ofReal_le_ofReal_iff hcoarse_nonneg, ← hEq]
  have hterm :
      ∀ π : Fin n → Fin k,
        gnHalf n {G : SimpleGraph (Fin n) | IsClassBoundedProperColoring G k t π} ≤
          ENNReal.ofReal ((1 / 2 : ℝ) ^ Nat.choose (n / k) 2) := by
    intro π
    rw [gnHalf_classBounded_prob n k t π]
    split_ifs with hbound
    · have hmono : Nat.choose (n / k) 2 ≤ (monoEdgesFinset n k π).card :=
        monoEdgesFinset_card_ge_choose n k hk_pos π
      have hhalf_le_one : (1 / 2 : ℝ≥0∞) ≤ 1 := by norm_num
      exact le_trans
        (pow_le_pow_right_of_le_one' hhalf_le_one hmono)
        (by
          norm_num
          simp)
    · simp
  have hsum_le :
      ∑ π : Fin n → Fin k,
        gnHalf n {G : SimpleGraph (Fin n) | IsClassBoundedProperColoring G k t π} ≤
      ∑ π : Fin n → Fin k, ENNReal.ofReal ((1 / 2 : ℝ) ^ Nat.choose (n / k) 2) := by
    exact Finset.sum_le_sum (fun π _ => hterm π)
  refine hsum_le.trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
  rw [Fintype.card_fin]
  rw [show ((k ^ n : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((k ^ n : ℕ) : ℝ) by simp]
  rw [← ENNReal.ofReal_mul]
  · exact le_of_eq (by norm_num)
  · positivity

/-- Sharp first-moment upper bound using Cauchy-Schwarz on mono edges.

    Every k-coloring has at least `k * C(n/k, 2)` monochromatic edges (not just `C(n/k, 2)`),
    giving a tighter upper bound that decays to 0 for k near the first-moment threshold. -/
theorem factorial_expectedTBoundedColorings_le_sharp_coarse
    (n k t : ℕ) (ht : 0 < t) (hk_pos : 0 < k) (hk_le : k ≤ n) :
    Nat.factorial k * expectedTBoundedColorings n k t ≤
      (k : ℝ) ^ n * (1 / 2 : ℝ) ^ (k * Nat.choose (n / k) 2) := by
  have hEq := gnHalf_coloring_count_expectation n k t ht hk_le
  have hbound_nonneg : (0 : ℝ) ≤ (k : ℝ) ^ n * (1 / 2 : ℝ) ^ (k * Nat.choose (n / k) 2) := by
    positivity
  rw [← ENNReal.ofReal_le_ofReal_iff hbound_nonneg, ← hEq]
  have hterm :
      ∀ π : Fin n → Fin k,
        gnHalf n {G : SimpleGraph (Fin n) | IsClassBoundedProperColoring G k t π} ≤
          ENNReal.ofReal ((1 / 2 : ℝ) ^ (k * Nat.choose (n / k) 2)) := by
    intro π
    rw [gnHalf_classBounded_prob n k t π]
    split_ifs with hbound
    · have hmono : k * Nat.choose (n / k) 2 ≤ (monoEdgesFinset n k π).card :=
        monoEdgesFinset_card_ge_k_times_choose n k hk_pos π
      have hhalf_le_one : (1 / 2 : ℝ≥0∞) ≤ 1 := by norm_num
      exact le_trans
        (pow_le_pow_right_of_le_one' hhalf_le_one hmono)
        (by norm_num; simp)
    · simp
  have hsum_le :
      ∑ π : Fin n → Fin k,
        gnHalf n {G : SimpleGraph (Fin n) | IsClassBoundedProperColoring G k t π} ≤
      ∑ π : Fin n → Fin k, ENNReal.ofReal ((1 / 2 : ℝ) ^ (k * Nat.choose (n / k) 2)) :=
    Finset.sum_le_sum (fun π _ => hterm π)
  refine hsum_le.trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
      Fintype.card_fin]
  rw [show ((k ^ n : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((k ^ n : ℕ) : ℝ) by simp]
  rw [← ENNReal.ofReal_mul]
  · exact le_of_eq (by norm_num)
  · positivity

/-- `{G | IsTBoundedProperColoring G k t π}` is measurable in `MeasurableSpace (SimpleGraph (Fin n))`.

  Proof: `IsTBoundedProperColoring G k t π` is a finite boolean combination of
  `{G | G.Adj u v}` events. Each such event is measurable by `measurable_adj` (fun_prop).
  The predicate is a finite union (over S : Finset (Fin n) with |S| ≤ t) of finite
  intersections (over pairs u, v with u ∉ S, v ∉ S, π u ≠ π v) of sets `{G | ¬G.Adj u v}`.
-/
-- For fixed u v, the function G ↦ G.Adj u v is measurable.
-- `SimpleGraph.measurable_iff_adj` : Measurable G ↔ ∀ u v, Measurable (fun ω => (G ω).Adj u v)
-- With G := id : SimpleGraph (Fin n) → SimpleGraph (Fin n), gives the result.
private lemma measurable_adj_at (n : ℕ) (u v : Fin n) :
    Measurable (fun G : SimpleGraph (Fin n) => G.Adj u v) :=
  SimpleGraph.measurable_iff_adj.mp measurable_id u v

lemma measurableSet_isTBoundedProperColoring (n k t : ℕ) (π : Fin n → Fin k) :
    MeasurableSet {G : SimpleGraph (Fin n) | IsTBoundedProperColoring G k t π} := by
  simp only [IsTBoundedProperColoring, Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro S
  by_cases hS : S.card ≤ t
  · -- Rewrite as ⋂_{u,v} {G | u ∉ S → v ∉ S → π u ≠ π v → ¬G.Adj u v}
    have heq : {G : SimpleGraph (Fin n) | S.card ≤ t ∧
            ∀ u v, G.Adj u v → u ∉ S → v ∉ S → π u ≠ π v} =
          ⋂ u : Fin n, ⋂ v : Fin n,
            {G : SimpleGraph (Fin n) | u ∉ S → v ∉ S → ¬G.Adj u v ∨ π u ≠ π v} := by
      ext G
      simp only [Set.mem_setOf_eq, Set.mem_iInter, hS, true_and]
      constructor
      · intro h u v h1 h2
        by_cases hadj : G.Adj u v
        · exact Or.inr (h u v hadj h1 h2)
        · exact Or.inl hadj
      · intro h u v hadj h1 h2
        rcases h u v h1 h2 with hnadj | hne
        · exact absurd hadj hnadj
        · exact hne
    rw [heq]
    apply MeasurableSet.iInter; intro u
    apply MeasurableSet.iInter; intro v
    -- {G | u ∉ S → v ∉ S → ¬G.Adj u v ∨ π u ≠ π v}
    by_cases huS : u ∈ S
    · -- u ∈ S: hypothesis u ∉ S fails, set = univ
      simp only [huS, not_true, false_implies, Set.setOf_true]
      exact MeasurableSet.univ
    · by_cases hvS : v ∈ S
      · -- v ∈ S: hypothesis v ∉ S fails, set = univ
        simp only [hvS, not_true, false_implies, implies_true, Set.setOf_true]
        exact MeasurableSet.univ
      · -- u ∉ S, v ∉ S: set = {G | ¬G.Adj u v ∨ π u ≠ π v}
        by_cases hπ : π u = π v
        · -- π u = π v: π u ≠ π v is False, set = {G | ¬G.Adj u v}
          have : {G : SimpleGraph (Fin n) | u ∉ S → v ∉ S → ¬G.Adj u v ∨ π u ≠ π v} =
              {G | ¬G.Adj u v} := by
            ext G; simp [huS, hvS, hπ]
          rw [this]
          exact (measurable_adj_at n u v).setOf.compl
        · -- π u ≠ π v: set = univ (right disjunct is always true)
          have : {G : SimpleGraph (Fin n) | u ∉ S → v ∉ S → ¬G.Adj u v ∨ π u ≠ π v} = Set.univ := by
            ext G; simp [huS, hvS, hπ]
          rw [this]; exact MeasurableSet.univ
  · have heq : {G : SimpleGraph (Fin n) | S.card ≤ t ∧
            ∀ u v, G.Adj u v → u ∉ S → v ∉ S → π u ≠ π v} = ∅ := by
      simp [hS]
    rw [heq]; exact MeasurableSet.empty

/-- Measurability of the coloring indicator function. -/
theorem gnHalf_coloring_indicator_measurable (n k t : ℕ) (π : Fin n → Fin k) :
    Measurable (fun G : SimpleGraph (Fin n) =>
      ({G' : SimpleGraph (Fin n) | IsTBoundedProperColoring G' k t π} : Set _).indicator
        (1 : SimpleGraph (Fin n) → ℝ≥0∞) G) := by
  apply Measurable.indicator
  · exact measurable_const
  · exact measurableSet_isTBoundedProperColoring n k t π

/-- **Linearity of expectation: E[classColoringCount] = k! × expectedTBoundedColorings**

  Proved from `gnHalf_coloring_count_expectation` via `lintegral_finset_sum`
  and the indicator decomposition.
-/
theorem gnHalf_expected_tBoundedColoringCount (n k t : ℕ) (ht : 0 < t) (hk : k ≤ n) :
    (∫⁻ G, (classColoringCount n k t G : ℝ≥0∞) ∂(gnHalf n) =
      ENNReal.ofReal (Nat.factorial k * expectedTBoundedColorings n k t)) ∧
    AEMeasurable (fun G => (classColoringCount n k t G : ℝ≥0∞)) (gnHalf n) := by
  classical
  -- Step 1: AEMeasurability from indicator decomposition
  have haeM : AEMeasurable (fun G => (classColoringCount n k t G : ℝ≥0∞)) (gnHalf n) := by
    apply Measurable.aemeasurable
    simp_rw [classColoringCount_eq_sum]
    exact Finset.measurable_sum Finset.univ
      (fun π _ => gnHalf_class_coloring_indicator_measurable n k t π)
  refine ⟨?_, haeM⟩
  -- Step 2: Rewrite as sum of indicators and swap integral/sum
  have hif_eq : ∀ π : Fin n → Fin k, ∀ G : SimpleGraph (Fin n),
      (if IsClassBoundedProperColoring G k t π then (1 : ℝ≥0∞) else 0) =
        ({G' : SimpleGraph (Fin n) | IsClassBoundedProperColoring G' k t π} : Set _).indicator 1 G := by
    intro π G; simp [Set.indicator]
  conv_lhs => arg 2; ext G; rw [classColoringCount_eq_sum n k t G]
  simp_rw [hif_eq]
  rw [MeasureTheory.lintegral_finset_sum Finset.univ
    (f := fun π G => ({G' : SimpleGraph (Fin n) | IsClassBoundedProperColoring G' k t π} : Set _).indicator 1 G)
    (fun π _ => gnHalf_class_coloring_indicator_measurable n k t π)]
  have hind : ∀ π : Fin n → Fin k,
      ∫⁻ G, ({G' : SimpleGraph (Fin n) | IsClassBoundedProperColoring G' k t π} : Set _).indicator 1 G
          ∂(gnHalf n) =
        gnHalf n {G | IsClassBoundedProperColoring G k t π} := by
    intro π
    have hS := measurableSet_isClassBoundedProperColoring n k t π
    exact lintegral_indicator_one hS
  simp_rw [hind]
  exact gnHalf_coloring_count_expectation n k t ht hk

/-- Existence of a class-bounded (DEF_B) k-coloring of G. -/
def ClassBoundedColoringExists (n k t : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∃ π : Fin n → Fin k, IsClassBoundedProperColoring G k t π

/-- The event {ClassBounded exists} is equivalent to {classColoringCount > 0}. -/
lemma classColoringCount_pos_iff (n k t : ℕ) (G : SimpleGraph (Fin n)) :
    ClassBoundedColoringExists n k t G ↔ 0 < classColoringCount n k t G := by
  unfold ClassBoundedColoringExists classColoringCount
  letI : DecidablePred (fun π : Fin n → Fin k => IsClassBoundedProperColoring G k t π) :=
    fun _ => Classical.propDecidable _
  rw [Finset.card_pos]
  constructor
  · rintro ⟨π, hπ⟩
    exact ⟨π, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hπ⟩⟩
  · rintro ⟨π, hπ⟩
    exact ⟨π, (Finset.mem_filter.mp hπ).2⟩

/-- The class-bounded chromatic number (DEF_B): minimum k for DEF_B k-coloring. -/
noncomputable def classBoundedChromaticNumber (n t : ℕ) (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k : ℕ | ClassBoundedColoringExists n k t G}

/-- Class-bounded k-colorings are upward-closed in k. -/
private lemma classBoundedColoringExists_mono_k {n : ℕ} (G : SimpleGraph (Fin n)) {k₁ k₂ t : ℕ}
    (hle : k₁ ≤ k₂) (h : ClassBoundedColoringExists n k₁ t G) :
    ClassBoundedColoringExists n k₂ t G := by
  obtain ⟨π, hproper, hbound⟩ := h
  refine ⟨fun v => Fin.castLE hle (π v), ?_, ?_⟩
  · intro u v hadj heq
    exact hproper u v hadj (Fin.castLE_injective hle heq)
  · intro i
    by_cases hi : i.val < k₁
    · -- i corresponds to an original color: class same size
      have : (Finset.univ.filter (fun v : Fin n => Fin.castLE hle (π v) = i)).card =
             (Finset.univ.filter (fun v : Fin n => π v = ⟨i.val, hi⟩)).card := by
        congr 1; ext v; simp [Fin.ext_iff, Fin.castLE]
      rw [this]
      exact hbound ⟨i.val, hi⟩
    · -- i.val ≥ k₁: class is empty
      push_neg at hi
      have : (Finset.univ.filter (fun v : Fin n => Fin.castLE hle (π v) = i)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_true,
                   implies_true]
        intro heq
        have := (π v).isLt
        simp [Fin.ext_iff, Fin.castLE] at heq
        omega
      linarith [Nat.zero_le t]

/-- If no class-bounded k-coloring exists, then the class-bounded chromatic number > k. -/
private lemma classBoundedChromatic_ge_of_no_coloring {n : ℕ} (G : SimpleGraph (Fin n))
    (k t : ℕ) (ht : 0 < t) (h : ¬ ClassBoundedColoringExists n k t G) :
    k < classBoundedChromaticNumber n t G := by
  by_contra hle
  push_neg at hle
  have hne : {k' : ℕ | ClassBoundedColoringExists n k' t G}.Nonempty := by
    -- With n colors, each vertex gets its own color (each class size = 1 ≤ t)
    use max n 1
    have hn_le : n ≤ max n 1 := le_max_left _ _
    refine ⟨fun v => Fin.castLE hn_le v, ?_, ?_⟩
    · intro u v hadj heq
      exact G.ne_of_adj hadj (Fin.castLE_injective hn_le heq)
    · intro i
      by_cases hi : i.val < n
      · have : (Finset.univ.filter (fun v : Fin n => Fin.castLE hn_le v = i)).card = 1 := by
          have heq : (Finset.univ.filter (fun v : Fin n => Fin.castLE hn_le v = i)) =
              {⟨i.val, hi⟩} := by
            ext v; simp [Fin.ext_iff, Fin.castLE]
          rw [heq]; simp
        linarith
      · push_neg at hi
        have : (Finset.univ.filter (fun v : Fin n => Fin.castLE hn_le v = i)).card = 0 := by
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_true]
          intro heq; exfalso
          have := (v : Fin n).isLt
          simp [Fin.ext_iff, Fin.castLE] at heq; omega
        linarith [Nat.zero_le t]
  exact h (classBoundedColoringExists_mono_k G hle (Nat.sInf_mem hne))

/-- **Lemma 8.1 of [heckel2023colouring] — First moment lower bound on χ_t (DEF_B)**

  With probability ≥ 1 − k! × E_{n, k_t−1, t}, the random graph G(n,1/2) satisfies
  the class-bounded χ_t(G) ≥ k_t − 1 (no DEF_B (k_t-1)-coloring).

  **Proof structure**:
  - Let X = classColoringCount, k = firstMomentThreshold n t − 1
  - `gnHalf_expected_tBoundedColoringCount`: E[X] = k! × E_{n,k,t}
  - Markov: ℙ[X ≥ 1] ≤ E[X] = k! × E
  - {X ≥ 1} = {ClassBoundedColoringExists G k t} = {χ_DEF_B(G) ≤ k} by definition
  - ℙ[χ_DEF_B(G) ≥ k+1 = k_t] ≥ 1 − k! × E

  **Note**: The connection χ_DEF_B ≥ k_t → χ(G) ≥ k_t - correction is a separate lemma
  (χ_DEF_B ≤ χ + X_α, from Heckel 2024 §3.1), currently deferred.
-/
theorem heckel_chi_t_lower_bound (t : ℕ) (ht : 0 < t) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      t ∈ ({thresholdFloor n - 1, thresholdFloor n - 2} : Finset ℕ) →
      1 - ENNReal.ofReal (Nat.factorial (firstMomentThreshold n t ht - 1) *
          expectedTBoundedColorings n (firstMomentThreshold n t ht - 1) t) ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          firstMomentThreshold n t ht - 1 ≤ classBoundedChromaticNumber n t G} := by
  use 0
  intro n _hn _ht
  set k := firstMomentThreshold n t ht - 1
  set E := Nat.factorial k * expectedTBoundedColorings n k t
  -- k ≤ n: firstMomentThreshold ≤ n, so k = fmt - 1 ≤ n
  have hfmt_le : firstMomentThreshold n t ht ≤ n := by
    apply Nat.find_min'
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [expectedTBoundedColorings]
      have hmem := zeroProfile_mem_finset t
      have hpos : ∀ f ∈ coloringProfileFinset 0 0 t,
          (0 : ℝ) ≤ let fu : Fin 1 → ℕ := fun u => (f u).val
            (profileP 0 fu : ℝ) * (1 / 2 : ℝ) ^ profileF 0 fu / (profileSymm 0 fu : ℝ) :=
        fun f _ => div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)) (Nat.cast_nonneg _)
      linarith [zeroProfile_contribution t,
        Finset.single_le_sum hpos hmem]
    · have hmem := singletonsProfile_mem_finset n t hn ht
      have hpos : ∀ f ∈ coloringProfileFinset n n t,
          (0 : ℝ) ≤ let fu : Fin (n + 1) → ℕ := fun u => (f u).val
            (profileP n fu : ℝ) * (1 / 2 : ℝ) ^ profileF n fu / (profileSymm n fu : ℝ) :=
        fun f _ => div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)) (Nat.cast_nonneg _)
      simp only [expectedTBoundedColorings]
      linarith [singletonsProfile_contribution n hn,
        Finset.single_le_sum hpos hmem]
  have hk_le : k ≤ n := Nat.sub_le_of_le_add (hfmt_le.trans (Nat.le_add_right n 1))
  -- 0 ≤ E
  have hE_nn : (0 : ℝ) ≤ E := by
    apply mul_nonneg (Nat.cast_nonneg _)
    apply Finset.sum_nonneg; intro f _
    apply div_nonneg
    · apply mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)
    · exact Nat.cast_nonneg _
  -- Markov: ℙ[X ≥ 1] ≤ E[X] = E
  have hmarkov : gnHalf n {G : SimpleGraph (Fin n) | 1 ≤ classColoringCount n k t G} ≤
      ENNReal.ofReal E := by
    obtain ⟨hint, haeM⟩ := gnHalf_expected_tBoundedColoringCount n k t ht hk_le
    have hle : gnHalf n {G | 1 ≤ classColoringCount n k t G} ≤
        ∫⁻ G, (classColoringCount n k t G : ℝ≥0∞) ∂(gnHalf n) :=
      MeasureTheory.meas_le_lintegral₀
        (f := fun G => (classColoringCount n k t G : ℝ≥0∞))
        haeM
        (fun G hG => by
          simp only [Set.mem_setOf_eq] at hG
          simp only
          exact_mod_cast hG)
    rw [hint] at hle
    exact hle
  -- {ClassBoundedColoringExists G k t} ⊆ {X ≥ 1}
  have hset_sub : {G : SimpleGraph (Fin n) | ClassBoundedColoringExists n k t G} ⊆
      {G : SimpleGraph (Fin n) | 1 ≤ classColoringCount n k t G} := by
    intro G hG
    simp only [Set.mem_setOf_eq]
    exact (classColoringCount_pos_iff n k t G).mp hG
  have hprob_le : gnHalf n {G | ClassBoundedColoringExists n k t G} ≤ ENNReal.ofReal E :=
    (MeasureTheory.measure_mono hset_sub).trans hmarkov
  haveI : IsProbabilityMeasure (gnHalf n) := by unfold gnHalf; infer_instance
  have hcompl_sub : {G : SimpleGraph (Fin n) | ClassBoundedColoringExists n k t G}ᶜ ⊆
      {G : SimpleGraph (Fin n) | k ≤ classBoundedChromaticNumber n t G} := by
    intro G hG
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hG
    exact Nat.le_of_lt (classBoundedChromatic_ge_of_no_coloring G k t ht hG)
  haveI hprob := (inferInstance : IsProbabilityMeasure (gnHalf n))
  have hunion : Set.univ ⊆
      {G : SimpleGraph (Fin n) | k ≤ classBoundedChromaticNumber n t G} ∪
      {G : SimpleGraph (Fin n) | ClassBoundedColoringExists n k t G} := by
    intro G _
    by_cases hG : ClassBoundedColoringExists n k t G
    · exact Or.inr hG
    · exact Or.inl (Nat.le_of_lt (classBoundedChromatic_ge_of_no_coloring G k t ht hG))
  have hmeasure_ge : 1 ≤ gnHalf n {G | k ≤ classBoundedChromaticNumber n t G} +
      gnHalf n {G | ClassBoundedColoringExists n k t G} := by
    calc (1 : ℝ≥0∞) = gnHalf n Set.univ := (MeasureTheory.measure_univ).symm
      _ ≤ gnHalf n ({G | k ≤ classBoundedChromaticNumber n t G} ∪
            {G | ClassBoundedColoringExists n k t G}) :=
            MeasureTheory.measure_mono hunion
      _ ≤ gnHalf n {G | k ≤ classBoundedChromaticNumber n t G} +
            gnHalf n {G | ClassBoundedColoringExists n k t G} :=
            MeasureTheory.measure_union_le _ _
  have key : 1 - ENNReal.ofReal E ≤ gnHalf n {G | k ≤ classBoundedChromaticNumber n t G} := by
    set A := gnHalf n {G | k ≤ classBoundedChromaticNumber n t G}
    set B := gnHalf n {G | ClassBoundedColoringExists n k t G}
    rw [tsub_le_iff_right]
    calc (1 : ℝ≥0∞) ≤ A + B := hmeasure_ge
      _ ≤ A + ENNReal.ofReal E := by gcongr
  exact key

/-- Uniform-in-`n` form of `heckel_chi_t_lower_bound`.

The original theorem is already proved with witness `n₀ = 0`; this version exposes
that uniformity directly, which is convenient when `t` itself depends on `n`. -/
theorem heckel_chi_t_lower_bound_all_n (t : ℕ) (ht : 0 < t) :
    ∀ n : ℕ,
      t ∈ ({thresholdFloor n - 1, thresholdFloor n - 2} : Finset ℕ) →
      1 - ENNReal.ofReal (Nat.factorial (firstMomentThreshold n t ht - 1) *
          expectedTBoundedColorings n (firstMomentThreshold n t ht - 1) t) ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          firstMomentThreshold n t ht - 1 ≤ classBoundedChromaticNumber n t G} := by
  intro n htmem
  set k := firstMomentThreshold n t ht - 1
  set E := Nat.factorial k * expectedTBoundedColorings n k t
  have hfmt_le : firstMomentThreshold n t ht ≤ n := by
    apply Nat.find_min'
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [expectedTBoundedColorings]
      have hmem := zeroProfile_mem_finset t
      have hpos : ∀ f ∈ coloringProfileFinset 0 0 t,
          (0 : ℝ) ≤ let fu : Fin 1 → ℕ := fun u => (f u).val
            (profileP 0 fu : ℝ) * (1 / 2 : ℝ) ^ profileF 0 fu / (profileSymm 0 fu : ℝ) :=
        fun f _ => div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)) (Nat.cast_nonneg _)
      linarith [zeroProfile_contribution t,
        Finset.single_le_sum hpos hmem]
    · have hmem := singletonsProfile_mem_finset n t hn ht
      have hpos : ∀ f ∈ coloringProfileFinset n n t,
          (0 : ℝ) ≤ let fu : Fin (n + 1) → ℕ := fun u => (f u).val
            (profileP n fu : ℝ) * (1 / 2 : ℝ) ^ profileF n fu / (profileSymm n fu : ℝ) :=
        fun f _ => div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)) (Nat.cast_nonneg _)
      simp only [expectedTBoundedColorings]
      linarith [singletonsProfile_contribution n hn,
        Finset.single_le_sum hpos hmem]
  have hk_le : k ≤ n := Nat.sub_le_of_le_add (hfmt_le.trans (Nat.le_add_right n 1))
  have hE_nn : (0 : ℝ) ≤ E := by
    apply mul_nonneg (Nat.cast_nonneg _)
    apply Finset.sum_nonneg; intro f _
    apply div_nonneg
    · apply mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)
    · exact Nat.cast_nonneg _
  have hmarkov : gnHalf n {G : SimpleGraph (Fin n) | 1 ≤ classColoringCount n k t G} ≤
      ENNReal.ofReal E := by
    obtain ⟨hint, haeM⟩ := gnHalf_expected_tBoundedColoringCount n k t ht hk_le
    have hle : gnHalf n {G | 1 ≤ classColoringCount n k t G} ≤
        ∫⁻ G, (classColoringCount n k t G : ℝ≥0∞) ∂(gnHalf n) :=
      MeasureTheory.meas_le_lintegral₀
        (f := fun G => (classColoringCount n k t G : ℝ≥0∞))
        haeM
        (fun G hG => by
          simp only [Set.mem_setOf_eq] at hG
          simp only
          exact_mod_cast hG)
    rw [hint] at hle
    exact hle
  have hset_sub : {G : SimpleGraph (Fin n) | ClassBoundedColoringExists n k t G} ⊆
      {G : SimpleGraph (Fin n) | 1 ≤ classColoringCount n k t G} := by
    intro G hG
    simp only [Set.mem_setOf_eq]
    exact (classColoringCount_pos_iff n k t G).mp hG
  have hprob_le : gnHalf n {G | ClassBoundedColoringExists n k t G} ≤ ENNReal.ofReal E :=
    (MeasureTheory.measure_mono hset_sub).trans hmarkov
  haveI : IsProbabilityMeasure (gnHalf n) := by unfold gnHalf; infer_instance
  have hcompl_sub : {G : SimpleGraph (Fin n) | ClassBoundedColoringExists n k t G}ᶜ ⊆
      {G : SimpleGraph (Fin n) | k ≤ classBoundedChromaticNumber n t G} := by
    intro G hG
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hG
    exact Nat.le_of_lt (classBoundedChromatic_ge_of_no_coloring G k t ht hG)
  haveI hprob := (inferInstance : IsProbabilityMeasure (gnHalf n))
  have hunion : Set.univ ⊆
      {G : SimpleGraph (Fin n) | k ≤ classBoundedChromaticNumber n t G} ∪
      {G : SimpleGraph (Fin n) | ClassBoundedColoringExists n k t G} := by
    intro G _
    by_cases hG : ClassBoundedColoringExists n k t G
    · exact Or.inr hG
    · exact Or.inl (Nat.le_of_lt (classBoundedChromatic_ge_of_no_coloring G k t ht hG))
  have hmeasure_ge : 1 ≤ gnHalf n {G | k ≤ classBoundedChromaticNumber n t G} +
      gnHalf n {G | ClassBoundedColoringExists n k t G} := by
    calc (1 : ℝ≥0∞) = gnHalf n Set.univ := (MeasureTheory.measure_univ).symm
      _ ≤ gnHalf n ({G | k ≤ classBoundedChromaticNumber n t G} ∪
            {G | ClassBoundedColoringExists n k t G}) :=
            MeasureTheory.measure_mono hunion
      _ ≤ gnHalf n {G | k ≤ classBoundedChromaticNumber n t G} +
            gnHalf n {G | ClassBoundedColoringExists n k t G} :=
            MeasureTheory.measure_union_le _ _
  have key : 1 - ENNReal.ofReal E ≤ gnHalf n {G | k ≤ classBoundedChromaticNumber n t G} := by
    set A := gnHalf n {G | k ≤ classBoundedChromaticNumber n t G}
    set B := gnHalf n {G | ClassBoundedColoringExists n k t G}
    rw [tsub_le_iff_right]
    calc (1 : ℝ≥0∞) ≤ A + B := hmeasure_ge
      _ ≤ A + ENNReal.ofReal E := by gcongr
  exact key

end LowerBound

/-! ## Connection to the main axiom (Route D-2)

  The split proof in RouteD2.lean uses `kThresholdWitness` as the concrete witness `k_t`:
  ```
    k_t n := (firstMomentThreshold n (thresholdFloor n - 1) : ℝ)
  ```

  The theorem below shows that `heckel_chi_t_lower_bound` implies the χ lower-bound
  for this concrete k_t — modulo one remaining gap: connecting
  `boundedChromaticNumber G t ≥ k_t − 1` to `k_t - n^{1-0.9ε} ≤ chromaticNumber G`.

  The gap is bridged as follows (from Heckel 2024, §3.1):
  - χ_t(G) ≥ k_t − 1  (from Lemma 8.1)
  - χ(G) ≥ χ_t(G) − X_α where X_α is the count of α-sets
  - X_α ≤ n^{1-0.99ε} whp  (first moment bound in the main range)
  - Together: χ(G) ≥ k_t − 1 − n^{1-0.99ε} ≥ k_t − n^{1-0.9ε}  for large n
-/

section BridgeToRouteD2

/-- The concrete witness for k_t in the split proof:
  the (α−1)-bounded first moment threshold.
  We use `max 1 (thresholdFloor n - 1)` to guarantee the positivity requirement
  (for very small n, thresholdFloor n may be 0 or 1; the theorem is only used for large n). -/
noncomputable def kThresholdWitness (n : ℕ) : ℝ :=
  (firstMomentThreshold n (max 1 (thresholdFloor n - 1)) (Nat.lt_of_lt_of_le one_pos (le_max_left 1 _)) : ℝ)

/-- Helper: n^δ > C when n exceeds the Archimedean witness. -/
private lemma rpow_gt_of_large' (δ C : ℝ) (hδ : 0 < δ) (hC : 0 < C)
    (n n₀ : ℕ) (hn₀ : C^(δ⁻¹) < (n₀ : ℝ)) (hn : n₀ ≤ n) : (n : ℝ)^δ > C := by
  have h_n₀_pos : (0 : ℝ) < (n₀ : ℝ) := by linarith [Real.rpow_pos_of_pos hC δ⁻¹]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le (by exact_mod_cast h_n₀_pos) hn
  have hn_cast : (n₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have step1 : (C^(δ⁻¹))^δ < (n : ℝ)^δ :=
    Real.rpow_lt_rpow (le_of_lt (Real.rpow_pos_of_pos hC _)) (by linarith) hδ
  have step2 : (C^(δ⁻¹))^δ = C := by
    rw [← Real.rpow_mul (le_of_lt hC)]; field_simp; exact Real.rpow_one C
  linarith

lemma rpow_gap_ge_one (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (1 : ℝ) ≤ (n : ℝ)^(1 - 0.9 * ε) - (n : ℝ)^(1 - 0.99 * ε) := by
  -- Strategy: n^{1-0.9ε} = n^{1-0.99ε} · n^{0.09ε}.
  -- If n^{0.09ε} ≥ 2, then n^{1-0.9ε} ≥ 2 · n^{1-0.99ε} ≥ n^{1-0.99ε} + n^{1-0.99ε}.
  -- Since n^{1-0.99ε} ≥ 1 (for n ≥ 1), we get n^{1-0.9ε} − n^{1-0.99ε} ≥ 1.
  have hδ1 : (0 : ℝ) < 0.09 * ε := by linarith
  have hδ2 : (0 : ℝ) < 1 - 0.99 * ε := by nlinarith
  obtain ⟨n₁, hn₁⟩ := exists_nat_gt ((2 : ℝ)^((0.09 * ε)⁻¹))
  -- Also need n ≥ 1 so n^{1-0.99ε} ≥ 1
  -- n₁ > 2^{1/(0.09ε)} > 1, so n₁ ≥ 1 already
  use n₁
  intro n hn
  have hn₁n : (n₁ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- n > 0
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    have : (1 : ℝ) < (2 : ℝ)^((0.09 * ε)⁻¹) := Real.one_lt_rpow (by norm_num) (by positivity)
    linarith
  -- n^{0.09ε} > 2
  have h_exp : (n : ℝ)^(0.09 * ε) > 2 :=
    rpow_gt_of_large' (0.09 * ε) 2 hδ1 (by norm_num) n n₁ hn₁ hn
  -- n ≥ 1 as a real (n₁ > 2^... > 1, so n₁ ≥ 2, so n ≥ 2 > 1)
  have h_two_gt1 : (1 : ℝ) < (2 : ℝ)^((0.09 * ε)⁻¹) :=
    Real.one_lt_rpow (by norm_num) (by positivity)
  have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have h_base : (1 : ℝ) ≤ (n : ℝ)^(1 - 0.99 * ε) :=
    Real.one_le_rpow hn_ge1 (le_of_lt hδ2)
  -- n^{1-0.9ε} = n^{1-0.99ε} · n^{0.09ε}
  have h_split : (n : ℝ)^(1 - 0.9 * ε) = (n : ℝ)^(1 - 0.99 * ε) * (n : ℝ)^(0.09 * ε) := by
    rw [← Real.rpow_add hn_pos]; ring_nf
  -- n^{1-0.9ε} ≥ 2 · n^{1-0.99ε}
  have h_double : 2 * (n : ℝ)^(1 - 0.99 * ε) ≤ (n : ℝ)^(1 - 0.9 * ε) := by
    rw [h_split]
    have : (0 : ℝ) < (n : ℝ)^(1 - 0.99 * ε) := Real.rpow_pos_of_pos hn_pos _
    nlinarith
  linarith

/-- Step (B) reduced: deterministic arithmetic.
  Knowing χ_t ≥ k_t − 1, χ ≥ χ_t − n^{1-0.99ε}, and n^{1-0.9ε} − n^{1-0.99ε} ≥ 1:
  gives χ ≥ k_t − n^{1-0.9ε}.
-/
theorem chromatic_ge_kThreshold_sub_rpow
    {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    {G : SimpleGraph (Fin n)} {t : ℕ} {ht : 0 < t} (kt : ℕ)
    (hkt : kt = firstMomentThreshold n t ht)
    (h_chi_t  : (kt : ℝ) - 1 ≤ (boundedChromaticNumber G t : ℝ))
    (h_chi_ge : (boundedChromaticNumber G t : ℝ) ≤ (chromaticNumber G : ℝ))
    (h_alpha  : (chromaticNumber G : ℝ) ≥
                  (boundedChromaticNumber G t : ℝ) - (n : ℝ)^(1 - 0.99 * ε))
    (h_gap    : (1 : ℝ) ≤ (n : ℝ)^(1 - 0.9 * ε) - (n : ℝ)^(1 - 0.99 * ε)) :
    (kt : ℝ) - (n : ℝ)^(1 - 0.9 * ε) ≤ (chromaticNumber G : ℝ) := by
  -- From h_chi_t: k_t - 1 ≤ χ_t
  -- From h_chi_ge: χ_t ≤ χ
  -- From h_alpha: χ ≥ χ_t - n^{1-0.99ε} ≥ k_t - 1 - n^{1-0.99ε}
  -- From h_gap: n^{1-0.9ε} - n^{1-0.99ε} ≥ 1, i.e., k_t - n^{1-0.9ε} ≤ k_t - 1 - n^{1-0.99ε}
  linarith

end BridgeToRouteD2

end Problem625
