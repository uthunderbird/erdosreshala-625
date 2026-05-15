import Erdos625.Defs

/-!
# Middle-branch certificate interface

This module records the Lean-facing numerical interface for the good-branch
partial-away-from-one package and the modified Lemma 7.20 certificate.

It does not formalize the middle-branch WHP theorem yet.  It fixes the
certificate-shaped constants that future formalization should consume.
-/

namespace Problem625.Analytical.MiddleBranch

/-- Good-branch lower handoff used in the wrapper. -/
def lowerCutoff : ℚ :=
  29155 / 1000000

/-- Fixed-away-from-one endpoint used by the current middle branch wrapper. -/
def upperCutoff : ℚ :=
  95 / 100

/-- Source epsilon cap from the good-branch theorem, `epsilon < 1/450`. -/
def sourceEpsilonCap : ℚ :=
  1 / 450

/-- Conservative lower envelope for the modified Lemma 7.10-ext certificate.

The source note records approximately `6.15e-7`; this file uses the smaller
exact rational `6e-7`.
-/
def lemma710ExtLowerEnvelope : ℚ :=
  6 / 10000000

/-- Certificate-shaped assumptions extracted from the middle-branch source
and modified Lemma 7.20 package.

Future work should replace uses of this structure by formal interval
arithmetic for Lemma 7.10-ext and Lean versions of the HP/Heckel good-branch
source machinery.
-/
structure Certificate : Prop where
  lower_cutoff_pos : 0 < lowerCutoff
  lower_lt_upper : lowerCutoff < upperCutoff
  upper_lt_one : upperCutoff < 1
  source_epsilon_pos : 0 < sourceEpsilonCap
  source_epsilon_small : sourceEpsilonCap < 1
  lemma710_lower_pos : 0 < lemma710ExtLowerEnvelope
  interval_width_pos : 0 < upperCutoff - lowerCutoff
  upper_room_to_one_pos : 0 < 1 - upperCutoff
  epsilon_below_upper_room : sourceEpsilonCap < 1 - upperCutoff
  lemma710_below_epsilon : lemma710ExtLowerEnvelope < sourceEpsilonCap

/-- The rational constants appearing in the middle-branch package satisfy the
certificate ordering constraints. -/
theorem rational_certificate : Certificate := by
  constructor <;> norm_num [
    lowerCutoff,
    upperCutoff,
    sourceEpsilonCap,
    lemma710ExtLowerEnvelope
  ]

/-- The middle branch interval is nonempty and lies below the upper boundary. -/
theorem middle_interval_order :
    0 < lowerCutoff ∧ lowerCutoff < upperCutoff ∧ upperCutoff < 1 := by
  exact ⟨
    rational_certificate.lower_cutoff_pos,
    rational_certificate.lower_lt_upper,
    rational_certificate.upper_lt_one
  ⟩

/-- The modified Lemma 7.10-ext certificate has a positive lower envelope. -/
theorem lemma710_lower_envelope_pos :
    0 < lemma710ExtLowerEnvelope := by
  exact rational_certificate.lemma710_lower_pos

/-- The middle interval has positive rational width between its lower and
upper cutoffs. -/
theorem middle_interval_width_pos :
    0 < upperCutoff - lowerCutoff := by
  norm_num [
    upperCutoff,
    lowerCutoff
  ]

/-- The upper middle cutoff stays a fixed rational distance below `1`. -/
theorem middle_upper_room_to_one_pos :
    0 < 1 - upperCutoff := by
  norm_num [upperCutoff]

/-- The source epsilon cap is far below the fixed room from the upper middle
cutoff to `1`. -/
theorem source_epsilon_below_upper_room :
    sourceEpsilonCap < 1 - upperCutoff := by
  norm_num [
    sourceEpsilonCap,
    upperCutoff
  ]

/-- The modified Lemma 7.10-ext lower envelope is below the source epsilon
cap, recording that it can be paid inside the source epsilon budget. -/
theorem lemma710_envelope_below_source_epsilon :
    lemma710ExtLowerEnvelope < sourceEpsilonCap := by
  norm_num [
    lemma710ExtLowerEnvelope,
    sourceEpsilonCap
  ]

end Problem625.Analytical.MiddleBranch
