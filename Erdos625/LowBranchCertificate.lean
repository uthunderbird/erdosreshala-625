import Erdos625.Defs

/-!
# Low-branch certificate interface

This module records the Lean-facing numerical interface for the low-branch
quantitative splice package.

It does not formalize the low-branch WHP theorem yet.  It fixes the rational
constants and certificate-shaped positivity facts that the later exact-finite
and active-profile formalization should consume.
-/

namespace Problem625.Analytical.LowBranch

/-- Low-branch endpoint `x <= 0.029155`, represented exactly as a rational
decimal. -/
def lowCutoff : ℚ :=
  29155 / 1000000

/-- Conservative exact finite room margin for the `r=2` low-branch profile. -/
def roomR2FiniteLower : ℚ :=
  5 / 100

/-- Conservative exact finite room margin for the `r=3` low-branch profile. -/
def roomR3FiniteLower : ℚ :=
  1 / 100

/-- Earlier G4 exact transfer margin for `r=2`, before the final conservative
halving used in the low-branch finite objective note. -/
def roomR2ExactLower : ℚ :=
  1 / 10

/-- Earlier G4 exact transfer margin for `r=3`, before the final conservative
halving used in the low-branch finite objective note. -/
def roomR3ExactLower : ℚ :=
  2 / 100

/-- Certificate-shaped assumptions extracted from the low-branch finite
objective and quantitative splice notes.

Future work should replace uses of this structure by theorems connecting the
exact finite P3 profiles, endpoint split, shifted active profiles, and C5
active-profile theorem.
-/
structure Certificate : Prop where
  cutoff_pos : 0 < lowCutoff
  cutoff_lt_one : lowCutoff < 1
  room_r2_pos : 0 < roomR2FiniteLower
  room_r3_pos : 0 < roomR3FiniteLower
  room_r2_finite_lt_exact : roomR2FiniteLower < roomR2ExactLower
  room_r3_finite_lt_exact : roomR3FiniteLower < roomR3ExactLower
  r2_exact_after_finite_pos : 0 < roomR2ExactLower - roomR2FiniteLower
  r3_exact_after_finite_pos : 0 < roomR3ExactLower - roomR3FiniteLower
  cutoff_lt_half : lowCutoff < 1 / 2

/-- The rational constants appearing in the low-branch notes satisfy the
certificate ordering constraints. -/
theorem rational_certificate : Certificate := by
  constructor <;> norm_num [
    lowCutoff,
    roomR2FiniteLower,
    roomR3FiniteLower,
    roomR2ExactLower,
    roomR3ExactLower
  ]

/-- Both low-branch exact finite room reserves are positive. -/
theorem finite_room_reserves_pos :
    0 < roomR2FiniteLower ∧ 0 < roomR3FiniteLower := by
  exact ⟨rational_certificate.room_r2_pos, rational_certificate.room_r3_pos⟩

/-- The conservative finite margins are strictly below the exact transfer
margins quoted by the G4 closure note. -/
theorem finite_margins_below_exact_margins :
    roomR2FiniteLower < roomR2ExactLower ∧
      roomR3FiniteLower < roomR3ExactLower := by
  exact ⟨
    rational_certificate.room_r2_finite_lt_exact,
    rational_certificate.room_r3_finite_lt_exact
  ⟩

/-- The conservative `r=2` finite room leaves positive slack below the exact
transfer margin quoted by the G4 closure note. -/
theorem r2_exact_room_after_finite_margin_pos :
    0 < roomR2ExactLower - roomR2FiniteLower := by
  norm_num [
    roomR2ExactLower,
    roomR2FiniteLower
  ]

/-- The conservative `r=3` finite room leaves positive slack below the exact
transfer margin quoted by the G4 closure note. -/
theorem r3_exact_room_after_finite_margin_pos :
    0 < roomR3ExactLower - roomR3FiniteLower := by
  norm_num [
    roomR3ExactLower,
    roomR3FiniteLower
  ]

/-- The low cutoff is safely below the fixed-away-from-one midpoint `1/2`.
This records a simple rational separation used when routing the low interval
away from the middle/upper boundary. -/
theorem low_cutoff_lt_half :
    lowCutoff < 1 / 2 := by
  norm_num [lowCutoff]

end Problem625.Analytical.LowBranch
