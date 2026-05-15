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



/-- Certified low-branch consequences consumed by the finite-profile
low-branch bridge.  This names the currently tuple-shaped handoff facts so the
remaining WHP source theorem can depend on a stable structured contract. -/
structure CertifiedConsequences : Prop where
  r2_exact_room_after_finite_margin :
    0 < roomR2ExactLower - roomR2FiniteLower
  r3_exact_room_after_finite_margin :
    0 < roomR3ExactLower - roomR3FiniteLower
  cutoff_below_half :
    lowCutoff < 1 / 2
  r2_finite_margin_lt_exact :
    roomR2FiniteLower < roomR2ExactLower
  r3_finite_margin_lt_exact :
    roomR3FiniteLower < roomR3ExactLower

/-- Any low-branch certificate leaves positive `r=2` room between the exact
transfer margin and the conservative finite margin. -/
theorem certified_r2_exact_room_after_finite_margin
    (hcert : Certificate) :
    0 < roomR2ExactLower - roomR2FiniteLower := by
  exact hcert.r2_exact_after_finite_pos

/-- Any low-branch certificate leaves positive `r=3` room between the exact
transfer margin and the conservative finite margin. -/
theorem certified_r3_exact_room_after_finite_margin
    (hcert : Certificate) :
    0 < roomR3ExactLower - roomR3FiniteLower := by
  exact hcert.r3_exact_after_finite_pos

/-- Any low-branch certificate keeps the low cutoff below the midpoint `1/2`. -/
theorem certified_low_cutoff_lt_half
    (hcert : Certificate) :
    lowCutoff < 1 / 2 := by
  exact hcert.cutoff_lt_half

/-- Any low-branch certificate keeps the conservative `r=2` finite margin
below the exact transfer margin. -/
theorem certified_r2_finite_margin_lt_exact
    (hcert : Certificate) :
    roomR2FiniteLower < roomR2ExactLower := by
  exact hcert.room_r2_finite_lt_exact

/-- Any low-branch certificate keeps the conservative `r=3` finite margin
below the exact transfer margin. -/
theorem certified_r3_finite_margin_lt_exact
    (hcert : Certificate) :
    roomR3FiniteLower < roomR3ExactLower := by
  exact hcert.room_r3_finite_lt_exact

/-- The concrete rational low-branch certificate supplies all currently
formalized interval-skeleton slack consequences. -/
theorem rational_certificate_interval_slack :
    (0 < roomR2ExactLower - roomR2FiniteLower) ∧
      (0 < roomR3ExactLower - roomR3FiniteLower) ∧
      lowCutoff < 1 / 2 := by
  exact ⟨
    certified_r2_exact_room_after_finite_margin rational_certificate,
    certified_r3_exact_room_after_finite_margin rational_certificate,
    certified_low_cutoff_lt_half rational_certificate
  ⟩

/-- A named bundle of the low-branch finite-profile margins already certified
by the concrete rational certificate.  This is the convenient handoff shape for
the next finite-profile lemma: both conservative finite margins leave positive
room below their exact transfer margins, and the low cutoff stays safely below
the midpoint. -/
theorem rational_certificate_paid_margin_bundle :
    (0 < roomR2ExactLower - roomR2FiniteLower) ∧
      (0 < roomR3ExactLower - roomR3FiniteLower) ∧
      lowCutoff < 1 / 2 := by
  exact rational_certificate_interval_slack

/-- The concrete rational low-branch certificate keeps the conservative
finite margins below their exact transfer margins. -/
theorem rational_certificate_finite_margins_lt_exact :
    roomR2FiniteLower < roomR2ExactLower ∧
      roomR3FiniteLower < roomR3ExactLower := by
  exact ⟨
    certified_r2_finite_margin_lt_exact rational_certificate,
    certified_r3_finite_margin_lt_exact rational_certificate
  ⟩

/-- Any low-branch certificate yields the structured low-branch consequence
bundle consumed by the finite-profile low-branch bridge. -/
theorem certified_consequences_of_certificate
    (hcert : Certificate) :
    CertifiedConsequences := by
  exact {
    r2_exact_room_after_finite_margin :=
      certified_r2_exact_room_after_finite_margin hcert
    r3_exact_room_after_finite_margin :=
      certified_r3_exact_room_after_finite_margin hcert
    cutoff_below_half :=
      certified_low_cutoff_lt_half hcert
    r2_finite_margin_lt_exact :=
      certified_r2_finite_margin_lt_exact hcert
    r3_finite_margin_lt_exact :=
      certified_r3_finite_margin_lt_exact hcert
  }

/-- Structured low-branch consequence bundle supplied by the concrete rational
certificate. -/
theorem rational_certificate_certified_consequences :
    CertifiedConsequences := by
  exact certified_consequences_of_certificate rational_certificate

/-- Source-side low-branch bridge input package.

This is the next structured handoff below the wrapper-level
`LowBranchBridgeInputs`: it keeps the rational certificate, the named
finite-margin consequences, and the tuple-shaped slack bundles together for
the eventual finite-profile WHP proof. -/
structure SourceBridgeInputs : Prop where
  certificate : Certificate
  certified_consequences : CertifiedConsequences
  paid_margin_bundle :
    (0 < roomR2ExactLower - roomR2FiniteLower) ∧
      (0 < roomR3ExactLower - roomR3FiniteLower) ∧
      lowCutoff < 1 / 2
  finite_margins_lt_exact :
    roomR2FiniteLower < roomR2ExactLower ∧
      roomR3FiniteLower < roomR3ExactLower

/-- Any low-branch certificate supplies the structured source-side bridge
input package used by the future finite-profile WHP proof. -/
theorem source_bridge_inputs_of_certificate
    (hcert : Certificate) :
    SourceBridgeInputs := by
  exact {
    certificate := hcert
    certified_consequences := certified_consequences_of_certificate hcert
    paid_margin_bundle := ⟨
      certified_r2_exact_room_after_finite_margin hcert,
      certified_r3_exact_room_after_finite_margin hcert,
      certified_low_cutoff_lt_half hcert
    ⟩
    finite_margins_lt_exact := ⟨
      certified_r2_finite_margin_lt_exact hcert,
      certified_r3_finite_margin_lt_exact hcert
    ⟩
  }

/-- Concrete source-side bridge input package supplied by the rational
low-branch certificate. -/
theorem rational_certificate_source_bridge_inputs :
    SourceBridgeInputs := by
  exact source_bridge_inputs_of_certificate rational_certificate

/-- Certificate projection from the concrete low source-side bridge input
package. -/
theorem rational_certificate_source_bridge_certificate :
    Certificate := by
  exact rational_certificate_source_bridge_inputs.certificate

/-- Certified-consequence projection from the concrete low source-side bridge
input package. -/
theorem rational_certificate_source_bridge_certified_consequences :
    CertifiedConsequences := by
  exact rational_certificate_source_bridge_inputs.certified_consequences

/-- `r=2` exact-room projection from the concrete low source-side bridge
certified consequences. -/
theorem rational_certificate_source_bridge_r2_exact_room_after_finite_margin :
    0 < roomR2ExactLower - roomR2FiniteLower := by
  exact rational_certificate_source_bridge_certified_consequences.r2_exact_room_after_finite_margin

/-- `r=3` exact-room projection from the concrete low source-side bridge
certified consequences. -/
theorem rational_certificate_source_bridge_r3_exact_room_after_finite_margin :
    0 < roomR3ExactLower - roomR3FiniteLower := by
  exact rational_certificate_source_bridge_certified_consequences.r3_exact_room_after_finite_margin

/-- Low-cutoff projection from the concrete low source-side bridge certified
consequences. -/
theorem rational_certificate_source_bridge_cutoff_below_half :
    lowCutoff < 1 / 2 := by
  exact rational_certificate_source_bridge_certified_consequences.cutoff_below_half

/-- `r=2` finite-margin comparison projection from the concrete low
source-side bridge certified consequences. -/
theorem rational_certificate_source_bridge_r2_finite_margin_lt_exact :
    roomR2FiniteLower < roomR2ExactLower := by
  exact rational_certificate_source_bridge_certified_consequences.r2_finite_margin_lt_exact

/-- `r=3` finite-margin comparison projection from the concrete low
source-side bridge certified consequences. -/
theorem rational_certificate_source_bridge_r3_finite_margin_lt_exact :
    roomR3FiniteLower < roomR3ExactLower := by
  exact rational_certificate_source_bridge_certified_consequences.r3_finite_margin_lt_exact

/-- Scalar certified-consequence readiness package extracted from the concrete
low source-side bridge input package. -/
theorem rational_certificate_source_bridge_scalar_ready_bundle :
    (0 < roomR2ExactLower - roomR2FiniteLower) ∧
      (0 < roomR3ExactLower - roomR3FiniteLower) ∧
      lowCutoff < 1 / 2 ∧
      roomR2FiniteLower < roomR2ExactLower ∧
      roomR3FiniteLower < roomR3ExactLower := by
  exact ⟨
    rational_certificate_source_bridge_r2_exact_room_after_finite_margin,
    rational_certificate_source_bridge_r3_exact_room_after_finite_margin,
    rational_certificate_source_bridge_cutoff_below_half,
    rational_certificate_source_bridge_r2_finite_margin_lt_exact,
    rational_certificate_source_bridge_r3_finite_margin_lt_exact
  ⟩

/-- Paid-margin projection from the concrete low source-side bridge input
package. -/
theorem rational_certificate_source_bridge_paid_margin_bundle :
    (0 < roomR2ExactLower - roomR2FiniteLower) ∧
      (0 < roomR3ExactLower - roomR3FiniteLower) ∧
      lowCutoff < 1 / 2 := by
  exact rational_certificate_source_bridge_inputs.paid_margin_bundle

/-- Finite-margin comparison projection from the concrete low source-side
bridge input package. -/
theorem rational_certificate_source_bridge_finite_margins_lt_exact :
    roomR2FiniteLower < roomR2ExactLower ∧
      roomR3FiniteLower < roomR3ExactLower := by
  exact rational_certificate_source_bridge_inputs.finite_margins_lt_exact

/-- Named scalar bridge-input contract for the concrete low branch.

This is the lightweight bridge shape for future finite-profile low WHP work:
the certificate plus the scalar margin facts extracted from the structured
source-side bridge input package. -/
def LowBranchScalarBridgeInputs : Prop :=
  Certificate ∧
    (0 < roomR2ExactLower - roomR2FiniteLower) ∧
    (0 < roomR3ExactLower - roomR3FiniteLower) ∧
    lowCutoff < 1 / 2 ∧
    roomR2FiniteLower < roomR2ExactLower ∧
    roomR3FiniteLower < roomR3ExactLower

/-- Current rational-certificate instance of the named low scalar bridge-input
contract. -/
theorem rational_certificate_scalar_bridge_inputs :
    LowBranchScalarBridgeInputs := by
  exact ⟨
    rational_certificate_source_bridge_certificate,
    rational_certificate_source_bridge_scalar_ready_bundle
  ⟩

/-- Certificate projection from the named low scalar bridge-input package. -/
theorem low_scalar_bridge_certificate :
    Certificate := by
  exact rational_certificate_scalar_bridge_inputs.1

/-- `r=2` exact-room projection from the named low scalar bridge-input
package. -/
theorem low_scalar_bridge_r2_exact_room_after_finite_margin :
    0 < roomR2ExactLower - roomR2FiniteLower := by
  exact rational_certificate_scalar_bridge_inputs.2.1

/-- `r=3` exact-room projection from the named low scalar bridge-input
package. -/
theorem low_scalar_bridge_r3_exact_room_after_finite_margin :
    0 < roomR3ExactLower - roomR3FiniteLower := by
  exact rational_certificate_scalar_bridge_inputs.2.2.1

/-- Low-cutoff projection from the named low scalar bridge-input package. -/
theorem low_scalar_bridge_cutoff_below_half :
    lowCutoff < 1 / 2 := by
  exact rational_certificate_scalar_bridge_inputs.2.2.2.1

/-- `r=2` finite-margin comparison projection from the named low scalar
bridge-input package. -/
theorem low_scalar_bridge_r2_finite_margin_lt_exact :
    roomR2FiniteLower < roomR2ExactLower := by
  exact rational_certificate_scalar_bridge_inputs.2.2.2.2.1

/-- `r=3` finite-margin comparison projection from the named low scalar
bridge-input package. -/
theorem low_scalar_bridge_r3_finite_margin_lt_exact :
    roomR3FiniteLower < roomR3ExactLower := by
  exact rational_certificate_scalar_bridge_inputs.2.2.2.2.2

/-- Paid-margin bundle projection from the named low scalar bridge-input
package. -/
theorem low_scalar_bridge_paid_margin_bundle :
    (0 < roomR2ExactLower - roomR2FiniteLower) ∧
      (0 < roomR3ExactLower - roomR3FiniteLower) ∧
      lowCutoff < 1 / 2 := by
  exact ⟨
    low_scalar_bridge_r2_exact_room_after_finite_margin,
    low_scalar_bridge_r3_exact_room_after_finite_margin,
    low_scalar_bridge_cutoff_below_half
  ⟩

/-- Finite-margin comparison bundle projection from the named low scalar
bridge-input package. -/
theorem low_scalar_bridge_finite_margins_lt_exact :
    roomR2FiniteLower < roomR2ExactLower ∧
      roomR3FiniteLower < roomR3ExactLower := by
  exact ⟨
    low_scalar_bridge_r2_finite_margin_lt_exact,
    low_scalar_bridge_r3_finite_margin_lt_exact
  ⟩


end Problem625.Analytical.LowBranch
