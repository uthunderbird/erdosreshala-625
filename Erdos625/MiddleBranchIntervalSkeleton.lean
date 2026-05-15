import Erdos625.MiddleBranchCertificate

/-!
# Middle-branch interval skeleton

This module is the first Lean-side consumer of
`Problem625.Analytical.MiddleBranch.Certificate`.

It does not formalize the good-branch partial-away-from-one WHP source theorem.
It records certificate-to-slack consequences that the eventual modified
Lemma 7.20 and good-branch formalization should use when discharging
`good_branch_partial_away_from_one_loglog_whp_of_bridge_inputs`.
-/

namespace Problem625.Analytical.MiddleBranch

/-- Certified middle-branch consequences consumed by the modified Lemma 7.20
and good-branch bridge.  This names the currently tuple-shaped handoff facts so
the remaining WHP source theorem can depend on a stable structured contract. -/
structure CertifiedConsequences : Prop where
  interval_width :
    0 < upperCutoff - lowerCutoff
  upper_room_to_one :
    0 < 1 - upperCutoff
  source_epsilon_below_upper_room :
    sourceEpsilonCap < 1 - upperCutoff
  lemma710_envelope_below_source_epsilon :
    lemma710ExtLowerEnvelope < sourceEpsilonCap

/-- Any middle-branch certificate gives a nonempty interval between the lower
and upper cutoffs. -/
theorem certified_middle_interval_width
    (hcert : Certificate) :
    0 < upperCutoff - lowerCutoff := by
  exact hcert.interval_width_pos

/-- Any middle-branch certificate keeps the upper cutoff a positive distance
below `1`. -/
theorem certified_middle_upper_room_to_one
    (hcert : Certificate) :
    0 < 1 - upperCutoff := by
  exact hcert.upper_room_to_one_pos

/-- Any middle-branch certificate places the source epsilon budget below the
room from the upper cutoff to `1`. -/
theorem certified_source_epsilon_below_upper_room
    (hcert : Certificate) :
    sourceEpsilonCap < 1 - upperCutoff := by
  exact hcert.epsilon_below_upper_room

/-- Any middle-branch certificate places the modified Lemma 7.10-ext lower
envelope inside the source epsilon budget. -/
theorem certified_lemma710_envelope_below_source_epsilon
    (hcert : Certificate) :
    lemma710ExtLowerEnvelope < sourceEpsilonCap := by
  exact hcert.lemma710_below_epsilon

/-- The concrete rational middle-branch certificate supplies all currently
formalized interval-skeleton slack consequences. -/
theorem rational_certificate_interval_slack :
    (0 < upperCutoff - lowerCutoff) ∧
      (0 < 1 - upperCutoff) ∧
      sourceEpsilonCap < 1 - upperCutoff ∧
      lemma710ExtLowerEnvelope < sourceEpsilonCap := by
  exact ⟨
    certified_middle_interval_width rational_certificate,
    certified_middle_upper_room_to_one rational_certificate,
    certified_source_epsilon_below_upper_room rational_certificate,
    certified_lemma710_envelope_below_source_epsilon rational_certificate
  ⟩

/-- A named bundle of the middle-branch interval and epsilon payments already
certified by the concrete rational certificate.  This is the convenient
handoff shape for the next middle interval lemma: the middle interval has
positive width, the upper cutoff leaves room to `1`, the source epsilon fits
inside that room, and the Lemma 7.10-ext envelope fits inside the epsilon
budget. -/
theorem rational_certificate_paid_epsilon_bundle :
    (0 < upperCutoff - lowerCutoff) ∧
      (sourceEpsilonCap < 1 - upperCutoff) ∧
      (lemma710ExtLowerEnvelope < sourceEpsilonCap) ∧
      (0 < 1 - upperCutoff) := by
  exact ⟨
    rational_certificate_interval_slack.1,
    rational_certificate_interval_slack.2.2.1,
    rational_certificate_interval_slack.2.2.2,
    rational_certificate_interval_slack.2.1
  ⟩

/-- Any middle-branch certificate places the Lemma 7.10-ext envelope below the
source epsilon budget, and the source epsilon budget below the room from the
upper cutoff to `1`. -/
theorem certified_lemma710_epsilon_upper_room_chain
    (hcert : Certificate) :
    lemma710ExtLowerEnvelope < sourceEpsilonCap ∧
      sourceEpsilonCap < 1 - upperCutoff := by
  exact ⟨hcert.lemma710_below_epsilon, hcert.epsilon_below_upper_room⟩

/-- The concrete rational middle-branch certificate supplies the chain
`lemma710 envelope < epsilon cap < upper room`. -/
theorem rational_certificate_lemma710_epsilon_upper_room_chain :
    lemma710ExtLowerEnvelope < sourceEpsilonCap ∧
      sourceEpsilonCap < 1 - upperCutoff := by
  exact certified_lemma710_epsilon_upper_room_chain rational_certificate

/-- Any middle-branch certificate yields the structured middle-branch
consequence bundle consumed by the modified Lemma 7.20 and good-branch bridge. -/
theorem certified_consequences_of_certificate
    (hcert : Certificate) :
    CertifiedConsequences := by
  exact {
    interval_width :=
      certified_middle_interval_width hcert
    upper_room_to_one :=
      certified_middle_upper_room_to_one hcert
    source_epsilon_below_upper_room :=
      certified_source_epsilon_below_upper_room hcert
    lemma710_envelope_below_source_epsilon :=
      certified_lemma710_envelope_below_source_epsilon hcert
  }

/-- Structured middle-branch consequence bundle supplied by the concrete
rational certificate. -/
theorem rational_certificate_certified_consequences :
    CertifiedConsequences := by
  exact certified_consequences_of_certificate rational_certificate

/-- Source-side middle-branch bridge input package.

This is the structured handoff below the wrapper-level
`MiddleBranchBridgeInputs`: it keeps the rational certificate, the named
epsilon-budget consequences, the paid epsilon bundle, and the Lemma 7.10-ext
epsilon-room chain together for the eventual good-branch WHP proof. -/
structure SourceBridgeInputs : Prop where
  certificate : Certificate
  certified_consequences : CertifiedConsequences
  paid_epsilon_bundle :
    (0 < upperCutoff - lowerCutoff) ∧
      (sourceEpsilonCap < 1 - upperCutoff) ∧
      (lemma710ExtLowerEnvelope < sourceEpsilonCap) ∧
      (0 < 1 - upperCutoff)
  lemma710_epsilon_upper_room_chain :
    lemma710ExtLowerEnvelope < sourceEpsilonCap ∧
      sourceEpsilonCap < 1 - upperCutoff

/-- Any middle-branch certificate supplies the structured source-side bridge
input package used by the future good-branch WHP proof. -/
theorem source_bridge_inputs_of_certificate
    (hcert : Certificate) :
    SourceBridgeInputs := by
  exact {
    certificate := hcert
    certified_consequences := certified_consequences_of_certificate hcert
    paid_epsilon_bundle := ⟨
      certified_middle_interval_width hcert,
      certified_source_epsilon_below_upper_room hcert,
      certified_lemma710_envelope_below_source_epsilon hcert,
      certified_middle_upper_room_to_one hcert
    ⟩
    lemma710_epsilon_upper_room_chain :=
      certified_lemma710_epsilon_upper_room_chain hcert
  }

/-- Concrete source-side bridge input package supplied by the rational
middle-branch certificate. -/
theorem rational_certificate_source_bridge_inputs :
    SourceBridgeInputs := by
  exact source_bridge_inputs_of_certificate rational_certificate

/-- Certificate projection from the concrete middle source-side bridge input
package. -/
theorem rational_certificate_source_bridge_certificate :
    Certificate := by
  exact rational_certificate_source_bridge_inputs.certificate

/-- Certified-consequence projection from the concrete middle source-side
bridge input package. -/
theorem rational_certificate_source_bridge_certified_consequences :
    CertifiedConsequences := by
  exact rational_certificate_source_bridge_inputs.certified_consequences

/-- Interval-width projection from the concrete middle source-side bridge
certified consequences. -/
theorem rational_certificate_source_bridge_interval_width :
    0 < upperCutoff - lowerCutoff := by
  exact rational_certificate_source_bridge_certified_consequences.interval_width

/-- Upper-room projection from the concrete middle source-side bridge
certified consequences. -/
theorem rational_certificate_source_bridge_upper_room_to_one :
    0 < 1 - upperCutoff := by
  exact rational_certificate_source_bridge_certified_consequences.upper_room_to_one

/-- Source-epsilon room projection from the concrete middle source-side bridge
certified consequences. -/
theorem rational_certificate_source_bridge_epsilon_below_upper_room :
    sourceEpsilonCap < 1 - upperCutoff := by
  exact rational_certificate_source_bridge_certified_consequences.source_epsilon_below_upper_room

/-- Lemma 7.10 envelope projection from the concrete middle source-side bridge
certified consequences. -/
theorem rational_certificate_source_bridge_lemma710_below_epsilon :
    lemma710ExtLowerEnvelope < sourceEpsilonCap := by
  exact rational_certificate_source_bridge_certified_consequences.lemma710_envelope_below_source_epsilon

/-- Scalar certified-consequence readiness package extracted from the concrete
middle source-side bridge input package. -/
theorem rational_certificate_source_bridge_scalar_ready_bundle :
    (0 < upperCutoff - lowerCutoff) ∧
      (0 < 1 - upperCutoff) ∧
      sourceEpsilonCap < 1 - upperCutoff ∧
      lemma710ExtLowerEnvelope < sourceEpsilonCap := by
  exact ⟨
    rational_certificate_source_bridge_interval_width,
    rational_certificate_source_bridge_upper_room_to_one,
    rational_certificate_source_bridge_epsilon_below_upper_room,
    rational_certificate_source_bridge_lemma710_below_epsilon
  ⟩

/-- Paid-epsilon projection from the concrete middle source-side bridge input
package. -/
theorem rational_certificate_source_bridge_paid_epsilon_bundle :
    (0 < upperCutoff - lowerCutoff) ∧
      (sourceEpsilonCap < 1 - upperCutoff) ∧
      (lemma710ExtLowerEnvelope < sourceEpsilonCap) ∧
      (0 < 1 - upperCutoff) := by
  exact rational_certificate_source_bridge_inputs.paid_epsilon_bundle

/-- Lemma 7.10 envelope/epsilon/room chain projection from the concrete middle
source-side bridge input package. -/
theorem rational_certificate_source_bridge_lemma710_epsilon_upper_room_chain :
    lemma710ExtLowerEnvelope < sourceEpsilonCap ∧
      sourceEpsilonCap < 1 - upperCutoff := by
  exact rational_certificate_source_bridge_inputs.lemma710_epsilon_upper_room_chain

/-- Named scalar bridge-input contract for the concrete middle branch.

This is the lightweight bridge shape for future good-branch WHP work: the
certificate plus the scalar interval/epsilon facts extracted from the
structured source-side bridge input package. -/
def MiddleBranchScalarBridgeInputs : Prop :=
  Certificate ∧
    (0 < upperCutoff - lowerCutoff) ∧
    (0 < 1 - upperCutoff) ∧
    sourceEpsilonCap < 1 - upperCutoff ∧
    lemma710ExtLowerEnvelope < sourceEpsilonCap

/-- Current rational-certificate instance of the named middle scalar
bridge-input contract. -/
theorem rational_certificate_scalar_bridge_inputs :
    MiddleBranchScalarBridgeInputs := by
  exact ⟨
    rational_certificate_source_bridge_certificate,
    rational_certificate_source_bridge_scalar_ready_bundle
  ⟩

/-- Certificate projection from the named middle scalar bridge-input package. -/
theorem middle_scalar_bridge_certificate :
    Certificate := by
  exact rational_certificate_scalar_bridge_inputs.1

/-- Interval-width projection from the named middle scalar bridge-input
package. -/
theorem middle_scalar_bridge_interval_width :
    0 < upperCutoff - lowerCutoff := by
  exact rational_certificate_scalar_bridge_inputs.2.1

/-- Upper-room projection from the named middle scalar bridge-input package. -/
theorem middle_scalar_bridge_upper_room_to_one :
    0 < 1 - upperCutoff := by
  exact rational_certificate_scalar_bridge_inputs.2.2.1

/-- Source-epsilon room projection from the named middle scalar bridge-input
package. -/
theorem middle_scalar_bridge_epsilon_below_upper_room :
    sourceEpsilonCap < 1 - upperCutoff := by
  exact rational_certificate_scalar_bridge_inputs.2.2.2.1

/-- Lemma 7.10 envelope projection from the named middle scalar bridge-input
package. -/
theorem middle_scalar_bridge_lemma710_below_epsilon :
    lemma710ExtLowerEnvelope < sourceEpsilonCap := by
  exact rational_certificate_scalar_bridge_inputs.2.2.2.2

end Problem625.Analytical.MiddleBranch
