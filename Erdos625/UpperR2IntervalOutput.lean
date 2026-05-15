import Erdos625.UpperR2IntervalSkeleton

/-!
# Upper-boundary `r=2` interval-output component

This module is the first dedicated Lean-facing home for actual upper
interval-output components.

At this stage the endpoint quantities are represented by the appendix table
constants themselves.  Future interval-arithmetic work should replace these
constants-level components by theorems about the real endpoint quantities
computed from the upper-boundary appendix.
-/

namespace Problem625.Analytical.UpperR2

/-- Lean-facing lower endpoint quantity for the upper `Room_2(1)` table. -/
def roomEndpointLower : ℚ :=
  roomEndpointTableLower

/-- Lean-facing lower endpoint quantity for the tight upper prefix guard. -/
def prefixEndpointLower : ℚ :=
  tightPrefixTableLower

/-- Lean-facing upper endpoint quantity for the current upper tail ratio. -/
def tailEndpointActual : ℚ :=
  tailRatioUpper

/-- Lean-facing `p_2` lower endpoint quantity for the current component proof.

This is deliberately equal to the appendix reciprocal lower endpoint for now;
it gives the future interval proof a stable name to replace or refine. -/
def p2EndpointLower : ℚ :=
  1 / p2AppendixDenomUpper

/-- The current named `p_2` endpoint component satisfies the reciprocal-output
contract.  This is the first component theorem to be replaced by a genuine
interval endpoint proof. -/
theorem p2_endpoint_reciprocal_output :
    P2ReciprocalOutput p2EndpointLower := by
  dsimp [p2EndpointLower]
  exact appendix_constant_p2_reciprocal_output

/-- The named `p_2` endpoint component yields the certified admissibility
inequalities needed by the upper branch. -/
theorem p2_endpoint_admissibility_ready :
    delta < p2EndpointLower ∧
      p2CertifiedLower < p2EndpointLower := by
  exact p2_admissibility_of_reciprocal_output
    p2_endpoint_reciprocal_output

/-- The named `p_2` endpoint lower bound is positive.

This exposes the positivity side condition that future reciprocal endpoint
interval proofs normally need, without unfolding the appendix constant at each
call site. -/
theorem p2_endpoint_lower_pos :
    0 < p2EndpointLower := by
  dsimp [p2EndpointLower]
  exact rational_certificate_p2_reciprocal_admissibility_ready.2.2.1

/-- Bundled readiness facts for the named `p_2` endpoint lower bound. -/
theorem p2_endpoint_ready_bundle :
    P2ReciprocalOutput p2EndpointLower ∧
      delta < p2EndpointLower ∧
      p2CertifiedLower < p2EndpointLower ∧
      0 < p2EndpointLower := by
  exact ⟨
    p2_endpoint_reciprocal_output,
    p2_endpoint_admissibility_ready.1,
    p2_endpoint_admissibility_ready.2,
    p2_endpoint_lower_pos
  ⟩

/-- The named upper room endpoint lower bound is positive. -/
theorem room_endpoint_lower_pos :
    0 < roomEndpointLower := by
  dsimp [roomEndpointLower]
  exact lt_trans
    rational_certificate.room_pos
    rational_certificate_table_support_ready.1

/-- The named tight prefix endpoint lower bound is positive. -/
theorem prefix_endpoint_lower_pos :
    0 < prefixEndpointLower := by
  dsimp [prefixEndpointLower]
  exact lt_trans
    rational_certificate.prefix_pos
    rational_certificate_table_support_ready.2

/-- The named upper tail endpoint quantity is positive. -/
theorem tail_endpoint_actual_pos :
    0 < tailEndpointActual := by
  dsimp [tailEndpointActual, tailRatioUpper]
  norm_num

/-- Bundled positivity side conditions for the named upper appendix endpoints. -/
theorem upper_appendix_endpoint_pos :
    0 < roomEndpointLower ∧
      0 < prefixEndpointLower ∧
      0 < tailEndpointActual ∧
      0 < p2EndpointLower := by
  exact ⟨
    room_endpoint_lower_pos,
    prefix_endpoint_lower_pos,
    tail_endpoint_actual_pos,
    p2_endpoint_lower_pos
  ⟩

/-- Current Lean-facing upper interval-output theorem for the named appendix
endpoint quantities.

This is still constants-level: it packages the appendix endpoint constants
under the exact `IntervalOutputs` contract that the next real interval
arithmetic theorem should target and eventually replace. -/
theorem upper_appendix_interval_outputs :
    IntervalOutputs
      roomEndpointLower
      prefixEndpointLower
      tailEndpointActual
      p2EndpointLower := by
  dsimp [
    roomEndpointLower,
    prefixEndpointLower,
    tailEndpointActual,
    p2EndpointLower,
  ]
  exact appendix_constant_interval_outputs

/-- Named endpoint/table inequalities extracted from the current appendix
interval-output package.

This is a small bridge for the next replacement step: a genuine interval
endpoint proof should establish these four inequalities for computed endpoint
quantities, then feed the same `IntervalOutputs` consumer path below. -/
theorem upper_appendix_endpoint_table_facts :
    roomEndpointTableLower ≤ roomEndpointLower ∧
      tightPrefixTableLower ≤ prefixEndpointLower ∧
      tailEndpointActual ≤ tailRatioUpper ∧
      1 / p2AppendixDenomUpper ≤ p2EndpointLower := by
  have h := upper_appendix_interval_outputs
  exact ⟨
    h.room_table_lower,
    h.prefix_table_lower,
    h.tail_upper,
    h.p2_reciprocal_lower
  ⟩

/-- Named room endpoint table fact for the current upper appendix output. -/
theorem room_endpoint_table_lower_ready :
    roomEndpointTableLower ≤ roomEndpointLower := by
  exact upper_appendix_endpoint_table_facts.1

/-- Named prefix endpoint table fact for the current upper appendix output. -/
theorem prefix_endpoint_table_lower_ready :
    tightPrefixTableLower ≤ prefixEndpointLower := by
  exact upper_appendix_endpoint_table_facts.2.1

/-- Named tail endpoint upper fact for the current upper appendix output. -/
theorem tail_endpoint_upper_ready :
    tailEndpointActual ≤ tailRatioUpper := by
  exact upper_appendix_endpoint_table_facts.2.2.1

/-- Bundled table-bound and positivity facts for the named upper endpoint
quantities other than the reciprocal `p_2` component. -/
theorem upper_appendix_endpoint_table_pos_bundle :
    roomEndpointTableLower ≤ roomEndpointLower ∧
      0 < roomEndpointLower ∧
      tightPrefixTableLower ≤ prefixEndpointLower ∧
      0 < prefixEndpointLower ∧
      tailEndpointActual ≤ tailRatioUpper ∧
      0 < tailEndpointActual := by
  exact ⟨
    room_endpoint_table_lower_ready,
    room_endpoint_lower_pos,
    prefix_endpoint_table_lower_ready,
    prefix_endpoint_lower_pos,
    tail_endpoint_upper_ready,
    tail_endpoint_actual_pos
  ⟩

/-- Named `p_2` reciprocal endpoint lower fact for the current upper appendix
output. -/
theorem p2_endpoint_reciprocal_lower_ready :
    1 / p2AppendixDenomUpper ≤ p2EndpointLower := by
  exact upper_appendix_endpoint_table_facts.2.2.2

/-- Combined endpoint readiness package for the current upper appendix output:
table bounds and positivity for room/prefix/tail, plus reciprocal output,
admissibility, and positivity for `p_2`. -/
theorem upper_appendix_endpoint_ready_bundle :
    (roomEndpointTableLower ≤ roomEndpointLower ∧
      0 < roomEndpointLower ∧
      tightPrefixTableLower ≤ prefixEndpointLower ∧
      0 < prefixEndpointLower ∧
      tailEndpointActual ≤ tailRatioUpper ∧
      0 < tailEndpointActual) ∧
      (P2ReciprocalOutput p2EndpointLower ∧
        delta < p2EndpointLower ∧
        p2CertifiedLower < p2EndpointLower ∧
        0 < p2EndpointLower) := by
  exact ⟨
    upper_appendix_endpoint_table_pos_bundle,
    p2_endpoint_ready_bundle
  ⟩

/-- The current named room endpoint component satisfies the table-lower
contract. -/
theorem room_endpoint_output :
    RoomEndpointOutput roomEndpointLower := by
  exact { table_lower := room_endpoint_table_lower_ready }

/-- The current named tight-prefix endpoint component satisfies the table-lower
contract. -/
theorem prefix_endpoint_output :
    PrefixEndpointOutput prefixEndpointLower := by
  exact { table_lower := prefix_endpoint_table_lower_ready }

/-- The current named upper-tail endpoint component satisfies the tail-upper
contract. -/
theorem tail_endpoint_output :
    TailEndpointOutput tailEndpointActual := by
  exact { tail_upper := tail_endpoint_upper_ready }

/-- Bundled current endpoint components for the upper appendix output. -/
theorem upper_appendix_endpoint_components :
    UpperEndpointComponents
      roomEndpointLower
      prefixEndpointLower
      tailEndpointActual
      p2EndpointLower := by
  exact {
    room := room_endpoint_output
    pref := prefix_endpoint_output
    tail_component := tail_endpoint_output
    p2 := p2_endpoint_reciprocal_output
  }

/-- Combined component and side-condition package for the current upper
appendix endpoints. -/
theorem upper_appendix_endpoint_components_ready_bundle :
    UpperEndpointComponents
        roomEndpointLower
        prefixEndpointLower
        tailEndpointActual
        p2EndpointLower ∧
      ((roomEndpointTableLower ≤ roomEndpointLower ∧
        0 < roomEndpointLower ∧
        tightPrefixTableLower ≤ prefixEndpointLower ∧
        0 < prefixEndpointLower ∧
        tailEndpointActual ≤ tailRatioUpper ∧
        0 < tailEndpointActual) ∧
        (P2ReciprocalOutput p2EndpointLower ∧
          delta < p2EndpointLower ∧
          p2CertifiedLower < p2EndpointLower ∧
          0 < p2EndpointLower)) := by
  exact ⟨
    upper_appendix_endpoint_components,
    upper_appendix_endpoint_ready_bundle
  ⟩

/-- Reassemble the upper appendix `IntervalOutputs` contract from the four
named endpoint facts.

Future interval arithmetic can replace the four ready facts above while
preserving this package-level consumer theorem. -/
theorem upper_appendix_interval_outputs_of_endpoint_facts :
    IntervalOutputs
      roomEndpointLower
      prefixEndpointLower
      tailEndpointActual
      p2EndpointLower := by
  exact interval_outputs_of_component_bundle
    upper_appendix_endpoint_components

/-- Compatibility name showing that the current constants-level appendix
package is available through the endpoint-facts route. -/
theorem upper_appendix_interval_outputs_ready :
    IntervalOutputs
      roomEndpointLower
      prefixEndpointLower
      tailEndpointActual
      p2EndpointLower := by
  exact upper_appendix_interval_outputs_of_endpoint_facts

/-- Combined interval-output and endpoint-readiness package for the current
upper appendix output layer. -/
theorem upper_appendix_interval_outputs_ready_bundle :
    IntervalOutputs
        roomEndpointLower
        prefixEndpointLower
        tailEndpointActual
        p2EndpointLower ∧
      UpperEndpointComponents
        roomEndpointLower
        prefixEndpointLower
        tailEndpointActual
        p2EndpointLower ∧
      ((roomEndpointTableLower ≤ roomEndpointLower ∧
        0 < roomEndpointLower ∧
        tightPrefixTableLower ≤ prefixEndpointLower ∧
        0 < prefixEndpointLower ∧
        tailEndpointActual ≤ tailRatioUpper ∧
        0 < tailEndpointActual) ∧
        (P2ReciprocalOutput p2EndpointLower ∧
          delta < p2EndpointLower ∧
          p2CertifiedLower < p2EndpointLower ∧
          0 < p2EndpointLower)) := by
  exact ⟨
    upper_appendix_interval_outputs_ready,
    upper_appendix_endpoint_components_ready_bundle
  ⟩

/-- The named appendix endpoint package yields the certified consequences
expected by the upper assembly.

This theorem is the direct replacement point for a future genuine interval
endpoint theorem: once `upper_appendix_interval_outputs` is replaced by an
actual interval proof, this consumer should remain unchanged. -/
theorem upper_appendix_certified_consequences :
    CertifiedConsequences
      roomEndpointLower
      prefixEndpointLower
      tailEndpointActual
      p2EndpointLower := by
  exact certified_consequences_of_components
    room_endpoint_output
    prefix_endpoint_output
    tail_endpoint_output
    p2_endpoint_reciprocal_output

/-- Certified consequences bundled with the endpoint readiness package for the
current upper appendix output layer. -/
theorem upper_appendix_certified_consequences_ready_bundle :
    CertifiedConsequences
        roomEndpointLower
        prefixEndpointLower
        tailEndpointActual
        p2EndpointLower ∧
      IntervalOutputs
        roomEndpointLower
        prefixEndpointLower
        tailEndpointActual
        p2EndpointLower ∧
      UpperEndpointComponents
        roomEndpointLower
        prefixEndpointLower
        tailEndpointActual
        p2EndpointLower ∧
      ((roomEndpointTableLower ≤ roomEndpointLower ∧
        0 < roomEndpointLower ∧
        tightPrefixTableLower ≤ prefixEndpointLower ∧
        0 < prefixEndpointLower ∧
        tailEndpointActual ≤ tailRatioUpper ∧
        0 < tailEndpointActual) ∧
        (P2ReciprocalOutput p2EndpointLower ∧
          delta < p2EndpointLower ∧
          p2CertifiedLower < p2EndpointLower ∧
          0 < p2EndpointLower)) := by
  exact ⟨
    upper_appendix_certified_consequences,
    upper_appendix_interval_outputs_ready_bundle
  ⟩

/-- The named appendix endpoint package, together with the static upper
payment inequalities, is ready for the upper assembly consumer. -/
theorem upper_appendix_consequences_with_payment :
    ((shiftCertifiedUpper + finalGapCoefficient + tailRatioUpper <
      prefixCertifiedLower) ∧
      (prefixCertifiedLower + tailRatioUpper < roomCertifiedLower) ∧
      0 < finalGapCoefficient) ∧
      CertifiedConsequences
        roomEndpointLower
        prefixEndpointLower
        tailEndpointActual
        p2EndpointLower := by
  exact certified_consequences_with_payment_of_component_bundle
    upper_appendix_endpoint_components

/-- Stable ready name for the certified consequences exposed by the current
upper appendix interval-output layer. -/
theorem upper_appendix_certified_consequences_ready :
    CertifiedConsequences
      roomEndpointLower
      prefixEndpointLower
      tailEndpointActual
      p2EndpointLower := by
  exact upper_appendix_certified_consequences

/-- Stable ready name for the upper appendix consequences together with the
payment inequalities expected by the upper assembly. -/
theorem upper_appendix_consequences_with_payment_ready :
    ((shiftCertifiedUpper + finalGapCoefficient + tailRatioUpper <
      prefixCertifiedLower) ∧
      (prefixCertifiedLower + tailRatioUpper < roomCertifiedLower) ∧
      0 < finalGapCoefficient) ∧
      CertifiedConsequences
        roomEndpointLower
        prefixEndpointLower
        tailEndpointActual
        p2EndpointLower := by
  exact upper_appendix_consequences_with_payment

/-- Payment-ready consequences bundled with the endpoint and certified
consequence readiness package for the current upper appendix output layer. -/
theorem upper_appendix_consequences_with_payment_ready_bundle :
    (((shiftCertifiedUpper + finalGapCoefficient + tailRatioUpper <
      prefixCertifiedLower) ∧
      (prefixCertifiedLower + tailRatioUpper < roomCertifiedLower) ∧
      0 < finalGapCoefficient) ∧
      CertifiedConsequences
        roomEndpointLower
        prefixEndpointLower
        tailEndpointActual
        p2EndpointLower) ∧
      CertifiedConsequences
        roomEndpointLower
        prefixEndpointLower
        tailEndpointActual
        p2EndpointLower ∧
      IntervalOutputs
        roomEndpointLower
        prefixEndpointLower
        tailEndpointActual
        p2EndpointLower ∧
      UpperEndpointComponents
        roomEndpointLower
        prefixEndpointLower
        tailEndpointActual
        p2EndpointLower ∧
      ((roomEndpointTableLower ≤ roomEndpointLower ∧
        0 < roomEndpointLower ∧
        tightPrefixTableLower ≤ prefixEndpointLower ∧
        0 < prefixEndpointLower ∧
        tailEndpointActual ≤ tailRatioUpper ∧
        0 < tailEndpointActual) ∧
        (P2ReciprocalOutput p2EndpointLower ∧
          delta < p2EndpointLower ∧
          p2CertifiedLower < p2EndpointLower ∧
          0 < p2EndpointLower)) := by
  exact ⟨
    upper_appendix_consequences_with_payment_ready,
    upper_appendix_certified_consequences_ready_bundle
  ⟩

/-- Named contract for the complete upper `r=2` interval-output layer package.

This is the upper-module home for the output layer consumed by the analytical
wrapper.  It packages the endpoint-table facts, the `IntervalOutputs` contract,
the certified consequences, and the payment-ready consequences under one
stable type name. -/
def UpperR2OutputLayer : Prop :=
  (roomEndpointTableLower ≤ roomEndpointLower ∧
    tightPrefixTableLower ≤ prefixEndpointLower ∧
    tailEndpointActual ≤ tailRatioUpper ∧
    1 / p2AppendixDenomUpper ≤ p2EndpointLower) ∧
    IntervalOutputs
      roomEndpointLower
      prefixEndpointLower
      tailEndpointActual
      p2EndpointLower ∧
    CertifiedConsequences
      roomEndpointLower
      prefixEndpointLower
      tailEndpointActual
      p2EndpointLower ∧
    ((shiftCertifiedUpper + finalGapCoefficient + tailRatioUpper <
      prefixCertifiedLower) ∧
      (prefixCertifiedLower + tailRatioUpper < roomCertifiedLower) ∧
      0 < finalGapCoefficient) ∧
      CertifiedConsequences
        roomEndpointLower
        prefixEndpointLower
        tailEndpointActual
        p2EndpointLower

/-- Build the complete upper output layer from the bundled endpoint-component
contract.  This is the direct consumer for a future genuine interval endpoint
proof over the named upper appendix quantities. -/
theorem upper_output_layer_of_endpoint_components
    (hcomponents :
      UpperEndpointComponents
        roomEndpointLower
        prefixEndpointLower
        tailEndpointActual
        p2EndpointLower) :
    UpperR2OutputLayer := by
  let houtputs := interval_outputs_of_component_bundle hcomponents
  exact ⟨
    ⟨
      houtputs.room_table_lower,
      houtputs.prefix_table_lower,
      houtputs.tail_upper,
      houtputs.p2_reciprocal_lower
    ⟩,
    houtputs,
    certified_consequences_of_components
      hcomponents.room
      hcomponents.pref
      hcomponents.tail_component
      hcomponents.p2,
    certified_consequences_with_payment_of_component_bundle hcomponents
  ⟩

/-- Single assembly-facing bundle for the current upper appendix output layer.

This packages the endpoint-table facts, the `IntervalOutputs` contract, the
certified consequences, and the payment-ready consequences under one stable
name for the future upper analytical bridge. -/
theorem upper_appendix_output_layer_ready :
    UpperR2OutputLayer := by
  exact upper_output_layer_of_endpoint_components
    upper_appendix_endpoint_components

/-- Complete upper output layer bundled with the payment and endpoint
readiness package for the current appendix output. -/
theorem upper_appendix_output_layer_ready_bundle :
    UpperR2OutputLayer ∧
      (((shiftCertifiedUpper + finalGapCoefficient + tailRatioUpper <
        prefixCertifiedLower) ∧
        (prefixCertifiedLower + tailRatioUpper < roomCertifiedLower) ∧
        0 < finalGapCoefficient) ∧
        CertifiedConsequences
          roomEndpointLower
          prefixEndpointLower
          tailEndpointActual
          p2EndpointLower) ∧
      CertifiedConsequences
        roomEndpointLower
        prefixEndpointLower
        tailEndpointActual
        p2EndpointLower ∧
      IntervalOutputs
        roomEndpointLower
        prefixEndpointLower
        tailEndpointActual
        p2EndpointLower ∧
      UpperEndpointComponents
        roomEndpointLower
        prefixEndpointLower
        tailEndpointActual
        p2EndpointLower ∧
      ((roomEndpointTableLower ≤ roomEndpointLower ∧
        0 < roomEndpointLower ∧
        tightPrefixTableLower ≤ prefixEndpointLower ∧
        0 < prefixEndpointLower ∧
        tailEndpointActual ≤ tailRatioUpper ∧
        0 < tailEndpointActual) ∧
        (P2ReciprocalOutput p2EndpointLower ∧
          delta < p2EndpointLower ∧
          p2CertifiedLower < p2EndpointLower ∧
          0 < p2EndpointLower)) := by
  exact ⟨
    upper_appendix_output_layer_ready,
    upper_appendix_consequences_with_payment_ready_bundle
  ⟩

/-- Upper bridge input bundle: the concrete rational certificate together with
the current validated upper appendix output layer.

This is the Lean-facing handoff point for replacing
`upper_boundary_r2_integrated_loglog_whp_of_certificate` by a proof that uses
the certificate and the output-layer facts. -/
theorem upper_boundary_bridge_inputs_ready :
    Certificate ∧ UpperR2OutputLayer := by
  exact ⟨rational_certificate, upper_appendix_output_layer_ready⟩

/-- Named certificate component of the current upper bridge-input package. -/
theorem upper_boundary_certificate_ready :
    Certificate := by
  exact upper_boundary_bridge_inputs_ready.1

/-- Named output-layer component of the current upper bridge-input package. -/
theorem upper_boundary_output_layer_ready :
    UpperR2OutputLayer := by
  exact upper_boundary_bridge_inputs_ready.2

/-- Named endpoint-table facts extracted from the current complete upper
output layer. -/
theorem upper_output_layer_table_facts_ready :
    roomEndpointTableLower ≤ roomEndpointLower ∧
      tightPrefixTableLower ≤ prefixEndpointLower ∧
      tailEndpointActual ≤ tailRatioUpper ∧
      1 / p2AppendixDenomUpper ≤ p2EndpointLower := by
  exact upper_boundary_output_layer_ready.1

/-- Named room table fact extracted from the current complete upper output
layer. -/
theorem upper_output_layer_room_table_lower_ready :
    roomEndpointTableLower ≤ roomEndpointLower := by
  exact upper_output_layer_table_facts_ready.1

/-- Named prefix table fact extracted from the current complete upper output
layer. -/
theorem upper_output_layer_prefix_table_lower_ready :
    tightPrefixTableLower ≤ prefixEndpointLower := by
  exact upper_output_layer_table_facts_ready.2.1

/-- Named tail upper fact extracted from the current complete upper output
layer. -/
theorem upper_output_layer_tail_upper_ready :
    tailEndpointActual ≤ tailRatioUpper := by
  exact upper_output_layer_table_facts_ready.2.2.1

/-- Named `p_2` reciprocal lower fact extracted from the current complete
upper output layer. -/
theorem upper_output_layer_p2_reciprocal_lower_ready :
    1 / p2AppendixDenomUpper ≤ p2EndpointLower := by
  exact upper_output_layer_table_facts_ready.2.2.2

/-- Scalar endpoint-table readiness package extracted from the current
complete upper output layer. -/
theorem upper_output_layer_table_scalar_ready_bundle :
    roomEndpointTableLower ≤ roomEndpointLower ∧
      tightPrefixTableLower ≤ prefixEndpointLower ∧
      tailEndpointActual ≤ tailRatioUpper ∧
      1 / p2AppendixDenomUpper ≤ p2EndpointLower := by
  exact ⟨
    upper_output_layer_room_table_lower_ready,
    upper_output_layer_prefix_table_lower_ready,
    upper_output_layer_tail_upper_ready,
    upper_output_layer_p2_reciprocal_lower_ready
  ⟩

/-- Named interval-output facts extracted from the current complete upper
output layer. -/
theorem upper_output_layer_interval_outputs_ready :
    IntervalOutputs
      roomEndpointLower
      prefixEndpointLower
      tailEndpointActual
      p2EndpointLower := by
  exact upper_boundary_output_layer_ready.2.1

/-- Named certified consequences extracted from the current complete upper
output layer. -/
theorem upper_output_layer_certified_consequences_ready :
    CertifiedConsequences
      roomEndpointLower
      prefixEndpointLower
      tailEndpointActual
      p2EndpointLower := by
  exact upper_boundary_output_layer_ready.2.2.1

/-- Named room reserve consequence extracted from the current complete upper
output layer. -/
theorem upper_output_layer_room_reserve_ready :
    roomCertifiedLower < roomEndpointLower := by
  exact upper_output_layer_certified_consequences_ready.room_reserve

/-- Named prefix reserve consequence extracted from the current complete upper
output layer. -/
theorem upper_output_layer_prefix_reserve_ready :
    prefixCertifiedLower < prefixEndpointLower := by
  exact upper_output_layer_certified_consequences_ready.prefix_reserve

/-- Named tail payment consequence extracted from the current complete upper
output layer. -/
theorem upper_output_layer_tail_paid_by_final_gap_ready :
    tailEndpointActual < finalGapCoefficient := by
  exact upper_output_layer_certified_consequences_ready.tail_paid_by_final_gap

/-- Named delta admissibility consequence extracted from the current complete
upper output layer. -/
theorem upper_output_layer_delta_admissible_ready :
    delta < p2EndpointLower := by
  exact upper_output_layer_certified_consequences_ready.delta_admissible

/-- Named `p_2` reserve admissibility consequence extracted from the current
complete upper output layer. -/
theorem upper_output_layer_p2_reserve_admissible_ready :
    p2CertifiedLower < p2EndpointLower := by
  exact upper_output_layer_certified_consequences_ready.p2_reserve_admissible

/-- Scalar certified-consequence readiness package extracted from the current
complete upper output layer. -/
theorem upper_output_layer_certified_scalar_ready_bundle :
    roomCertifiedLower < roomEndpointLower ∧
      prefixCertifiedLower < prefixEndpointLower ∧
      tailEndpointActual < finalGapCoefficient ∧
      delta < p2EndpointLower ∧
      p2CertifiedLower < p2EndpointLower := by
  exact ⟨
    upper_output_layer_room_reserve_ready,
    upper_output_layer_prefix_reserve_ready,
    upper_output_layer_tail_paid_by_final_gap_ready,
    upper_output_layer_delta_admissible_ready,
    upper_output_layer_p2_reserve_admissible_ready
  ⟩

/-- Named payment-ready consequences extracted from the current complete upper
output layer. -/
theorem upper_output_layer_consequences_with_payment_ready :
    ((shiftCertifiedUpper + finalGapCoefficient + tailRatioUpper <
      prefixCertifiedLower) ∧
      (prefixCertifiedLower + tailRatioUpper < roomCertifiedLower) ∧
      0 < finalGapCoefficient) ∧
      CertifiedConsequences
        roomEndpointLower
        prefixEndpointLower
        tailEndpointActual
        p2EndpointLower := by
  exact upper_boundary_output_layer_ready.2.2.2

/-- Named first payment inequality extracted from the current complete upper
output layer. -/
theorem upper_output_layer_shift_gap_tail_lt_prefix_ready :
    shiftCertifiedUpper + finalGapCoefficient + tailRatioUpper <
      prefixCertifiedLower := by
  exact upper_output_layer_consequences_with_payment_ready.1.1

/-- Named second payment inequality extracted from the current complete upper
output layer. -/
theorem upper_output_layer_prefix_tail_lt_room_ready :
    prefixCertifiedLower + tailRatioUpper < roomCertifiedLower := by
  exact upper_output_layer_consequences_with_payment_ready.1.2.1

/-- Named final-gap positivity fact extracted from the current complete upper
output layer. -/
theorem upper_output_layer_final_gap_pos_ready :
    0 < finalGapCoefficient := by
  exact upper_output_layer_consequences_with_payment_ready.1.2.2

/-- Combined scalar readiness package extracted from the current complete
upper output layer. -/
theorem upper_output_layer_scalar_ready_bundle :
    (roomEndpointTableLower ≤ roomEndpointLower ∧
      tightPrefixTableLower ≤ prefixEndpointLower ∧
      tailEndpointActual ≤ tailRatioUpper ∧
      1 / p2AppendixDenomUpper ≤ p2EndpointLower) ∧
      (roomCertifiedLower < roomEndpointLower ∧
        prefixCertifiedLower < prefixEndpointLower ∧
        tailEndpointActual < finalGapCoefficient ∧
        delta < p2EndpointLower ∧
        p2CertifiedLower < p2EndpointLower) ∧
      (shiftCertifiedUpper + finalGapCoefficient + tailRatioUpper <
        prefixCertifiedLower) ∧
      (prefixCertifiedLower + tailRatioUpper < roomCertifiedLower) ∧
      0 < finalGapCoefficient := by
  exact ⟨
    upper_output_layer_table_scalar_ready_bundle,
    upper_output_layer_certified_scalar_ready_bundle,
    upper_output_layer_shift_gap_tail_lt_prefix_ready,
    upper_output_layer_prefix_tail_lt_room_ready,
    upper_output_layer_final_gap_pos_ready
  ⟩

/-- Upper bridge input bundle together with the complete output-layer
readiness package for the current appendix output. -/
theorem upper_boundary_bridge_inputs_ready_bundle :
    (Certificate ∧ UpperR2OutputLayer) ∧
      UpperR2OutputLayer ∧
      (((shiftCertifiedUpper + finalGapCoefficient + tailRatioUpper <
        prefixCertifiedLower) ∧
        (prefixCertifiedLower + tailRatioUpper < roomCertifiedLower) ∧
        0 < finalGapCoefficient) ∧
        CertifiedConsequences
          roomEndpointLower
          prefixEndpointLower
          tailEndpointActual
          p2EndpointLower) ∧
      CertifiedConsequences
        roomEndpointLower
        prefixEndpointLower
        tailEndpointActual
        p2EndpointLower ∧
      IntervalOutputs
        roomEndpointLower
        prefixEndpointLower
        tailEndpointActual
        p2EndpointLower ∧
      UpperEndpointComponents
        roomEndpointLower
        prefixEndpointLower
        tailEndpointActual
        p2EndpointLower ∧
      ((roomEndpointTableLower ≤ roomEndpointLower ∧
        0 < roomEndpointLower ∧
        tightPrefixTableLower ≤ prefixEndpointLower ∧
        0 < prefixEndpointLower ∧
        tailEndpointActual ≤ tailRatioUpper ∧
        0 < tailEndpointActual) ∧
        (P2ReciprocalOutput p2EndpointLower ∧
          delta < p2EndpointLower ∧
          p2CertifiedLower < p2EndpointLower ∧
          0 < p2EndpointLower)) := by
  exact ⟨
    upper_boundary_bridge_inputs_ready,
    upper_appendix_output_layer_ready_bundle
  ⟩

/-- Upper bridge input certificate bundled with the scalar readiness facts
extracted from the current complete output layer. -/
theorem upper_boundary_bridge_inputs_scalar_ready_bundle :
    Certificate ∧
      (roomEndpointTableLower ≤ roomEndpointLower ∧
        tightPrefixTableLower ≤ prefixEndpointLower ∧
        tailEndpointActual ≤ tailRatioUpper ∧
        1 / p2AppendixDenomUpper ≤ p2EndpointLower) ∧
      (roomCertifiedLower < roomEndpointLower ∧
        prefixCertifiedLower < prefixEndpointLower ∧
        tailEndpointActual < finalGapCoefficient ∧
        delta < p2EndpointLower ∧
        p2CertifiedLower < p2EndpointLower) ∧
      (shiftCertifiedUpper + finalGapCoefficient + tailRatioUpper <
        prefixCertifiedLower) ∧
      (prefixCertifiedLower + tailRatioUpper < roomCertifiedLower) ∧
      0 < finalGapCoefficient := by
  exact ⟨
    upper_boundary_certificate_ready,
    upper_output_layer_scalar_ready_bundle
  ⟩

/-- Named scalar bridge-input contract for the current upper appendix output.

This is the lightweight, non-structure-shaped package of certificate plus
endpoint, certified-consequence, and payment scalar facts that a future upper
WHP proof can consume directly. -/
def UpperR2ScalarBridgeInputs : Prop :=
  Certificate ∧
    (roomEndpointTableLower ≤ roomEndpointLower ∧
      tightPrefixTableLower ≤ prefixEndpointLower ∧
      tailEndpointActual ≤ tailRatioUpper ∧
      1 / p2AppendixDenomUpper ≤ p2EndpointLower) ∧
    (roomCertifiedLower < roomEndpointLower ∧
      prefixCertifiedLower < prefixEndpointLower ∧
      tailEndpointActual < finalGapCoefficient ∧
      delta < p2EndpointLower ∧
      p2CertifiedLower < p2EndpointLower) ∧
    (shiftCertifiedUpper + finalGapCoefficient + tailRatioUpper <
      prefixCertifiedLower) ∧
    (prefixCertifiedLower + tailRatioUpper < roomCertifiedLower) ∧
    0 < finalGapCoefficient

/-- Current upper appendix instance of the named scalar bridge-input
contract. -/
theorem upper_boundary_scalar_bridge_inputs_ready :
    UpperR2ScalarBridgeInputs := by
  exact upper_boundary_bridge_inputs_scalar_ready_bundle

/-- Certificate projection from the named upper scalar bridge-input package. -/
theorem upper_scalar_bridge_certificate_ready :
    Certificate := by
  exact upper_boundary_scalar_bridge_inputs_ready.1

/-- Endpoint-table scalar projection from the named upper scalar bridge-input
package. -/
theorem upper_scalar_bridge_table_ready_bundle :
    roomEndpointTableLower ≤ roomEndpointLower ∧
      tightPrefixTableLower ≤ prefixEndpointLower ∧
      tailEndpointActual ≤ tailRatioUpper ∧
      1 / p2AppendixDenomUpper ≤ p2EndpointLower := by
  exact upper_boundary_scalar_bridge_inputs_ready.2.1

/-- Certified-consequence scalar projection from the named upper scalar
bridge-input package. -/
theorem upper_scalar_bridge_certified_ready_bundle :
    roomCertifiedLower < roomEndpointLower ∧
      prefixCertifiedLower < prefixEndpointLower ∧
      tailEndpointActual < finalGapCoefficient ∧
      delta < p2EndpointLower ∧
      p2CertifiedLower < p2EndpointLower := by
  exact upper_boundary_scalar_bridge_inputs_ready.2.2.1

/-- Payment scalar projection from the named upper scalar bridge-input package. -/
theorem upper_scalar_bridge_payment_ready_bundle :
    (shiftCertifiedUpper + finalGapCoefficient + tailRatioUpper <
      prefixCertifiedLower) ∧
      (prefixCertifiedLower + tailRatioUpper < roomCertifiedLower) ∧
      0 < finalGapCoefficient := by
  exact upper_boundary_scalar_bridge_inputs_ready.2.2.2

end Problem625.Analytical.UpperR2
