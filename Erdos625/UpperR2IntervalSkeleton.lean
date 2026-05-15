import Erdos625.UpperR2Certificate

/-!
# Upper-boundary `r=2` interval skeleton

This module is the first Lean-side consumer of
`Problem625.Analytical.UpperR2.Certificate`.

It does not formalize the upper-boundary WHP source theorem.  It records
certificate-to-slack consequences that the eventual interval-arithmetic
formalization should use when discharging
`upper_boundary_r2_integrated_loglog_whp_of_bridge_inputs`.
-/

namespace Problem625.Analytical.UpperR2

/-- Lean-facing output contract for the future upper-boundary interval
arithmetic lemma.  The fields are exactly the table/tail/endpoint inequalities
that the current rational certificate adapters can consume. -/
structure IntervalOutputs
    (roomLower prefixLower tailActual p2Lower : ℚ) : Prop where
  room_table_lower : roomEndpointTableLower ≤ roomLower
  prefix_table_lower : tightPrefixTableLower ≤ prefixLower
  tail_upper : tailActual ≤ tailRatioUpper
  p2_reciprocal_lower : 1 / p2AppendixDenomUpper ≤ p2Lower

/-- Certified consequences consumed by the upper-branch payment/admissibility
assembly after an interval-output package has been proved. -/
structure CertifiedConsequences
    (roomLower prefixLower tailActual p2Lower : ℚ) : Prop where
  room_reserve : roomCertifiedLower < roomLower
  prefix_reserve : prefixCertifiedLower < prefixLower
  tail_paid_by_final_gap : tailActual < finalGapCoefficient
  delta_admissible : delta < p2Lower
  p2_reserve_admissible : p2CertifiedLower < p2Lower

/-- Lean-facing component contract for the future `p_2` reciprocal endpoint
interval lemma. -/
structure P2ReciprocalOutput
    (p2Lower : ℚ) : Prop where
  reciprocal_lower : 1 / p2AppendixDenomUpper ≤ p2Lower

/-- Lean-facing component contract for the future upper room endpoint proof. -/
structure RoomEndpointOutput
    (roomLower : ℚ) : Prop where
  table_lower : roomEndpointTableLower ≤ roomLower

/-- Lean-facing component contract for the future tight-prefix endpoint proof. -/
structure PrefixEndpointOutput
    (prefixLower : ℚ) : Prop where
  table_lower : tightPrefixTableLower ≤ prefixLower

/-- Lean-facing component contract for the future upper tail endpoint proof. -/
structure TailEndpointOutput
    (tailActual : ℚ) : Prop where
  tail_upper : tailActual ≤ tailRatioUpper

/-- Bundled component contract for the future upper endpoint proof. -/
structure UpperEndpointComponents
    (roomLower prefixLower tailActual p2Lower : ℚ) : Prop where
  room : RoomEndpointOutput roomLower
  pref : PrefixEndpointOutput prefixLower
  tail_component : TailEndpointOutput tailActual
  p2 : P2ReciprocalOutput p2Lower

/-- Assemble the full upper `IntervalOutputs` contract from the four component
endpoint contracts. -/
theorem interval_outputs_of_components
    {roomLower prefixLower tailActual p2Lower : ℚ}
    (hroom : RoomEndpointOutput roomLower)
    (hprefix : PrefixEndpointOutput prefixLower)
    (htail : TailEndpointOutput tailActual)
    (hp2 : P2ReciprocalOutput p2Lower) :
    IntervalOutputs roomLower prefixLower tailActual p2Lower where
  room_table_lower := hroom.table_lower
  prefix_table_lower := hprefix.table_lower
  tail_upper := htail.tail_upper
  p2_reciprocal_lower := hp2.reciprocal_lower

/-- Assemble the full upper `IntervalOutputs` contract from the bundled
component endpoint contract. -/
theorem interval_outputs_of_component_bundle
    {roomLower prefixLower tailActual p2Lower : ℚ}
    (hcomponents :
      UpperEndpointComponents roomLower prefixLower tailActual p2Lower) :
    IntervalOutputs roomLower prefixLower tailActual p2Lower := by
  exact interval_outputs_of_components
    hcomponents.room
    hcomponents.pref
    hcomponents.tail_component
    hcomponents.p2

/-- The appendix constants themselves satisfy the upper interval-output
contract.  This is the canonical contract instance that a later interval
arithmetic proof should replace by actual function endpoint bounds. -/
theorem appendix_constant_interval_outputs :
    IntervalOutputs
      roomEndpointTableLower
      tightPrefixTableLower
      tailRatioUpper
      (1 / p2AppendixDenomUpper) := by
  constructor <;> rfl

/-- Any upper-boundary certificate supplies enough prefix room after paying the
shift, final gap, and interval-tail costs. -/
theorem certified_prefix_room_after_tail_gap_and_shift
    (hcert : Certificate) :
    0 <
      prefixCertifiedLower -
        shiftCertifiedUpper -
        finalGapCoefficient -
        tailRatioUpper := by
  exact hcert.prefix_after_tail_gap_shift_pos

/-- Any upper-boundary certificate supplies enough global room after paying the
prefix and interval-tail costs. -/
theorem certified_room_after_prefix_and_tail
    (hcert : Certificate) :
    0 < roomCertifiedLower - prefixCertifiedLower - tailRatioUpper := by
  exact hcert.room_after_prefix_tail_pos

/-- Any upper-boundary certificate makes the interval tail smaller than the
final log-gap coefficient. -/
theorem certified_tail_ratio_below_final_gap
    (hcert : Certificate) :
    tailRatioUpper < finalGapCoefficient := by
  exact hcert.tail_lt_final_gap

/-- Any upper-boundary certificate makes the final log-gap coefficient
positive. -/
theorem certified_final_gap_coefficient_pos
    (hcert : Certificate) :
    0 < finalGapCoefficient := by
  exact hcert.final_gap_pos

/-- Any upper-boundary certificate pays the shift, final gap, and interval-tail
costs inside the certified prefix reserve. -/
theorem certified_shift_gap_tail_lt_prefix
    (hcert : Certificate) :
    shiftCertifiedUpper + finalGapCoefficient + tailRatioUpper <
      prefixCertifiedLower := by
  linarith [hcert.prefix_after_tail_gap_shift_pos]

/-- Any upper-boundary certificate pays the prefix and interval-tail costs
inside the certified global room reserve. -/
theorem certified_prefix_tail_lt_room
    (hcert : Certificate) :
    prefixCertifiedLower + tailRatioUpper < roomCertifiedLower := by
  linarith [hcert.room_after_prefix_tail_pos]

/-- Any upper-boundary certificate records that the explicit room endpoint
table lower bound is stronger than the certified room reserve. -/
theorem certified_room_table_supports_reserve
    (hcert : Certificate) :
    roomCertifiedLower < roomEndpointTableLower := by
  exact hcert.room_table_supports_certified

/-- Any upper-boundary certificate records that the explicit tight-prefix table
lower bound is stronger than the certified prefix reserve. -/
theorem certified_tight_prefix_table_supports_reserve
    (hcert : Certificate) :
    prefixCertifiedLower < tightPrefixTableLower := by
  exact hcert.tight_prefix_table_supports_certified

/-- Any upper-boundary certificate records that the explicit `p_2` appendix
lower bound is stronger than the certified admissibility reserve. -/
theorem certified_p2_table_supports_reserve
    (hcert : Certificate) :
    p2CertifiedLower < p2AppendixTableLower := by
  exact hcert.p2_table_supports_certified

/-- Any upper-boundary certificate records that the explicit `p_2` appendix
lower bound is admissible for the endpoint `delta`. -/
theorem certified_delta_lt_p2_table_lower
    (hcert : Certificate) :
    delta < p2AppendixTableLower := by
  exact hcert.delta_lt_p2_table_lower

/-- Any upper-boundary certificate records positivity of the certified `p_2`
admissibility reserve. -/
theorem certified_p2_lower_pos
    (hcert : Certificate) :
    0 < p2CertifiedLower := by
  exact hcert.p2_certified_lower_pos

/-- Any upper-boundary certificate records positivity of the explicit `p_2`
appendix table lower bound. -/
theorem certified_p2_table_lower_pos
    (hcert : Certificate) :
    0 < p2AppendixTableLower := by
  exact hcert.p2_table_lower_pos

/-- Any upper-boundary certificate records positivity of the denominator
enclosure used in the reciprocal `p_2` appendix chain. -/
theorem certified_p2_denom_upper_pos
    (hcert : Certificate) :
    0 < p2AppendixDenomUpper := by
  exact hcert.p2_denom_upper_pos

/-- Any upper-boundary certificate records positivity of the reciprocal
denominator lower bound used in the `p_2` appendix chain. -/
theorem certified_p2_recip_denom_upper_pos
    (hcert : Certificate) :
    0 < 1 / p2AppendixDenomUpper := by
  exact hcert.p2_recip_denom_upper_pos

/-- Any upper-boundary certificate records that the explicit denominator
enclosure `2.69` implies the decimal lower bound `0.37` by reciprocal
comparison. -/
theorem certified_p2_table_lower_lt_recip_denom_upper
    (hcert : Certificate) :
    p2AppendixTableLower < 1 / p2AppendixDenomUpper := by
  exact hcert.p2_table_lower_lt_recip_denom_upper

/-- The concrete rational upper-boundary certificate supplies all currently
formalized interval-skeleton slack consequences. -/
theorem rational_certificate_interval_slack :
    (0 <
      prefixCertifiedLower -
        shiftCertifiedUpper -
        finalGapCoefficient -
        tailRatioUpper) ∧
      (0 < roomCertifiedLower - prefixCertifiedLower - tailRatioUpper) ∧
      tailRatioUpper < finalGapCoefficient := by
  exact ⟨
    certified_prefix_room_after_tail_gap_and_shift rational_certificate,
    certified_room_after_prefix_and_tail rational_certificate,
    certified_tail_ratio_below_final_gap rational_certificate
  ⟩

/-- A named bundle of the upper-branch numerical payments already certified by
the concrete rational certificate.  This is the convenient handoff shape for
the next interval/arithmetic lemma: the prefix reserve pays the shift, final
gap, and tail costs, while the global room reserve still dominates the prefix
and tail costs. -/
theorem rational_certificate_paid_budget_bundle :
    (0 <
      prefixCertifiedLower -
        shiftCertifiedUpper -
        finalGapCoefficient -
        tailRatioUpper) ∧
      (tailRatioUpper < finalGapCoefficient) ∧
      (0 < finalGapCoefficient) ∧
      (0 < roomCertifiedLower - prefixCertifiedLower - tailRatioUpper) := by
  exact ⟨
    rational_certificate_interval_slack.1,
    rational_certificate_interval_slack.2.2,
    certified_final_gap_coefficient_pos rational_certificate,
    rational_certificate_interval_slack.2.1
  ⟩

/-- The concrete rational upper-boundary certificate pays the shift, final
gap, and tail costs inside the prefix reserve. -/
theorem rational_certificate_shift_gap_tail_lt_prefix :
    shiftCertifiedUpper + finalGapCoefficient + tailRatioUpper <
      prefixCertifiedLower := by
  exact certified_shift_gap_tail_lt_prefix rational_certificate

/-- The concrete rational upper-boundary certificate pays the prefix and tail
costs inside the global room reserve. -/
theorem rational_certificate_prefix_tail_lt_room :
    prefixCertifiedLower + tailRatioUpper < roomCertifiedLower := by
  exact certified_prefix_tail_lt_room rational_certificate

/-- The concrete upper certificate is ready for the next interval lemma in the
standard payment form: prefix pays shift/final-gap/tail, global room pays
prefix/tail, and the final log-gap coefficient is positive. -/
theorem rational_certificate_upper_payment_ready :
    (shiftCertifiedUpper + finalGapCoefficient + tailRatioUpper <
      prefixCertifiedLower) ∧
      (prefixCertifiedLower + tailRatioUpper < roomCertifiedLower) ∧
      (0 < finalGapCoefficient) := by
  exact ⟨
    rational_certificate_shift_gap_tail_lt_prefix,
    rational_certificate_prefix_tail_lt_room,
    certified_final_gap_coefficient_pos rational_certificate
  ⟩

/-- The concrete rational upper-boundary certificate connects the two explicit
appendix lower endpoint tables to the certified reserves consumed by the upper
payment lemmas. -/
theorem rational_certificate_table_support_ready :
    roomCertifiedLower < roomEndpointTableLower ∧
      prefixCertifiedLower < tightPrefixTableLower := by
  exact ⟨
    certified_room_table_supports_reserve rational_certificate,
    certified_tight_prefix_table_supports_reserve rational_certificate
  ⟩

/-- The concrete rational upper-boundary certificate connects the explicit
appendix `p_2` lower table bound to the certified reserve and to the endpoint
admissibility inequality consumed by the upper bridge. -/
theorem rational_certificate_p2_table_support_ready :
    delta < p2CertifiedLower ∧
      p2CertifiedLower < p2AppendixTableLower ∧
      delta < p2AppendixTableLower := by
  exact ⟨
    delta_lt_p2_lower,
    certified_p2_table_supports_reserve rational_certificate,
    certified_delta_lt_p2_table_lower rational_certificate
  ⟩

/-- The concrete rational upper-boundary certificate gives the Lean-facing
arithmetic chain behind the appendix sentence `p_2 > 1/2.69 > 0.37`: the
certified reserve is below the table lower bound, and the table lower bound is
below the reciprocal of the denominator enclosure. -/
theorem rational_certificate_p2_reciprocal_chain_ready :
    delta < p2CertifiedLower ∧
      p2CertifiedLower < p2AppendixTableLower ∧
      p2AppendixTableLower < 1 / p2AppendixDenomUpper := by
  exact ⟨
    rational_certificate_p2_table_support_ready.1,
    rational_certificate_p2_table_support_ready.2.1,
    certified_p2_table_lower_lt_recip_denom_upper rational_certificate
  ⟩

/-- The concrete rational upper-boundary certificate packages the full strict
`p_2` appendix admissibility chain in the natural left-to-right order:
`delta < 0.35 < 0.37 < 1 / 2.69`. -/
theorem rational_certificate_p2_full_admissibility_chain :
    delta < p2CertifiedLower ∧
      p2CertifiedLower < p2AppendixTableLower ∧
      p2AppendixTableLower < 1 / p2AppendixDenomUpper ∧
      0 < 1 / p2AppendixDenomUpper := by
  exact ⟨
    rational_certificate_p2_reciprocal_chain_ready.1,
    rational_certificate_p2_reciprocal_chain_ready.2.1,
    rational_certificate_p2_reciprocal_chain_ready.2.2,
    certified_p2_recip_denom_upper_pos rational_certificate
  ⟩

/-- The concrete rational upper-boundary certificate gives the reciprocal
admissibility consequences in the direct form expected by a later `p_2`
interval lemma: both the endpoint `delta` and the certified reserve are below
the reciprocal denominator enclosure `1 / 2.69`. -/
theorem rational_certificate_p2_reciprocal_admissibility_ready :
    delta < 1 / p2AppendixDenomUpper ∧
      p2CertifiedLower < 1 / p2AppendixDenomUpper ∧
      0 < 1 / p2AppendixDenomUpper ∧
      0 < p2CertifiedLower ∧
      0 < p2AppendixTableLower := by
  exact ⟨
    lt_trans
      rational_certificate_p2_reciprocal_chain_ready.1
      (lt_trans
        rational_certificate_p2_reciprocal_chain_ready.2.1
        rational_certificate_p2_reciprocal_chain_ready.2.2),
    lt_trans
      rational_certificate_p2_reciprocal_chain_ready.2.1
      rational_certificate_p2_reciprocal_chain_ready.2.2,
    certified_p2_recip_denom_upper_pos rational_certificate,
    certified_p2_lower_pos rational_certificate,
    certified_p2_table_lower_pos rational_certificate
  ⟩

/-- The concrete rational upper-boundary certificate packages the currently
formalized numerical inputs for the first real upper interval lemma: paid
prefix/global budget, explicit table support for room and prefix reserves, and
direct `p_2` reciprocal admissibility. -/
theorem rational_certificate_upper_interval_inputs_ready :
    ((shiftCertifiedUpper + finalGapCoefficient + tailRatioUpper <
      prefixCertifiedLower) ∧
      (prefixCertifiedLower + tailRatioUpper < roomCertifiedLower) ∧
      (0 < finalGapCoefficient)) ∧
      (roomCertifiedLower < roomEndpointTableLower ∧
        prefixCertifiedLower < tightPrefixTableLower) ∧
      (delta < 1 / p2AppendixDenomUpper ∧
        p2CertifiedLower < 1 / p2AppendixDenomUpper ∧
        0 < 1 / p2AppendixDenomUpper ∧
        0 < p2CertifiedLower ∧
        0 < p2AppendixTableLower) := by
  exact ⟨
    rational_certificate_upper_payment_ready,
    rational_certificate_table_support_ready,
    rational_certificate_p2_reciprocal_admissibility_ready
  ⟩

/-- Adapter for the future interval proof of the `p_2` lower endpoint.  Once
an interval lemma proves that the actual endpoint is at least the reciprocal
appendix lower bound `1 / 2.69`, the current rational certificate immediately
upgrades it to both endpoint admissibility and the certified reserve bound. -/
theorem p2_admissibility_of_reciprocal_lower_bound
    {p2Lower : ℚ}
    (hp2 : 1 / p2AppendixDenomUpper ≤ p2Lower) :
    delta < p2Lower ∧ p2CertifiedLower < p2Lower := by
  exact ⟨
    lt_of_lt_of_le
      rational_certificate_p2_reciprocal_admissibility_ready.1
      hp2,
    lt_of_lt_of_le
      rational_certificate_p2_reciprocal_admissibility_ready.2.1
      hp2
  ⟩

/-- Any future `p_2` reciprocal component output immediately gives the
certified endpoint and reserve admissibility inequalities. -/
theorem p2_admissibility_of_reciprocal_output
    {p2Lower : ℚ}
    (hp2 : P2ReciprocalOutput p2Lower) :
    delta < p2Lower ∧ p2CertifiedLower < p2Lower := by
  exact p2_admissibility_of_reciprocal_lower_bound
    hp2.reciprocal_lower

/-- The appendix reciprocal endpoint constant itself satisfies the future
`p_2` reciprocal component contract. -/
theorem appendix_constant_p2_reciprocal_output :
    P2ReciprocalOutput (1 / p2AppendixDenomUpper) := by
  exact { reciprocal_lower := le_rfl }

/-- Dry run of the `p_2` reciprocal component consumer on the appendix
reciprocal endpoint constant. -/
theorem appendix_constant_p2_reciprocal_output_ready :
    delta < 1 / p2AppendixDenomUpper ∧
      p2CertifiedLower < 1 / p2AppendixDenomUpper := by
  exact p2_admissibility_of_reciprocal_output
    appendix_constant_p2_reciprocal_output

/-- Adapter for the future interval proof of the upper room endpoint.  Once an
interval lemma proves that the actual room lower endpoint is at least the
appendix table lower bound `0.075`, the current rational certificate upgrades
it to the certified reserve `0.07`. -/
theorem room_reserve_of_table_lower_bound
    {roomLower : ℚ}
    (hroom : roomEndpointTableLower ≤ roomLower) :
    roomCertifiedLower < roomLower := by
  exact lt_of_lt_of_le
    rational_certificate_table_support_ready.1
    hroom

/-- Adapter for the future interval proof of the tight prefix endpoint.  Once
an interval lemma proves that the actual tight-prefix lower endpoint is at
least the appendix table lower bound `0.00670`, the current rational
certificate upgrades it to the certified reserve `0.006`. -/
theorem prefix_reserve_of_table_lower_bound
    {prefixLower : ℚ}
    (hprefix : tightPrefixTableLower ≤ prefixLower) :
    prefixCertifiedLower < prefixLower := by
  exact lt_of_lt_of_le
    rational_certificate_table_support_ready.2
    hprefix

/-- Combined adapter for future upper room and tight-prefix interval outputs:
table-level lower bounds immediately imply the certified room and prefix
reserves consumed by the upper payment layer. -/
theorem upper_reserves_of_table_lower_bounds
    {roomLower prefixLower : ℚ}
    (hroom : roomEndpointTableLower ≤ roomLower)
    (hprefix : tightPrefixTableLower ≤ prefixLower) :
    roomCertifiedLower < roomLower ∧
      prefixCertifiedLower < prefixLower := by
  exact ⟨
    room_reserve_of_table_lower_bound hroom,
    prefix_reserve_of_table_lower_bound hprefix
  ⟩

/-- Adapter for the future interval proof of the upper tail ratio.  Once a tail
lemma proves that the actual tail ratio is at most the appendix bound `5e-12`,
the current rational certificate upgrades it to the final-gap budget
inequality needed by the upper payment layer. -/
theorem tail_below_final_gap_of_tail_bound
    {tailActual : ℚ}
    (htail : tailActual ≤ tailRatioUpper) :
    tailActual < finalGapCoefficient := by
  exact lt_of_le_of_lt
    htail
    rational_certificate_interval_slack.2.2

/-- Combined adapter for future upper interval table and tail outputs: room and
prefix table lower bounds produce the certified reserves, while the tail upper
bound is paid by the final log-gap coefficient. -/
theorem upper_table_tail_outputs_ready
    {roomLower prefixLower tailActual : ℚ}
    (hroom : roomEndpointTableLower ≤ roomLower)
    (hprefix : tightPrefixTableLower ≤ prefixLower)
    (htail : tailActual ≤ tailRatioUpper) :
    roomCertifiedLower < roomLower ∧
      prefixCertifiedLower < prefixLower ∧
      tailActual < finalGapCoefficient := by
  exact ⟨
    room_reserve_of_table_lower_bound hroom,
    prefix_reserve_of_table_lower_bound hprefix,
    tail_below_final_gap_of_tail_bound htail
  ⟩

/-- Combined adapter for the future upper interval-output package: room and
prefix lower tables give certified reserves, the tail upper table is paid by
the final log-gap coefficient, and the `p_2` reciprocal lower endpoint gives
both endpoint and certified-reserve admissibility. -/
theorem upper_interval_outputs_ready
    {roomLower prefixLower tailActual p2Lower : ℚ}
    (hroom : roomEndpointTableLower ≤ roomLower)
    (hprefix : tightPrefixTableLower ≤ prefixLower)
    (htail : tailActual ≤ tailRatioUpper)
    (hp2 : 1 / p2AppendixDenomUpper ≤ p2Lower) :
    roomCertifiedLower < roomLower ∧
      prefixCertifiedLower < prefixLower ∧
      tailActual < finalGapCoefficient ∧
      delta < p2Lower ∧
      p2CertifiedLower < p2Lower := by
  exact ⟨
    room_reserve_of_table_lower_bound hroom,
    prefix_reserve_of_table_lower_bound hprefix,
    tail_below_final_gap_of_tail_bound htail,
    (p2_admissibility_of_reciprocal_lower_bound hp2).1,
    (p2_admissibility_of_reciprocal_lower_bound hp2).2
  ⟩

/-- Consumer theorem for the future upper interval-output contract.  Any
`IntervalOutputs` package immediately yields the certified room/prefix
reserves, the tail payment by the final gap, and the `p_2` admissibility facts
needed by the upper branch. -/
theorem upper_interval_outputs_contract_ready
    {roomLower prefixLower tailActual p2Lower : ℚ}
    (houtputs :
      IntervalOutputs roomLower prefixLower tailActual p2Lower) :
    roomCertifiedLower < roomLower ∧
      prefixCertifiedLower < prefixLower ∧
      tailActual < finalGapCoefficient ∧
      delta < p2Lower ∧
      p2CertifiedLower < p2Lower := by
  exact upper_interval_outputs_ready
    houtputs.room_table_lower
    houtputs.prefix_table_lower
    houtputs.tail_upper
    houtputs.p2_reciprocal_lower

/-- Structured version of `upper_interval_outputs_contract_ready`: a future
`IntervalOutputs` proof yields the named certified consequences expected by
the upper-branch assembly. -/
theorem certified_consequences_of_interval_outputs
    {roomLower prefixLower tailActual p2Lower : ℚ}
    (houtputs :
      IntervalOutputs roomLower prefixLower tailActual p2Lower) :
    CertifiedConsequences roomLower prefixLower tailActual p2Lower := by
  let hready := upper_interval_outputs_contract_ready houtputs
  exact {
    room_reserve := hready.1
    prefix_reserve := hready.2.1
    tail_paid_by_final_gap := hready.2.2.1
    delta_admissible := hready.2.2.2.1
    p2_reserve_admissible := hready.2.2.2.2
  }

/-- Component-level consumer theorem for future upper endpoint proofs.  Once
the four endpoint components are proved, the certified consequences expected by
the upper assembly follow without manually rebuilding the package contract. -/
theorem certified_consequences_of_components
    {roomLower prefixLower tailActual p2Lower : ℚ}
    (hroom : RoomEndpointOutput roomLower)
    (hprefix : PrefixEndpointOutput prefixLower)
    (htail : TailEndpointOutput tailActual)
    (hp2 : P2ReciprocalOutput p2Lower) :
    CertifiedConsequences roomLower prefixLower tailActual p2Lower := by
  exact certified_consequences_of_interval_outputs
    (interval_outputs_of_components hroom hprefix htail hp2)

/-- The appendix constants, viewed through the interval-output contract,
already imply the certified room/prefix reserves, tail budget, and `p_2`
admissibility facts.  This is a Lean-facing dry run of the future interval
output consumer path. -/
theorem appendix_constant_interval_outputs_ready :
    roomCertifiedLower < roomEndpointTableLower ∧
      prefixCertifiedLower < tightPrefixTableLower ∧
      tailRatioUpper < finalGapCoefficient ∧
      delta < 1 / p2AppendixDenomUpper ∧
      p2CertifiedLower < 1 / p2AppendixDenomUpper := by
  exact upper_interval_outputs_contract_ready
    appendix_constant_interval_outputs

/-- Structured dry run of the certified-consequence output contract on the
appendix constants themselves. -/
theorem appendix_constant_certified_consequences :
    CertifiedConsequences
      roomEndpointTableLower
      tightPrefixTableLower
      tailRatioUpper
      (1 / p2AppendixDenomUpper) := by
  exact certified_consequences_of_interval_outputs
    appendix_constant_interval_outputs

/-- Structured dry run of the full upper interval-output handoff on the
appendix constants: static payment inequalities plus certified consequences
for the canonical appendix table/tail/`p_2` constants. -/
theorem appendix_constant_consequences_with_payment :
    ((shiftCertifiedUpper + finalGapCoefficient + tailRatioUpper <
      prefixCertifiedLower) ∧
      (prefixCertifiedLower + tailRatioUpper < roomCertifiedLower) ∧
      (0 < finalGapCoefficient)) ∧
      CertifiedConsequences
        roomEndpointTableLower
        tightPrefixTableLower
        tailRatioUpper
        (1 / p2AppendixDenomUpper) := by
  exact ⟨
    rational_certificate_upper_payment_ready,
    appendix_constant_certified_consequences
  ⟩

/-- Consumer theorem for the future upper interval-output contract, bundled
with the already certified payment inequalities.  This is the handoff shape for
the next upper-branch assembly step after an interval lemma has produced
`IntervalOutputs`. -/
theorem upper_interval_outputs_with_payment_ready
    {roomLower prefixLower tailActual p2Lower : ℚ}
    (houtputs :
      IntervalOutputs roomLower prefixLower tailActual p2Lower) :
    ((shiftCertifiedUpper + finalGapCoefficient + tailRatioUpper <
      prefixCertifiedLower) ∧
      (prefixCertifiedLower + tailRatioUpper < roomCertifiedLower) ∧
      (0 < finalGapCoefficient)) ∧
      (roomCertifiedLower < roomLower ∧
        prefixCertifiedLower < prefixLower ∧
        tailActual < finalGapCoefficient ∧
        delta < p2Lower ∧
        p2CertifiedLower < p2Lower) := by
  exact ⟨
    rational_certificate_upper_payment_ready,
    upper_interval_outputs_contract_ready houtputs
  ⟩

/-- Structured payment handoff for any future upper interval-output package:
the interval outputs yield named certified consequences, while the rational
certificate supplies the static payment inequalities. -/
theorem certified_consequences_with_payment_of_interval_outputs
    {roomLower prefixLower tailActual p2Lower : ℚ}
    (houtputs :
      IntervalOutputs roomLower prefixLower tailActual p2Lower) :
    ((shiftCertifiedUpper + finalGapCoefficient + tailRatioUpper <
      prefixCertifiedLower) ∧
      (prefixCertifiedLower + tailRatioUpper < roomCertifiedLower) ∧
      (0 < finalGapCoefficient)) ∧
      CertifiedConsequences roomLower prefixLower tailActual p2Lower := by
  exact ⟨
    rational_certificate_upper_payment_ready,
    certified_consequences_of_interval_outputs houtputs
  ⟩

/-- Component-level payment consumer for future upper endpoint proofs.  Once
the four endpoint components are available, this produces the exact payment
and certified-consequence bundle consumed by the upper assembly. -/
theorem certified_consequences_with_payment_of_components
    {roomLower prefixLower tailActual p2Lower : ℚ}
    (hroom : RoomEndpointOutput roomLower)
    (hprefix : PrefixEndpointOutput prefixLower)
    (htail : TailEndpointOutput tailActual)
    (hp2 : P2ReciprocalOutput p2Lower) :
    ((shiftCertifiedUpper + finalGapCoefficient + tailRatioUpper <
      prefixCertifiedLower) ∧
      (prefixCertifiedLower + tailRatioUpper < roomCertifiedLower) ∧
      (0 < finalGapCoefficient)) ∧
      CertifiedConsequences roomLower prefixLower tailActual p2Lower := by
  exact ⟨
    rational_certificate_upper_payment_ready,
    certified_consequences_of_components hroom hprefix htail hp2
  ⟩

/-- Bundled-component payment consumer for future upper endpoint proofs. -/
theorem certified_consequences_with_payment_of_component_bundle
    {roomLower prefixLower tailActual p2Lower : ℚ}
    (hcomponents :
      UpperEndpointComponents roomLower prefixLower tailActual p2Lower) :
    ((shiftCertifiedUpper + finalGapCoefficient + tailRatioUpper <
      prefixCertifiedLower) ∧
      (prefixCertifiedLower + tailRatioUpper < roomCertifiedLower) ∧
      (0 < finalGapCoefficient)) ∧
      CertifiedConsequences roomLower prefixLower tailActual p2Lower := by
  exact certified_consequences_with_payment_of_components
    hcomponents.room
    hcomponents.pref
    hcomponents.tail_component
    hcomponents.p2

/-- Source-side upper `r=2` bridge input package.

This is the structured handoff below the wrapper-level `UpperR2BridgeInputs`.
It keeps the rational certificate, endpoint-component package, interval-output
contract, and payment/certified-consequence bundle together for the eventual
upper-boundary WHP proof. -/
structure SourceBridgeInputs
    (roomLower prefixLower tailActual p2Lower : ℚ) : Prop where
  certificate : Certificate
  endpoint_components :
    UpperEndpointComponents roomLower prefixLower tailActual p2Lower
  interval_outputs :
    IntervalOutputs roomLower prefixLower tailActual p2Lower
  consequences_with_payment :
    ((shiftCertifiedUpper + finalGapCoefficient + tailRatioUpper <
      prefixCertifiedLower) ∧
      (prefixCertifiedLower + tailRatioUpper < roomCertifiedLower) ∧
      (0 < finalGapCoefficient)) ∧
      CertifiedConsequences roomLower prefixLower tailActual p2Lower

/-- Any upper certificate and endpoint-component package supplies the
structured source-side bridge input package used by the future upper-boundary
WHP proof. -/
theorem source_bridge_inputs_of_endpoint_components
    {roomLower prefixLower tailActual p2Lower : ℚ}
    (hcert : Certificate)
    (hcomponents :
      UpperEndpointComponents roomLower prefixLower tailActual p2Lower) :
    SourceBridgeInputs roomLower prefixLower tailActual p2Lower := by
  exact {
    certificate := hcert
    endpoint_components := hcomponents
    interval_outputs := interval_outputs_of_component_bundle hcomponents
    consequences_with_payment :=
      certified_consequences_with_payment_of_component_bundle hcomponents
  }

end Problem625.Analytical.UpperR2
