import Erdos625.Defs


/-!
# Upper-boundary `r=2` certificate interface

This module records the Lean-facing numerical interface for the upper-boundary
`r=2` interval appendix.

It is not yet the full interval-arithmetic formalization of the appendix.
Instead, it fixes the constants and the certificate-shaped inequalities that
the future interval proof must supply before the upper-branch WHP obligation
can be discharged.
-/

namespace Problem625.Analytical.UpperR2

/-- The upper-boundary prefix endpoint `delta=0.01`. -/
def delta : ℚ :=
  1 / 100

/-- The finite prefix cutoff `I=40` used by the interval appendix. -/
def prefixCutoff : ℕ :=
  40

/-- Certified lower bound for the upper-boundary `r=2` room margin. -/
def roomCertifiedLower : ℚ :=
  7 / 100

/-- Explicit appendix lower endpoint for `Room_2(1)`, recorded from the
interval table as `0.075`. -/
def roomEndpointTableLower : ℚ :=
  75 / 1000

/-- Certified lower bound for the upper-boundary `r=2` prefix margin. -/
def prefixCertifiedLower : ℚ :=
  6 / 1000

/-- Explicit appendix lower endpoint for the tight prefix guard, recorded from
the interval table as `0.00670`. -/
def tightPrefixTableLower : ℚ :=
  670 / 100000

/-- Shift margin used in the integrated upper-boundary proof. -/
def shiftCertifiedUpper : ℚ :=
  3 / 1000

/-- Final log-gap coefficient promised by the upper-boundary route. -/
def finalGapCoefficient : ℚ :=
  1 / 1000

/-- The appendix tail ratio is bounded by `5e-12`. -/
def tailRatioUpper : ℚ :=
  5 / 1000000000000

/-- Conservative lower bound on the `p_2` endpoint. -/
def p2CertifiedLower : ℚ :=
  35 / 100

/-- Explicit appendix lower endpoint for the `p_2` admissibility table,
recorded as the conservative decimal lower bound `0.37`. -/
def p2AppendixTableLower : ℚ :=
  37 / 100

/-- Explicit appendix upper endpoint for the reciprocal denominator in the
`p_2` admissibility estimate, recorded from the interval enclosure as `2.69`.
-/
def p2AppendixDenomUpper : ℚ :=
  269 / 100

/-- Certificate-shaped assumptions extracted from the upper-boundary `r=2`
interval appendix.

Future work should replace uses of this structure by concrete interval
arithmetic proofs of each field, using exact rational enclosures rather than
the current Python reproducibility checker.
-/
structure Certificate : Prop where
  room_pos : 0 < roomCertifiedLower
  prefix_pos : 0 < prefixCertifiedLower
  shift_lt_prefix : shiftCertifiedUpper < prefixCertifiedLower
  final_gap_pos : 0 < finalGapCoefficient
  final_gap_lt_shift : finalGapCoefficient < shiftCertifiedUpper
  tail_ratio_small : tailRatioUpper < 1
  delta_admissible : delta < p2CertifiedLower
  tail_lt_final_gap : tailRatioUpper < finalGapCoefficient
  prefix_after_tail_gap_shift_pos :
    0 <
      prefixCertifiedLower -
        shiftCertifiedUpper -
        finalGapCoefficient -
        tailRatioUpper
  room_after_prefix_tail_pos :
    0 < roomCertifiedLower - prefixCertifiedLower - tailRatioUpper
  room_table_supports_certified :
    roomCertifiedLower < roomEndpointTableLower
  tight_prefix_table_supports_certified :
    prefixCertifiedLower < tightPrefixTableLower
  p2_table_supports_certified :
    p2CertifiedLower < p2AppendixTableLower
  delta_lt_p2_table_lower :
    delta < p2AppendixTableLower
  p2_certified_lower_pos :
    0 < p2CertifiedLower
  p2_table_lower_pos :
    0 < p2AppendixTableLower
  p2_denom_upper_pos :
    0 < p2AppendixDenomUpper
  p2_recip_denom_upper_pos :
    0 < 1 / p2AppendixDenomUpper
  p2_table_lower_lt_recip_denom_upper :
    p2AppendixTableLower < 1 / p2AppendixDenomUpper

/-- The numerical constants appearing in the appendix satisfy the certificate
ordering constraints. -/
theorem rational_certificate : Certificate := by
  constructor <;> norm_num [
    roomCertifiedLower,
    prefixCertifiedLower,
    shiftCertifiedUpper,
    finalGapCoefficient,
    tailRatioUpper,
    delta,
    p2CertifiedLower,
    p2AppendixTableLower,
    p2AppendixDenomUpper,
    roomEndpointTableLower,
    tightPrefixTableLower
  ]

/-- The interval certificate leaves positive room after paying the shift cost. -/
theorem shift_room_remaining_pos :
    0 < prefixCertifiedLower - shiftCertifiedUpper := by
  norm_num [prefixCertifiedLower, shiftCertifiedUpper]

/-- The final requested upper-branch coefficient is below the paid shift
margin, so a `0.003` prefix reserve can support a `0.001` final gap. -/
theorem final_gap_supported_by_shift :
    finalGapCoefficient < shiftCertifiedUpper := by
  exact rational_certificate.final_gap_lt_shift

/-- The appendix admissibility lower bound is stronger than the tight endpoint
`delta=0.01`. -/
theorem delta_lt_p2_lower :
    delta < p2CertifiedLower := by
  exact rational_certificate.delta_admissible

/-- The explicit appendix `p_2` lower table bound `0.37` is stronger than the
certified admissibility reserve `0.35` consumed by the upper bridge. -/
theorem p2_table_supports_certified_lower :
    p2CertifiedLower < p2AppendixTableLower := by
  exact rational_certificate.p2_table_supports_certified

/-- The explicit appendix `p_2` lower table bound is itself stronger than the
endpoint `delta=0.01`. -/
theorem delta_lt_p2_appendix_table_lower :
    delta < p2AppendixTableLower := by
  exact rational_certificate.delta_lt_p2_table_lower

/-- The certified `p_2` admissibility reserve `0.35` is positive. -/
theorem p2_certified_lower_pos :
    0 < p2CertifiedLower := by
  exact rational_certificate.p2_certified_lower_pos

/-- The explicit appendix `p_2` table lower bound `0.37` is positive. -/
theorem p2_table_lower_pos :
    0 < p2AppendixTableLower := by
  exact rational_certificate.p2_table_lower_pos

/-- The appendix reciprocal denominator enclosure `2.69` is positive. -/
theorem p2_denom_upper_pos :
    0 < p2AppendixDenomUpper := by
  exact rational_certificate.p2_denom_upper_pos

/-- The reciprocal of the appendix denominator enclosure is positive. -/
theorem p2_recip_denom_upper_pos :
    0 < 1 / p2AppendixDenomUpper := by
  exact rational_certificate.p2_recip_denom_upper_pos

/-- The rational appendix denominator bound `2.69` supports the decimal lower
bound `0.37`, since `0.37 < 1 / 2.69`. -/
theorem p2_table_lower_lt_recip_denom_upper :
    p2AppendixTableLower < 1 / p2AppendixDenomUpper := by
  exact rational_certificate.p2_table_lower_lt_recip_denom_upper

/-- The numerical reserves are strictly ordered in the direction needed by the
upper-boundary final assembly. -/
theorem reserve_ordering :
    0 < finalGapCoefficient ∧
      finalGapCoefficient < shiftCertifiedUpper ∧
      shiftCertifiedUpper < prefixCertifiedLower ∧
      prefixCertifiedLower < roomCertifiedLower := by
  norm_num [
    finalGapCoefficient,
    shiftCertifiedUpper,
    prefixCertifiedLower,
    roomCertifiedLower
  ]

/-- After paying both the final gap coefficient and the shift cost, the prefix
certificate still has positive rational room. -/
theorem prefix_room_after_gap_and_shift_pos :
    0 < prefixCertifiedLower - shiftCertifiedUpper - finalGapCoefficient := by
  norm_num [
    prefixCertifiedLower,
    shiftCertifiedUpper,
    finalGapCoefficient
  ]

/-- The certified room reserve dominates the prefix reserve with a positive
gap.  This is the numerical slack needed before the interval tail estimate is
paid. -/
theorem room_dominates_prefix_with_slack :
    0 < roomCertifiedLower - prefixCertifiedLower := by
  norm_num [
    roomCertifiedLower,
    prefixCertifiedLower
  ]

/-- The tail-ratio certificate is strictly below the final gap coefficient,
so the appendix tail estimate is numerically smaller than the final claimed
log-gap coefficient. -/
theorem tail_ratio_below_final_gap :
    tailRatioUpper < finalGapCoefficient := by
  norm_num [
    tailRatioUpper,
    finalGapCoefficient
  ]

/-- The prefix reserve remains positive after paying the shift cost, the final
gap coefficient, and the appendix tail ratio. -/
theorem prefix_room_after_tail_gap_and_shift_pos :
    0 <
      prefixCertifiedLower -
        shiftCertifiedUpper -
        finalGapCoefficient -
        tailRatioUpper := by
  norm_num [
    prefixCertifiedLower,
    shiftCertifiedUpper,
    finalGapCoefficient,
    tailRatioUpper
  ]

/-- The room reserve remains positive after paying the prefix reserve and the
appendix tail ratio. -/
theorem room_after_prefix_and_tail_pos :
    0 < roomCertifiedLower - prefixCertifiedLower - tailRatioUpper := by
  norm_num [
    roomCertifiedLower,
    prefixCertifiedLower,
    tailRatioUpper
  ]

/-- The room endpoint table lower bound `0.075` is strictly stronger than the
certified reserve `0.07` used by the upper bridge. -/
theorem room_table_supports_certified_lower :
    roomCertifiedLower < roomEndpointTableLower := by
  exact rational_certificate.room_table_supports_certified

/-- The tight-prefix endpoint table lower bound `0.00670` is strictly stronger
than the certified reserve `0.006` used by the upper bridge. -/
theorem tight_prefix_table_supports_certified_lower :
    prefixCertifiedLower < tightPrefixTableLower := by
  exact rational_certificate.tight_prefix_table_supports_certified



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
