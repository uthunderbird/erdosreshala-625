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

end Problem625.Analytical.UpperR2
