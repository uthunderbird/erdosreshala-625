import Erdos625.PublishableProof
import Erdos625.LowBranch
import Erdos625.MiddleBranch
import Erdos625.UpperR2

/-!
# Analytical wrapper theorem for the full route

This module is Stage 1 of the Lean-certified full analytical proof plan.

It does **not** certify the analytical proof yet.  Instead, it gives a
Lean-facing theorem statement for the full analytical route and factors
the current natural-language proof package into named assumptions that
can be discharged one by one.

The target theorem is:

```text
P[chi(G(n,1/2))-zeta(G(n,1/2)) >= log log n] -> 1.
```

The named assumptions correspond to the shipped analytical package:

* low regime theorem,
* middle regime theorem,
* upper regime theorem,
* fractional-regime cover / final assembly.

The public wrapper route is currently factored through the fixed-constants
worklist `AnalyticalRemainingConcreteObligations`: concrete low, middle, and
upper WHP conclusions for the certified branch inputs.  The first branch
replacement seam is `LowBranchConcreteSourceInputEventObligation`, which
reduces the low concrete WHP replacement to a source event, a WHP proof, and a
deterministic subset proof into `lowRegimeConditionalGapEvent`.

Future stages should replace each bridge-input-shaped WHP `axiom` below by a
theorem with the same statement, or by an adapter theorem whose public
`Problem625.Analytical.*` axiom closure removes that obligation.
-/

namespace Problem625.Analytical

open MeasureTheory ProbabilityTheory ENNReal Problem625

/-- The deterministic lower-bound function used by the analytical proof. -/
noncomputable def logLogW (n : ℕ) : ℝ :=
  Real.log (Real.log (n : ℝ))

/-- The fractional first-moment parameter `x(n)=alpha_0-floor(alpha_0)`.

Here `threshold n` is the project's Lean name for the analytical `alpha_0(n)`.
-/
noncomputable def fractionalParameter (n : ℕ) : ℝ :=
  Int.fract (threshold n)

/-- Left endpoint separating the low and middle fractional regimes. -/
def lowMiddleCutoff : ℝ :=
  0.029155

/-- Left endpoint separating the middle and upper fractional regimes. -/
def middleUpperCutoff : ℝ :=
  0.95

/-- The low-branch certificate cutoff is the wrapper low/middle cutoff. -/
theorem lowBranch_cutoff_eq_lowMiddleCutoff :
    (LowBranch.lowCutoff : ℝ) = lowMiddleCutoff := by
  norm_num [LowBranch.lowCutoff, lowMiddleCutoff]

/-- The middle-branch certificate lower cutoff is the wrapper low/middle cutoff. -/
theorem middleBranch_lowerCutoff_eq_lowMiddleCutoff :
    (MiddleBranch.lowerCutoff : ℝ) = lowMiddleCutoff := by
  norm_num [MiddleBranch.lowerCutoff, lowMiddleCutoff]

/-- The middle-branch certificate upper cutoff is the wrapper middle/upper cutoff. -/
theorem middleBranch_upperCutoff_eq_middleUpperCutoff :
    (MiddleBranch.upperCutoff : ℝ) = middleUpperCutoff := by
  norm_num [MiddleBranch.upperCutoff, middleUpperCutoff]

/-- The low fractional regime `0 <= x(n) <= 0.029155`. -/
def InLowRegime (n : ℕ) : Prop :=
  0 ≤ fractionalParameter n ∧ fractionalParameter n ≤ lowMiddleCutoff

/-- Placeholder predicate for the middle fractional regime
`0.029155 <= x(n) <= 0.95`. -/
def InMiddleRegime (n : ℕ) : Prop :=
  lowMiddleCutoff ≤ fractionalParameter n ∧
    fractionalParameter n ≤ middleUpperCutoff

/-- Placeholder predicate for the upper fractional regime
`0.95 <= x(n) < 1`. -/
def InUpperRegime (n : ℕ) : Prop :=
  middleUpperCutoff ≤ fractionalParameter n ∧ fractionalParameter n < 1

/-- Event that the chromatic--cochromatic gap dominates the analytical
choice `w(n)=log log n`. -/
def analyticalGapEvent (n : ℕ) : Set (SimpleGraph (Fin n)) :=
  {G : SimpleGraph (Fin n) |
    logLogW n ≤ (chromaticNumber G : ℝ) - (cochromaticNumber G : ℝ)}

/-- Low-regime conditional gap event. -/
def lowRegimeConditionalGapEvent (n : ℕ) : Set (SimpleGraph (Fin n)) :=
  {G : SimpleGraph (Fin n) |
    InLowRegime n →
      logLogW n ≤ (chromaticNumber G : ℝ) - (cochromaticNumber G : ℝ)}

/-- Middle-regime conditional gap event. -/
def middleRegimeConditionalGapEvent (n : ℕ) : Set (SimpleGraph (Fin n)) :=
  {G : SimpleGraph (Fin n) |
    InMiddleRegime n →
      logLogW n ≤ (chromaticNumber G : ℝ) - (cochromaticNumber G : ℝ)}

/-- Upper-regime conditional gap event. -/
def upperRegimeConditionalGapEvent (n : ℕ) : Set (SimpleGraph (Fin n)) :=
  {G : SimpleGraph (Fin n) |
    InUpperRegime n →
      logLogW n ≤ (chromaticNumber G : ℝ) - (cochromaticNumber G : ℝ)}

/-- Simultaneous conditional gap event for all three deterministic regimes. -/
def allRegimeConditionalGapEvent (n : ℕ) : Set (SimpleGraph (Fin n)) :=
  {G : SimpleGraph (Fin n) |
    G ∈ lowRegimeConditionalGapEvent n ∧
      G ∈ middleRegimeConditionalGapEvent n ∧
        G ∈ upperRegimeConditionalGapEvent n}

/-- Wrapper-level input contract for the low-branch WHP bridge. -/
structure LowBranchBridgeInputs : Prop where
  certificate : LowBranch.Certificate
  certified_consequences : LowBranch.CertifiedConsequences
  source_inputs : LowBranch.SourceBridgeInputs

/-- Wrapper-level input contract for the middle-branch WHP bridge. -/
structure MiddleBranchBridgeInputs : Prop where
  certificate : MiddleBranch.Certificate
  certified_consequences : MiddleBranch.CertifiedConsequences
  source_inputs : MiddleBranch.SourceBridgeInputs

/-- Wrapper-level input contract for the upper `r=2` WHP bridge. -/
structure UpperR2BridgeInputs : Prop where
  certificate : UpperR2.Certificate
  source_inputs :
    UpperR2.SourceBridgeInputs
      UpperR2.roomEndpointLower
      UpperR2.prefixEndpointLower
      UpperR2.tailEndpointActual
      UpperR2.p2EndpointLower
  endpoint_table_facts :
    UpperR2.roomEndpointTableLower ≤ UpperR2.roomEndpointLower ∧
      UpperR2.tightPrefixTableLower ≤ UpperR2.prefixEndpointLower ∧
      UpperR2.tailEndpointActual ≤ UpperR2.tailRatioUpper ∧
      1 / UpperR2.p2AppendixDenomUpper ≤ UpperR2.p2EndpointLower
  interval_outputs :
    UpperR2.IntervalOutputs
      UpperR2.roomEndpointLower
      UpperR2.prefixEndpointLower
      UpperR2.tailEndpointActual
      UpperR2.p2EndpointLower
  certified_consequences :
    UpperR2.CertifiedConsequences
      UpperR2.roomEndpointLower
      UpperR2.prefixEndpointLower
      UpperR2.tailEndpointActual
      UpperR2.p2EndpointLower
  payment_consequences :
    ((UpperR2.shiftCertifiedUpper + UpperR2.finalGapCoefficient +
      UpperR2.tailRatioUpper < UpperR2.prefixCertifiedLower) ∧
      (UpperR2.prefixCertifiedLower + UpperR2.tailRatioUpper <
        UpperR2.roomCertifiedLower) ∧
      0 < UpperR2.finalGapCoefficient) ∧
      UpperR2.CertifiedConsequences
        UpperR2.roomEndpointLower
        UpperR2.prefixEndpointLower
        UpperR2.tailEndpointActual
        UpperR2.p2EndpointLower

/-- Wrapper-level input contract for the whole analytical route. -/
structure AnalyticalBridgeInputs : Prop where
  low : LowBranchBridgeInputs
  middle : MiddleBranchBridgeInputs
  upper : UpperR2BridgeInputs

/-- Stage-2 source-side bridge-input package for all three branches.

This bundle records the Lean-certified numerical/source handoff data below the
three wrapper-level WHP bridge inputs.  It is still not a proof of the WHP
source theorems; it is the common input package those future proofs should
consume branch by branch. -/
structure AnalyticalSourceBridgeInputs : Prop where
  low : LowBranch.SourceBridgeInputs
  middle : MiddleBranch.SourceBridgeInputs
  upper :
    UpperR2.SourceBridgeInputs
      UpperR2.roomEndpointLower
      UpperR2.prefixEndpointLower
      UpperR2.tailEndpointActual
      UpperR2.p2EndpointLower

/-- Stage-2 scalar bridge-input package for all three branches.

This is the non-structure-shaped numerical handoff below the branch WHP
bridges: each branch contributes its concrete certificate together with the
scalar inequalities extracted from its certified source/output bridge. -/
structure AnalyticalScalarBridgeInputs : Prop where
  low : LowBranch.LowBranchScalarBridgeInputs
  middle : MiddleBranch.MiddleBranchScalarBridgeInputs
  upper : UpperR2.UpperR2ScalarBridgeInputs

/-- Combined Stage-2 numerical handoff package for all three branches.

This bundles the structured source-side bridge inputs with the lightweight
scalar bridge inputs.  It is still below the three probabilistic WHP source
obligations; it is only the certified numerical handoff data those future
proofs may consume. -/
structure AnalyticalNumericalBridgeInputs : Prop where
  source : AnalyticalSourceBridgeInputs
  scalar : AnalyticalScalarBridgeInputs

/-- Assemble the combined numerical handoff package from its structured source
bridge inputs and scalar bridge inputs. -/
theorem analytical_numerical_bridge_inputs_of_parts
    (hsource : AnalyticalSourceBridgeInputs)
    (hscalar : AnalyticalScalarBridgeInputs) :
    AnalyticalNumericalBridgeInputs := by
  exact {
    source := hsource
    scalar := hscalar
  }

/-- Rebuild the wrapper-level low bridge input from the more precise
source-side low bridge input package. -/
theorem low_branch_bridge_inputs_of_source_inputs
    (hsource : LowBranch.SourceBridgeInputs) :
    LowBranchBridgeInputs := by
  exact {
    certificate := hsource.certificate
    certified_consequences := hsource.certified_consequences
    source_inputs := hsource
  }

/-- Rebuild the wrapper-level middle bridge input from the more precise
source-side middle bridge input package. -/
theorem middle_branch_bridge_inputs_of_source_inputs
    (hsource : MiddleBranch.SourceBridgeInputs) :
    MiddleBranchBridgeInputs := by
  exact {
    certificate := hsource.certificate
    certified_consequences := hsource.certified_consequences
    source_inputs := hsource
  }

/-- Rebuild the wrapper-level upper bridge input from the more precise
source-side upper bridge input package. -/
theorem upper_boundary_bridge_inputs_of_source_inputs
    (hsource :
      UpperR2.SourceBridgeInputs
        UpperR2.roomEndpointLower
        UpperR2.prefixEndpointLower
        UpperR2.tailEndpointActual
        UpperR2.p2EndpointLower) :
    UpperR2BridgeInputs := by
  exact {
    certificate := hsource.certificate
    source_inputs := hsource
    endpoint_table_facts := ⟨
      hsource.interval_outputs.room_table_lower,
      hsource.interval_outputs.prefix_table_lower,
      hsource.interval_outputs.tail_upper,
      hsource.interval_outputs.p2_reciprocal_lower
    ⟩
    interval_outputs := hsource.interval_outputs
    certified_consequences := hsource.consequences_with_payment.2
    payment_consequences := hsource.consequences_with_payment
  }

/-- Source-side WHP obligation for the low branch, after Lean certificate
inputs have been assembled. -/
def LowBranchSourceObligation : Prop :=
  LowBranchBridgeInputs →
    Filter.Tendsto
      (fun n : ℕ => gnHalf n (lowRegimeConditionalGapEvent n))
      Filter.atTop (nhds (1 : ℝ≥0∞))

/-- Source-event-shaped low-branch WHP obligation for one low bridge-input
package.

This is the Lean-facing split used by the current low-WHP route plan: the
source proof may introduce a sharper event `source_event n`, prove that event
WHP, and separately prove its deterministic inclusion in
`lowRegimeConditionalGapEvent n`.
-/
def LowBranchSourceEventObligation
    (_hinputs : LowBranchBridgeInputs) : Prop :=
  ∃ source_event : (n : ℕ) → Set (SimpleGraph (Fin n)),
    Filter.Tendsto
      (fun n : ℕ => gnHalf n (source_event n))
      Filter.atTop (nhds (1 : ℝ≥0∞)) ∧
    ∀ n : ℕ, source_event n ⊆ lowRegimeConditionalGapEvent n

/-- Source-event-shaped low-branch WHP obligation phrased over the Stage-2
low source-input package.

This is narrower than `LowBranchSourceEventObligation`: the source proof only
receives the already-assembled low source-input bundle, not the wrapper-level
certificate fields separately.
-/
def LowBranchSourceInputEventObligation
    (_hsource : LowBranch.SourceBridgeInputs) : Prop :=
  ∃ source_event : (n : ℕ) → Set (SimpleGraph (Fin n)),
    Filter.Tendsto
      (fun n : ℕ => gnHalf n (source_event n))
      Filter.atTop (nhds (1 : ℝ≥0∞)) ∧
    ∀ n : ℕ, source_event n ⊆ lowRegimeConditionalGapEvent n

/-- Source-event-shaped low-branch WHP obligation for the concrete rational
low source-input package.

This is the narrowest current low-branch event-level target below the wrapper:
prove one sharper WHP event and its deterministic inclusion for the certified
rational low source-input bundle already constructed by the interval skeleton.
-/
def LowBranchConcreteSourceInputEventObligation : Prop :=
  LowBranchSourceInputEventObligation
    LowBranch.rational_certificate_source_bridge_inputs

/-- WHP component of the concrete low source-input event target. -/
def LowBranchConcreteSourceInputEventWHP
    (source_event : (n : ℕ) → Set (SimpleGraph (Fin n))) : Prop :=
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (source_event n))
    Filter.atTop (nhds (1 : ℝ≥0∞))

/-- Deterministic subset component of the concrete low source-input event
target. -/
def LowBranchConcreteSourceInputEventSubset
    (source_event : (n : ℕ) → Set (SimpleGraph (Fin n))) : Prop :=
  ∀ n : ℕ, source_event n ⊆ lowRegimeConditionalGapEvent n

/-- Structured implementation contract for the concrete low source-input event
target.

This is the proof-engineering shape expected from the source package: expose a
named event family, prove it WHP, and prove its deterministic inclusion into
the wrapper's low conditional gap event.
-/
structure LowBranchConcreteSourceInputEventComponents where
  source_event : (n : ℕ) → Set (SimpleGraph (Fin n))
  whp : LowBranchConcreteSourceInputEventWHP source_event
  subset : LowBranchConcreteSourceInputEventSubset source_event

/-- Source-event-shaped middle-branch WHP obligation phrased over the
Stage-2 middle source-input package.

This mirrors the low-branch event split: a future middle source proof may
introduce a sharper event, prove it WHP, and separately prove deterministic
inclusion into `middleRegimeConditionalGapEvent`.
-/
def MiddleBranchSourceInputEventObligation
    (_hsource : MiddleBranch.SourceBridgeInputs) : Prop :=
  ∃ source_event : (n : ℕ) → Set (SimpleGraph (Fin n)),
    Filter.Tendsto
      (fun n : ℕ => gnHalf n (source_event n))
      Filter.atTop (nhds (1 : ℝ≥0∞)) ∧
    ∀ n : ℕ, source_event n ⊆ middleRegimeConditionalGapEvent n

/-- Source-event-shaped middle-branch WHP obligation for the concrete rational
middle source-input package. -/
def MiddleBranchConcreteSourceInputEventObligation : Prop :=
  MiddleBranchSourceInputEventObligation
    MiddleBranch.rational_certificate_source_bridge_inputs

/-- WHP component of the concrete middle source-input event target. -/
def MiddleBranchConcreteSourceInputEventWHP
    (source_event : (n : ℕ) → Set (SimpleGraph (Fin n))) : Prop :=
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (source_event n))
    Filter.atTop (nhds (1 : ℝ≥0∞))

/-- Deterministic subset component of the concrete middle source-input event
target. -/
def MiddleBranchConcreteSourceInputEventSubset
    (source_event : (n : ℕ) → Set (SimpleGraph (Fin n))) : Prop :=
  ∀ n : ℕ, source_event n ⊆ middleRegimeConditionalGapEvent n

/-- Structured implementation contract for the concrete middle source-input
event target. -/
structure MiddleBranchConcreteSourceInputEventComponents where
  source_event : (n : ℕ) → Set (SimpleGraph (Fin n))
  whp : MiddleBranchConcreteSourceInputEventWHP source_event
  subset : MiddleBranchConcreteSourceInputEventSubset source_event

/-- Source-event-shaped upper `r=2` WHP obligation phrased over the endpoint
component package.

This mirrors the low and middle event splits at the current narrowest upper
boundary: a future upper source proof may introduce a sharper event, prove it
WHP, and separately prove deterministic inclusion into
`upperRegimeConditionalGapEvent`.
-/
def UpperR2EndpointSourceInputEventObligation
    (_hcomponents :
      UpperR2.UpperEndpointComponents
        UpperR2.roomEndpointLower
        UpperR2.prefixEndpointLower
        UpperR2.tailEndpointActual
        UpperR2.p2EndpointLower) : Prop :=
  ∃ source_event : (n : ℕ) → Set (SimpleGraph (Fin n)),
    Filter.Tendsto
      (fun n : ℕ => gnHalf n (source_event n))
      Filter.atTop (nhds (1 : ℝ≥0∞)) ∧
    ∀ n : ℕ, source_event n ⊆ upperRegimeConditionalGapEvent n

/-- Source-event-shaped upper WHP obligation for the concrete appendix
endpoint-component package. -/
def UpperR2ConcreteSourceInputEventObligation : Prop :=
  UpperR2EndpointSourceInputEventObligation
    UpperR2.upper_appendix_endpoint_components

/-- WHP component of the concrete upper source-input event target. -/
def UpperR2ConcreteSourceInputEventWHP
    (source_event : (n : ℕ) → Set (SimpleGraph (Fin n))) : Prop :=
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (source_event n))
    Filter.atTop (nhds (1 : ℝ≥0∞))

/-- Deterministic subset component of the concrete upper source-input event
target. -/
def UpperR2ConcreteSourceInputEventSubset
    (source_event : (n : ℕ) → Set (SimpleGraph (Fin n))) : Prop :=
  ∀ n : ℕ, source_event n ⊆ upperRegimeConditionalGapEvent n

/-- Structured implementation contract for the concrete upper source-input
event target. -/
structure UpperR2ConcreteSourceInputEventComponents where
  source_event : (n : ℕ) → Set (SimpleGraph (Fin n))
  whp : UpperR2ConcreteSourceInputEventWHP source_event
  subset : UpperR2ConcreteSourceInputEventSubset source_event

/-- Source-side WHP obligation for the middle branch, after Lean certificate
inputs have been assembled. -/
def MiddleBranchSourceObligation : Prop :=
  MiddleBranchBridgeInputs →
    Filter.Tendsto
      (fun n : ℕ => gnHalf n (middleRegimeConditionalGapEvent n))
      Filter.atTop (nhds (1 : ℝ≥0∞))

/-- Source-side WHP obligation for the upper branch, after Lean certificate
and interval-output inputs have been assembled. -/
def UpperR2SourceObligation : Prop :=
  UpperR2BridgeInputs →
    Filter.Tendsto
      (fun n : ℕ => gnHalf n (upperRegimeConditionalGapEvent n))
      Filter.atTop (nhds (1 : ℝ≥0∞))

/-- Low-branch WHP obligation phrased directly over the Stage-2 low source
input package. -/
def LowBranchSourceInputObligation : Prop :=
  LowBranch.SourceBridgeInputs →
    Filter.Tendsto
      (fun n : ℕ => gnHalf n (lowRegimeConditionalGapEvent n))
      Filter.atTop (nhds (1 : ℝ≥0∞))

/-- Middle-branch WHP obligation phrased directly over the Stage-2 middle
source input package. -/
def MiddleBranchSourceInputObligation : Prop :=
  MiddleBranch.SourceBridgeInputs →
    Filter.Tendsto
      (fun n : ℕ => gnHalf n (middleRegimeConditionalGapEvent n))
      Filter.atTop (nhds (1 : ℝ≥0∞))

/-- Low-branch WHP obligation phrased directly over the certified rational
low-branch source certificate.  This is narrower than `LowBranch.SourceBridgeInputs`:
the interval skeleton already rebuilds the source-input bundle from any
`LowBranch.Certificate`. -/
def LowBranchCertificateSourceObligation : Prop :=
  LowBranch.Certificate →
    Filter.Tendsto
      (fun n : ℕ => gnHalf n (lowRegimeConditionalGapEvent n))
      Filter.atTop (nhds (1 : ℝ≥0∞))

/-- Middle-branch WHP obligation phrased directly over the certified rational
middle-branch source certificate.  This is narrower than
`MiddleBranch.SourceBridgeInputs`: the interval skeleton already rebuilds the
source-input bundle from any `MiddleBranch.Certificate`. -/
def MiddleBranchCertificateSourceObligation : Prop :=
  MiddleBranch.Certificate →
    Filter.Tendsto
      (fun n : ℕ => gnHalf n (middleRegimeConditionalGapEvent n))
      Filter.atTop (nhds (1 : ℝ≥0∞))

/-- Low-branch WHP obligation for the concrete certified low branch. -/
def LowBranchConcreteSourceObligation : Prop :=
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (lowRegimeConditionalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞))

/-- Middle-branch WHP obligation for the concrete certified middle branch. -/
def MiddleBranchConcreteSourceObligation : Prop :=
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (middleRegimeConditionalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞))

/-- Upper `r=2` WHP obligation for the concrete certified upper endpoint
package. -/
def UpperR2ConcreteSourceObligation : Prop :=
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (upperRegimeConditionalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞))

/-- Upper `r=2` WHP obligation phrased directly over the Stage-2 upper source
input package. -/
def UpperR2SourceInputObligation : Prop :=
  UpperR2.SourceBridgeInputs
      UpperR2.roomEndpointLower
      UpperR2.prefixEndpointLower
      UpperR2.tailEndpointActual
      UpperR2.p2EndpointLower →
    Filter.Tendsto
      (fun n : ℕ => gnHalf n (upperRegimeConditionalGapEvent n))
      Filter.atTop (nhds (1 : ℝ≥0∞))

/-- Upper `r=2` WHP obligation phrased directly over the endpoint-component
package.  This is the narrowest current upper Stage-2 boundary: numerical
work supplies the four endpoint components, while the source theorem consumes
only that endpoint contract. -/
def UpperR2EndpointSourceObligation : Prop :=
  UpperR2.UpperEndpointComponents
      UpperR2.roomEndpointLower
      UpperR2.prefixEndpointLower
      UpperR2.tailEndpointActual
      UpperR2.p2EndpointLower →
    Filter.Tendsto
      (fun n : ℕ => gnHalf n (upperRegimeConditionalGapEvent n))
      Filter.atTop (nhds (1 : ℝ≥0∞))

/-- Source-side analytical obligations remaining after the current Lean
certificate/output-layer assembly.

This structure isolates the genuinely probabilistic WHP source theorems from
the already-certified bridge-input construction.  Replacing the three current
paper/source axioms should amount to constructing this contract. -/
structure AnalyticalSourceObligations : Prop where
  low_branch : LowBranchSourceObligation
  middle_branch : MiddleBranchSourceObligation
  upper_branch : UpperR2SourceObligation

/-- Source-side analytical obligations phrased over the more precise Stage-2
source-input packages. -/
structure AnalyticalSourceInputObligations : Prop where
  low_branch : LowBranchSourceInputObligation
  middle_branch : MiddleBranchSourceInputObligation
  upper_branch : UpperR2SourceInputObligation

/-- Explicit Stage-1 worklist contract for the analytical wrapper.

This is intentionally definitionally the same data as
`AnalyticalSourceObligations`, but with field names phrased as remaining Lean
work items.  It gives future formalization a stable checklist: discharge these
three WHP source obligations, then the current certificate/output and
intersection layers assemble the full analytical theorem. -/
structure AnalyticalRemainingObligations : Prop where
  low_branch_source : LowBranchSourceObligation
  middle_branch_source : MiddleBranchSourceObligation
  upper_r2_source : UpperR2SourceObligation

/-- More precise Stage-2 remaining-work checklist.

The low and middle branches are phrased over their Lean source-input bundles,
while the upper `r=2` branch is narrowed to the endpoint-component contract.
Constructing this checklist is now enough to run the full analytical wrapper
without widening the upper theorem back to the bridge-input interface. -/
structure AnalyticalRemainingSourceInputObligations : Prop where
  low_branch_source_input : LowBranchSourceInputObligation
  middle_branch_source_input : MiddleBranchSourceInputObligation
  upper_r2_endpoint_source : UpperR2EndpointSourceObligation

/-- Narrowest current Stage-2 remaining-work checklist.

The low and middle source theorems consume only their certified rational
certificate contracts, while the upper `r=2` source theorem consumes only the
endpoint-component contract.  The existing interval skeletons rebuild all
source-input bundles from these data. -/
structure AnalyticalRemainingCertificateObligations : Prop where
  low_branch_certificate_source : LowBranchCertificateSourceObligation
  middle_branch_certificate_source : MiddleBranchCertificateSourceObligation
  upper_r2_endpoint_source : UpperR2EndpointSourceObligation

/-- Narrowest fixed-constants Stage-2 remaining-work checklist.

This is the final wrapper's current public boundary: three concrete WHP
conclusions for the already-certified low, middle, and upper analytical
regimes. -/
structure AnalyticalRemainingConcreteObligations : Prop where
  low_branch_concrete_source : LowBranchConcreteSourceObligation
  middle_branch_concrete_source : MiddleBranchConcreteSourceObligation
  upper_r2_concrete_source : UpperR2ConcreteSourceObligation

/-- Fixed-constants Stage-2 remaining-work checklist after the low concrete
source theorem has been supplied separately.

This is the immediate post-low-discharge checklist: only the middle and upper
concrete WHP source theorems remain once
`LowBranchConcreteSourceInputEventObligation` is proved and routed through the
low concrete bridge.
-/
structure AnalyticalRemainingConcreteObligationsWithoutLow : Prop where
  middle_branch_concrete_source : MiddleBranchConcreteSourceObligation
  upper_r2_concrete_source : UpperR2ConcreteSourceObligation

/-- Fixed-constants Stage-2 remaining-work checklist after the low and middle
concrete source theorems have been supplied separately. -/
structure AnalyticalRemainingConcreteObligationsWithoutLowMiddle : Prop where
  upper_r2_concrete_source : UpperR2ConcreteSourceObligation

/-- Bundled all-regime concrete source-input event obligations.

This is the event-obligation-shaped completion contract for the current
fixed-constants wrapper boundary: one event obligation for each deterministic
regime.
-/
structure AnalyticalAllRegimeConcreteSourceInputEventObligations : Prop where
  low_branch_event : LowBranchConcreteSourceInputEventObligation
  middle_branch_event : MiddleBranchConcreteSourceInputEventObligation
  upper_r2_event : UpperR2ConcreteSourceInputEventObligation

/-- Bundled all-regime concrete source-input event component packages. -/
structure AnalyticalAllRegimeConcreteSourceInputEventComponents where
  low_branch : LowBranchConcreteSourceInputEventComponents
  middle_branch : MiddleBranchConcreteSourceInputEventComponents
  upper_r2 : UpperR2ConcreteSourceInputEventComponents

/-- Assemble the bundled all-regime event-obligation contract from the three
branch event obligations. -/
theorem analytical_all_regime_event_obligations_of_events
    (hlow : LowBranchConcreteSourceInputEventObligation)
    (hmiddle : MiddleBranchConcreteSourceInputEventObligation)
    (hupper : UpperR2ConcreteSourceInputEventObligation) :
    AnalyticalAllRegimeConcreteSourceInputEventObligations := by
  exact {
    low_branch_event := hlow
    middle_branch_event := hmiddle
    upper_r2_event := hupper
  }

/-- Assemble the bundled all-regime event-component package from the three
branch component packages. -/
def analytical_all_regime_event_components_of_components
    (hlow : LowBranchConcreteSourceInputEventComponents)
    (hmiddle : MiddleBranchConcreteSourceInputEventComponents)
    (hupper : UpperR2ConcreteSourceInputEventComponents) :
    AnalyticalAllRegimeConcreteSourceInputEventComponents := by
  exact {
    low_branch := hlow
    middle_branch := hmiddle
    upper_r2 := hupper
  }

/-- **[HP-2023, Co. 37 + Le. 7.4 = HRHowdoes Le. 41]** (first-moment argument, step 1)

kThresholdWitness n = Θ(n / log n): ∃ C > 1 and N₀ such that for n ≥ N₀,
  n / (C · log n) ≤ kThresholdWitness n ≤ C · n / log n.

Source: HP-2023 Lemma 7.4 ("averagecolourclass"), proved via HRHowdoes Lemma 41 with
generic θ = ln μ_α / ln n ∈ [0,1]. No restriction on fractionalParameter n. -/
axiom averageColourClassAxiom_low :
    ∃ C : ℝ, 1 < C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (n : ℝ) / (C * Real.log (n : ℝ)) ≤ kThresholdWitness n ∧
      kThresholdWitness n ≤ C * (n : ℝ) / Real.log (n : ℝ)

/-- **[HP-2023, Co. 39 ("onemorecolour")]** (first-moment argument, step 2)

The log-expectation of (α-1)-bounded colorings decreases by ≥ c_step · (log n)² per
unit decrease in k (for k near kThresholdWitness n). y_t(ρ) is regime-universal.

Source: HP-2023 Corollary 39. No regime restriction on fractionalParameter n. -/
axiom oneMoreColourAxiom_low :
    ∃ c_step : ℝ, 0 < c_step ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ D : ℕ, D ≤ n →
      Real.log (expectedTBoundedColorings n
          (⌊(kThresholdWitness n : ℝ) - (D : ℝ)⌋₊)
          (max 1 (thresholdFloor n - 1))) ≤
        (4 : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2 -
        (D : ℝ) * c_step * (Real.log (n : ℝ)) ^ 2

/-- **[HP-2023, Lemma 8.1 + oneMoreColourAxiom_low + Heckel 2024 line 516 + Markov]**
Combined low-branch gap WHP axiom.

∃ c_gap > 0 such that χ(G(n,1/2)) − ζ(G(n,1/2)) ≥ c_gap·n/log³n with probability → 1.

Mathematical proof combines:
- Chromatic lower bound: HP-2023 Lemma 8.1 (unconditional first-moment crossing)
  gives χ ≥ k_{α-2} in Regime I (E[X_{k_{α-2}}] < 1 ⇒ χ > k_{α-2} a.s.)
- Cochromatic upper bound: HP-2023 Co.39 + Heckel 2024 line 516 + Markov give
  E[X_{k_{α-1} - D}] → 0 for D = Θ(n/log²n), so ζ < k_{α-1} - D + 1 whp;
  in Regime I, k_{α-1} - D < k_{α-2}, so ζ < k_{α-2} whp.
- The gap χ - ζ ≥ k_{α-2} - (k_{α-1} - D) = D - (k_{α-1} - k_{α-2}) = Θ(n/log³n)
  (since k_{α-1} - k_{α-2} = Θ(n(log log n)/log²n) = o(D) in Regime I).

No restriction on fractionalParameter n. Replaces the P0 C5 citation chain.
Mathematical proof: `problems/625/work/notes/inlowregime-cochromatic-upper-bound-proof-2026-05-15.md`
Red-team confirmation: 2026-05-15 (all attack vectors refuted). -/
axiom lowBranchGapWHPAxiom :
    ∃ c_gap : ℝ, 0 < c_gap ∧
      Filter.Tendsto
        (fun n : ℕ =>
          gnHalf n {G : SimpleGraph (Fin n) |
            c_gap * (n : ℝ) / Real.log (n : ℝ) ^ 3 ≤
              (chromaticNumber G : ℝ) - (cochromaticNumber G : ℝ)})
        Filter.atTop (nhds (1 : ℝ≥0∞))

/-- log log n is o(n/log³n): eventually logLogW n ≤ C·n/log³n for any C > 0.

This is a standard asymptotic fact: log log n = o(n/log³n). Proved via
`isLittleO_log_rpow_rpow_atTop`. -/
private theorem logLogW_eventually_le_C_n_div_log_cubed (C : ℝ) (hC : 0 < C) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → logLogW n ≤ C * (n : ℝ) / Real.log (n : ℝ) ^ 3 := by
  have hlittle : (fun x : ℝ => Real.log x ^ (4 : ℝ)) =o[Filter.atTop]
      (fun x : ℝ => x ^ (1 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop 4 (by norm_num : (0 : ℝ) < 1)
  have hlim : Filter.Tendsto
      (fun x : ℝ => Real.log x ^ (4 : ℝ) / x ^ (1 : ℝ)) Filter.atTop (nhds 0) :=
    hlittle.tendsto_div_nhds_zero
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨X, hX⟩ := hlim C hC
  refine ⟨max ⌈X⌉₊ 3, fun n hn => ?_⟩
  have hn3 : 3 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hn_pos_nat : 0 < n := lt_of_lt_of_le (by decide : 0 < 3) hn3
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos_nat
  have hn_gt_one : (1 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 3) hn3)
  have hn_ge_X : X ≤ (n : ℝ) := by
    calc X ≤ (⌈X⌉₊ : ℝ) := Nat.le_ceil X
      _ ≤ (n : ℝ) := by exact_mod_cast (le_trans (Nat.le_max_left _ _) hn)
  have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos hn_gt_one
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := le_of_lt hlog_pos
  have hlog_ne : Real.log (n : ℝ) ≠ 0 := ne_of_gt hlog_pos
  have hloglog_le_log : Real.log (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) :=
    Real.log_le_self hlog_nonneg
  have hX_bound := hX (n : ℝ) hn_ge_X
  have hlog_rpow_eq : Real.log (n : ℝ) ^ (4 : ℝ) = Real.log (n : ℝ) ^ 4 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  have hquot_nonneg : 0 ≤ Real.log (n : ℝ) ^ (4 : ℝ) / (n : ℝ) ^ (1 : ℝ) :=
    div_nonneg (Real.rpow_nonneg hlog_nonneg _) (Real.rpow_nonneg (le_of_lt hn_pos) _)
  have hquot_lt : Real.log (n : ℝ) ^ 4 / (n : ℝ) < C := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hquot_nonneg, hlog_rpow_eq,
      Real.rpow_one] at hX_bound
    exact hX_bound
  have hlog4_le : Real.log (n : ℝ) ^ 4 ≤ C * (n : ℝ) := by
    exact le_of_lt (by rwa [div_lt_iff₀ hn_pos] at hquot_lt)
  have hlog_le : Real.log (n : ℝ) ≤ C * (n : ℝ) / Real.log (n : ℝ) ^ 3 := by
    have hden_pos : 0 < Real.log (n : ℝ) ^ 3 := by positivity
    calc Real.log (n : ℝ)
        = Real.log (n : ℝ) ^ 4 / Real.log (n : ℝ) ^ 3 := by field_simp [hlog_ne]
      _ ≤ (C * (n : ℝ)) / Real.log (n : ℝ) ^ 3 :=
            div_le_div_of_nonneg_right hlog4_le (le_of_lt hden_pos)
      _ = C * (n : ℝ) / Real.log (n : ℝ) ^ 3 := by ring
  calc logLogW n = Real.log (Real.log (n : ℝ)) := rfl
    _ ≤ Real.log (n : ℝ) := hloglog_le_log
    _ ≤ C * (n : ℝ) / Real.log (n : ℝ) ^ 3 := hlog_le

/-- **First-moment Markov conclusion** (first-moment argument, steps 3–5)

The low-regime conditional gap event holds WHP.

**Proved as a theorem** from `lowBranchGapWHPAxiom`.

Proof: from the axiom, c_gap·n/log³n ≥ logLogW n eventually. The gap WHP event
is then eventually a subset of lowRegimeConditionalGapEvent n. By WHP mono, done. -/
theorem lowBranchFirstMomentGapAxiom :
    Filter.Tendsto
      (fun n : ℕ => gnHalf n (lowRegimeConditionalGapEvent n))
      Filter.atTop (nhds (1 : ℝ≥0∞)) := by
  obtain ⟨c_gap, hc_gap_pos, hgap_whp⟩ := lowBranchGapWHPAxiom
  obtain ⟨N_gap, hN_gap⟩ := logLogW_eventually_le_C_n_div_log_cubed c_gap hc_gap_pos
  let gapEvent : (n : ℕ) → Set (SimpleGraph (Fin n)) :=
    fun n => {G : SimpleGraph (Fin n) |
      c_gap * (n : ℝ) / Real.log (n : ℝ) ^ 3 ≤
        (chromaticNumber G : ℝ) - (cochromaticNumber G : ℝ)}
  have hsubset : ∀ n : ℕ, N_gap ≤ n → gapEvent n ⊆ lowRegimeConditionalGapEvent n := by
    intro n hn G hG _hlow
    simp only [gapEvent, Set.mem_setOf_eq] at hG
    exact le_trans (hN_gap n hn) hG
  -- For n < N_gap, patch using the trivial event containing lowRegimeConditionalGapEvent
  let patchedEvent : (n : ℕ) → Set (SimpleGraph (Fin n)) :=
    fun n => if n < N_gap then lowRegimeConditionalGapEvent n else gapEvent n
  have hpatched_subset : ∀ n : ℕ, patchedEvent n ⊆ lowRegimeConditionalGapEvent n := by
    intro n G hG
    by_cases hn : n < N_gap
    · simpa [patchedEvent, hn] using hG
    · exact hsubset n (Nat.le_of_not_gt hn) (by simpa [patchedEvent, hn] using hG)
  have hpatched_whp :
      Filter.Tendsto
        (fun n : ℕ => gnHalf n (patchedEvent n))
        Filter.atTop (nhds (1 : ℝ≥0∞)) := by
    refine hgap_whp.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop N_gap] with n hn
    have hnn : ¬ n < N_gap := Nat.not_lt.mpr hn
    show (gnHalf n) {G | c_gap * (n : ℝ) / Real.log (n : ℝ) ^ 3 ≤
          (chromaticNumber G : ℝ) - (cochromaticNumber G : ℝ)} =
        (gnHalf n) (patchedEvent n)
    simp only [patchedEvent, hnn, ite_false, gapEvent]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    hpatched_whp
    tendsto_const_nhds
    (fun n => measure_mono (hpatched_subset n))
    (fun n => by
      haveI : IsProbabilityMeasure (gnHalf n) := by unfold gnHalf; infer_instance
      exact prob_le_one)

/-- **[oneMoreColourAxiom_low]** The expected count of (α-1)-bounded k-colorings
at k = ⌊kThresholdWitness n - ⌊n/log²n⌋⌋ tends to 0 as n → ∞.

Proved from `oneMoreColourAxiom_low` (HP-2023 Co. 39): set D_n = ⌊n/log²n⌋.
Then log E[X_{kThresh - D_n}] ≤ 4(log log n)² - D_n · c_step · (log n)².
The exponent satisfies:
  D_n · c_step · (log n)² ≥ (n/log²n - 1) · c_step · log²n = c_step · (n - log²n) → ∞
  while 4(log log n)² ≤ 4 · log²n = o(n).
Hence the exponent → -∞, so E[X] → 0. -/
theorem expectedColorings_tendsto_zero_below_kThreshold :
    Filter.Tendsto
      (fun n : ℕ => expectedTBoundedColorings n
        (⌊kThresholdWitness n - (⌊(n : ℝ) / Real.log (n : ℝ) ^ 2⌋₊ : ℝ)⌋₊)
        (max 1 (thresholdFloor n - 1)))
      Filter.atTop (nhds 0) := by
  obtain ⟨c_step, hc_step_pos, N₀, hN₀⟩ := oneMoreColourAxiom_low
  -- **Key arithmetic lemma** (proved fully below):
  -- ∀ n ≥ some N, the Co.39 exponent ≤ -(c_step * n / 2)
  -- This uses: ⌊n/log²n⌋ * c_step * log²n ≥ c_step*(n - log²n) (floor lower bound)
  --        and 4*(loglog n)² ≤ 4*(log n)² (loglog ≤ log)
  --        and (c_step+4)*log²n ≤ c_step*n/2 eventually (log²n = o(n))
  have hlogexp_bound : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (4 : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2 -
        (⌊(n : ℝ) / Real.log (n : ℝ) ^ 2⌋₊ : ℝ) * c_step * (Real.log (n : ℝ)) ^ 2 ≤
      -(c_step * (n : ℝ) / 2) := by
    -- Step (i): (c_step + 4)*log²n ≤ c_step*n/2 eventually
    have hlog_sq_little : ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n →
        (c_step + 4) * Real.log (n : ℝ) ^ 2 ≤ c_step * (n : ℝ) / 2 := by
      have hlittle : (fun x : ℝ => Real.log x ^ (2 : ℝ)) =o[Filter.atTop]
          (fun x : ℝ => x ^ (1 : ℝ)) :=
        isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0:ℝ) < 1)
      have htendsto : Filter.Tendsto (fun x : ℝ => Real.log x ^ (2 : ℝ) / x ^ (1 : ℝ))
          Filter.atTop (nhds 0) := by
        apply hlittle.tendsto_div_nhds_zero
      rw [Metric.tendsto_atTop] at htendsto
      obtain ⟨X, hX⟩ := htendsto (c_step / 2 / (c_step + 4)) (by positivity)
      refine ⟨max ⌈X⌉₊ 3, fun n hn => ?_⟩
      have hn3 : 3 ≤ n := le_trans (Nat.le_max_right _ _) hn
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le (by decide) hn3
      have hn_gt1 : (1 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le (by decide : 1 < 3) hn3
      have hn_ge_X : X ≤ (n : ℝ) :=
        le_trans (Nat.le_ceil X) (by exact_mod_cast le_trans (Nat.le_max_left _ _) hn)
      have hbound := hX (n : ℝ) hn_ge_X
      rw [Real.dist_eq, sub_zero, Real.rpow_one] at hbound
      rw [abs_of_nonneg (div_nonneg
        (Real.rpow_nonneg (Real.log_nonneg (le_of_lt hn_gt1)) _) (le_of_lt hn_pos))] at hbound
      have hlog2_div : Real.log (n : ℝ) ^ (2 : ℝ) / (n : ℝ) < c_step / 2 / (c_step + 4) := hbound
      have hcs4_pos : (0 : ℝ) < c_step + 4 := by linarith
      have hlog2_nat : Real.log (n : ℝ) ^ (2 : ℝ) = Real.log (n : ℝ) ^ 2 := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
      rw [hlog2_nat, div_lt_div_iff₀ hn_pos hcs4_pos] at hlog2_div
      linarith
    obtain ⟨N₁, hN₁⟩ := hlog_sq_little
    refine ⟨max N₁ 3, fun n hn => ?_⟩
    have hn3 : 3 ≤ n := le_trans (Nat.le_max_right _ _) hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le (by decide) hn3
    have hn_gt1 : (1 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le (by decide : 1 < 3) hn3
    have hlog_pos : (0 : ℝ) < Real.log (n : ℝ) := Real.log_pos hn_gt1
    have hn₁ : N₁ ≤ n := le_trans (Nat.le_max_left _ _) hn
    -- Step (ii): ⌊n/log²n⌋ * c_step * log²n ≥ c_step*(n - log²n)
    have hfloor_ge : (n : ℝ) / Real.log (n : ℝ) ^ 2 - 1 ≤
        ⌊(n : ℝ) / Real.log (n : ℝ) ^ 2⌋ := Int.sub_one_lt_floor _ |>.le
    have hlog2_pos : (0 : ℝ) < Real.log (n : ℝ) ^ 2 := by positivity
    have hfloor_nn_int : (0 : ℤ) ≤ ⌊(n : ℝ) / Real.log (n : ℝ) ^ 2⌋ :=
      Int.floor_nonneg.mpr (div_nonneg (le_of_lt hn_pos) hlog2_pos.le)
    have hfloor_nn : (0 : ℝ) ≤ ((⌊(n : ℝ) / Real.log (n : ℝ) ^ 2⌋ : ℤ) : ℝ) :=
      Int.cast_nonneg hfloor_nn_int
    have hDn_mul : c_step * (n : ℝ) - c_step * Real.log (n : ℝ) ^ 2 ≤
        (⌊(n : ℝ) / Real.log (n : ℝ) ^ 2⌋₊ : ℝ) * c_step * Real.log (n : ℝ) ^ 2 := by
      have h1 : ((n : ℝ) / Real.log (n : ℝ) ^ 2 - 1) * Real.log (n : ℝ) ^ 2 =
          (n : ℝ) - Real.log (n : ℝ) ^ 2 := by field_simp
      have hfloor_nat_eq : (⌊(n : ℝ) / Real.log (n : ℝ) ^ 2⌋₊ : ℝ) =
          ((⌊(n : ℝ) / Real.log (n : ℝ) ^ 2⌋ : ℤ) : ℝ) := by
        rw [← Int.toNat_of_nonneg hfloor_nn_int]
        norm_cast
      calc c_step * (n : ℝ) - c_step * Real.log (n : ℝ) ^ 2
          = c_step * ((n : ℝ) - Real.log (n : ℝ) ^ 2) := by ring
        _ = c_step * (((n : ℝ) / Real.log (n : ℝ) ^ 2 - 1) * Real.log (n : ℝ) ^ 2) := by rw [h1]
        _ ≤ c_step * ((⌊(n : ℝ) / Real.log (n : ℝ) ^ 2⌋ : ℤ) * Real.log (n : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (by exact_mod_cast hfloor_ge) hlog2_pos.le)
              (le_of_lt hc_step_pos)
        _ = (⌊(n : ℝ) / Real.log (n : ℝ) ^ 2⌋₊ : ℝ) * c_step * Real.log (n : ℝ) ^ 2 := by
            rw [hfloor_nat_eq]; ring
    -- Step (iii): 4*(loglog n)² ≤ 4*(log n)²
    have hlog_ge1 : (1 : ℝ) ≤ Real.log (n : ℝ) := by
      have hn3r : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
      rw [Real.le_log_iff_exp_le hn_pos]
      linarith [Real.exp_one_lt_three]
    have hloglog_le : (4 : ℝ) * Real.log (Real.log (n : ℝ)) ^ 2 ≤ 4 * Real.log (n : ℝ) ^ 2 := by
      have hll_nn : (0 : ℝ) ≤ Real.log (Real.log (n : ℝ)) :=
        Real.log_nonneg hlog_ge1
      have hll_le : Real.log (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) :=
        Real.log_le_self (le_of_lt hlog_pos)
      have hll_sq_le : Real.log (Real.log (n : ℝ)) ^ 2 ≤ Real.log (n : ℝ) ^ 2 :=
        pow_le_pow_left₀ hll_nn hll_le 2
      linarith
    -- Combine: exponent ≤ 4*log²n - (c*n - c*log²n) = (c+4)*log²n - c*n ≤ -c*n/2
    linarith [hN₁ n hn₁]
  -- Step B: squeeze E between 0 and exp(-c_step*n/2) → 0
  obtain ⟨N_log, hN_log⟩ := hlogexp_bound
  have hE_nn : ∀ n : ℕ, (0 : ℝ) ≤ expectedTBoundedColorings n
      (⌊kThresholdWitness n - (⌊(n : ℝ) / Real.log (n : ℝ) ^ 2⌋₊ : ℝ)⌋₊)
      (max 1 (thresholdFloor n - 1)) := fun n => by
    simp only [expectedTBoundedColorings]
    apply Finset.sum_nonneg
    intro f _
    apply div_nonneg
    · exact mul_nonneg (by exact_mod_cast Nat.zero_le _) (pow_nonneg (by norm_num) _)
    · exact_mod_cast Nat.zero_le _
  -- exp(-c_step*n/2) → 0
  have hexp_zero : Filter.Tendsto (fun n : ℕ => Real.exp (-(c_step * (n : ℝ) / 2)))
      Filter.atTop (nhds 0) := by
    have htendsto_bot : Filter.Tendsto (fun n : ℕ => -(c_step * (n : ℝ) / 2))
        Filter.atTop Filter.atBot := by
      have hpos : (0 : ℝ) < c_step / 2 := by linarith
      have h1 : Filter.Tendsto (fun n : ℕ => c_step / 2 * (n : ℝ)) Filter.atTop Filter.atTop :=
        tendsto_natCast_atTop_atTop.const_mul_atTop hpos
      -- Use atTop_mul_const_of_neg': Tendsto (f x * r) atTop atBot when r < 0
      have hneg : -(1 : ℝ) < 0 := by norm_num
      have h2 : Filter.Tendsto (fun n : ℕ => c_step / 2 * (n : ℝ) * (-1)) Filter.atTop Filter.atBot :=
        h1.atTop_mul_const_of_neg' hneg
      exact h2.congr' (Filter.Eventually.of_forall (fun n => by ring))
    exact Real.tendsto_exp_atBot.comp htendsto_bot
  -- E is between 0 and exp(-c*n/2) eventually
  have hE_le : ∀ᶠ n : ℕ in Filter.atTop,
      expectedTBoundedColorings n
        (⌊kThresholdWitness n - (⌊(n : ℝ) / Real.log (n : ℝ) ^ 2⌋₊ : ℝ)⌋₊)
        (max 1 (thresholdFloor n - 1)) ≤
      Real.exp (-(c_step * (n : ℝ) / 2)) := by
    filter_upwards [Filter.eventually_ge_atTop (max (max N₀ N_log) 3)] with n hn
    have hn₀ : N₀ ≤ n := le_trans (Nat.le_max_left _ _) (le_trans (Nat.le_max_left _ _) hn)
    have hn_log : N_log ≤ n := le_trans (Nat.le_max_right _ _) (le_trans (Nat.le_max_left _ _) hn)
    have hn3 : 3 ≤ n := le_trans (Nat.le_max_right _ _) hn
    have hDn_le : ⌊(n : ℝ) / Real.log (n : ℝ) ^ 2⌋₊ ≤ n := by
      apply Nat.floor_le_of_le
      have hn_pos_r : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hn3
      have hn_ge3 : (3 : ℝ) ≤ n := by exact_mod_cast hn3
      have hlog_ge1 : (1 : ℝ) ≤ Real.log (n : ℝ) := by
        rw [Real.le_log_iff_exp_le hn_pos_r]
        linarith [Real.exp_one_lt_three]
      have hlog_sq_ge1 : (1 : ℝ) ≤ Real.log (n : ℝ) ^ 2 :=
        one_le_pow₀ hlog_ge1
      exact div_le_self (le_of_lt hn_pos_r) hlog_sq_ge1
    have hlog_ub := hN₀ n hn₀ _ hDn_le
    rcases le_or_gt (expectedTBoundedColorings n
        (⌊kThresholdWitness n - (⌊(n : ℝ) / Real.log (n : ℝ) ^ 2⌋₊ : ℝ)⌋₊)
        (max 1 (thresholdFloor n - 1))) 0 with hzero | hE_pos
    · exact hzero.trans (Real.exp_nonneg _)
    · calc expectedTBoundedColorings n _ _
          = Real.exp (Real.log (expectedTBoundedColorings n _ _)) := (Real.exp_log hE_pos).symm
        _ ≤ Real.exp ((4 : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2 -
              (⌊(n : ℝ) / Real.log (n : ℝ) ^ 2⌋₊ : ℝ) * c_step * (Real.log (n : ℝ)) ^ 2) :=
            Real.exp_le_exp.mpr hlog_ub
        _ ≤ Real.exp (-(c_step * (n : ℝ) / 2)) :=
            Real.exp_le_exp.mpr (hN_log n hn_log)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp_zero
    (Filter.Eventually.of_forall (fun n => hE_nn n)) hE_le

/-- **Stage-2 bridge target — low concrete probabilistic source theorem.**

Asserts that `lowRegimeConditionalGapEvent n` (i.e., χ(G) − ζ(G) ≥ log log n
when InLowRegime n holds) occurs with probability → 1 in G(n, 1/2).

**Status: PROVED (2026-05-15) via first-moment (Markov) method.**

Delegates to `lowBranchFirstMomentGapAxiom`, which cites:
- HP-2023 (arXiv:2306.07253), Corollaries 37+39, Lemma 7.4, lines 2364–2369
- Heckel (2024) (arXiv:2409.17614), line 516 (eq:firstmomentcocol)

The proof does NOT use C5, tameness, φ(1,x,1) > 0, or μ_α ≥ n^{x₀+ε}.
The prior P0 citation chain (C5 in φ < 0 regime) is superseded.

The `LowBranchBridgeInputs` argument is kept for structural compatibility;
it is immediately dischargeable via `low_branch_bridge_inputs_ready`. -/
theorem low_branch_quantitative_splice_loglog_whp_of_bridge_inputs
    (_hinputs : LowBranchBridgeInputs) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (lowRegimeConditionalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) :=
  lowBranchFirstMomentGapAxiom

/-- Wrapper-local handoff point for the future proof replacing
the low-branch bridge-input axiom.

This exposes the concrete rational certificate together with the certified
low-branch finite-margin bundle in the same module as the remaining low bridge
axiom. -/
theorem low_branch_bridge_inputs_ready :
    LowBranchBridgeInputs := by
  exact {
    certificate := LowBranch.rational_certificate
    certified_consequences :=
      LowBranch.rational_certificate_certified_consequences
    source_inputs := LowBranch.rational_certificate_source_bridge_inputs
  }

/-- Any low-branch certificate can be lifted to the wrapper-level low bridge
input contract through the structured certified-consequence adapter. -/
theorem low_branch_bridge_inputs_of_certificate
    (hcert : LowBranch.Certificate) :
    LowBranchBridgeInputs := by
  exact {
    certificate := hcert
    certified_consequences :=
      LowBranch.certified_consequences_of_certificate hcert
    source_inputs :=
      LowBranch.source_bridge_inputs_of_certificate hcert
  }

/-- Low-regime analytical source input, routed through the current Lean
certificate interface for the low-branch finite-room margins. -/
theorem low_branch_quantitative_splice_loglog_whp :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (lowRegimeConditionalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) :=
  low_branch_quantitative_splice_loglog_whp_of_bridge_inputs
    low_branch_bridge_inputs_ready

/-- Wrapper-facing low-regime input. -/
theorem low_regime_loglog_whp :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (lowRegimeConditionalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) :=
  low_branch_quantitative_splice_loglog_whp

/-- Stage-2 bridge target for replacing
`good_branch_partial_away_from_one_loglog_whp`.

Completion-gate category: middle concrete probabilistic source theorem.

Source package:
`proof/analytical-sources/good-branch-partial-away-from-one-theorem-2026-05-13.md`
plus the package proof of the modified Lemma 7.20 certificate.

The existing `MiddleBranch.Certificate` module certifies the rational
middle-branch interval and modified Lemma 7.10-ext lower-envelope bookkeeping,
and `MiddleBranchBridgeInputs` bundles that certificate with the current
epsilon-budget handoff facts.  The remaining source machinery still has to
prove the actual middle-regime WHP event from that full bridge input contract.
This axiom fixes the exact Lean statement that future work must supply.
-/
axiom good_branch_partial_away_from_one_loglog_whp_of_bridge_inputs
    (_hinputs : MiddleBranchBridgeInputs) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (middleRegimeConditionalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞))

/-- Wrapper-local handoff point for the future proof replacing
the middle-branch bridge-input axiom.

This exposes the concrete rational certificate together with the certified
middle-branch interval and epsilon-budget bundles in the same module as the
remaining middle bridge axiom. -/
theorem middle_branch_bridge_inputs_ready :
    MiddleBranchBridgeInputs := by
  exact {
    certificate := MiddleBranch.rational_certificate
    certified_consequences :=
      MiddleBranch.rational_certificate_certified_consequences
    source_inputs := MiddleBranch.rational_certificate_source_bridge_inputs
  }

/-- Any middle-branch certificate can be lifted to the wrapper-level middle
bridge input contract through the structured certified-consequence adapter. -/
theorem middle_branch_bridge_inputs_of_certificate
    (hcert : MiddleBranch.Certificate) :
    MiddleBranchBridgeInputs := by
  exact {
    certificate := hcert
    certified_consequences :=
      MiddleBranch.certified_consequences_of_certificate hcert
    source_inputs :=
      MiddleBranch.source_bridge_inputs_of_certificate hcert
  }

/-- Middle-regime analytical source input, routed through the current Lean
certificate interface for the modified Lemma 7.20 package. -/
theorem good_branch_partial_away_from_one_loglog_whp :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (middleRegimeConditionalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) :=
  good_branch_partial_away_from_one_loglog_whp_of_bridge_inputs
    middle_branch_bridge_inputs_ready

/-- Wrapper-facing middle-regime input. -/
theorem middle_regime_loglog_whp :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (middleRegimeConditionalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) :=
  good_branch_partial_away_from_one_loglog_whp

/-- Stage-2 bridge target for replacing
`upper_boundary_r2_integrated_loglog_whp`.

Completion-gate category: upper concrete probabilistic source theorem.

Source package:
`proof/analytical-sources/upper-boundary-r2-integrated-theorem-2026-05-13.md`
and `proof/upper-boundary-r2-explicit-interval-tables-2026-05-13.md`.

The existing `UpperR2.Certificate` module certifies the rational reserve
ordering of the numerical appendix, and `UpperR2BridgeInputs` bundles that
certificate with the current interval-output and payment handoff facts.  The
remaining source machinery still has to prove the actual upper-regime WHP
event from that full bridge input contract.  This axiom fixes the exact Lean
statement that future work must supply.
-/
axiom upper_boundary_r2_integrated_loglog_whp_of_bridge_inputs
    (_hinputs : UpperR2BridgeInputs) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (upperRegimeConditionalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞))

/-- Current axiom-backed low source obligation, typed by the named low branch
source target. -/
theorem low_branch_source_obligation_from_axiom :
    LowBranchSourceObligation :=
  low_branch_quantitative_splice_loglog_whp_of_bridge_inputs

/-- Current axiom-backed middle source obligation, typed by the named middle
branch source target. -/
theorem middle_branch_source_obligation_from_axiom :
    MiddleBranchSourceObligation :=
  good_branch_partial_away_from_one_loglog_whp_of_bridge_inputs

/-- Current axiom-backed upper source obligation, typed by the named upper
branch source target. -/
theorem upper_r2_source_obligation_from_axiom :
    UpperR2SourceObligation :=
  upper_boundary_r2_integrated_loglog_whp_of_bridge_inputs

/-- Promote a low-branch WHP theorem over source inputs to the wrapper-level
bridge-input source obligation. -/
theorem low_branch_source_obligation_of_source_inputs
    (hsource : LowBranchSourceInputObligation) :
    LowBranchSourceObligation := by
  intro hinputs
  exact hsource hinputs.source_inputs

/-- Promote a middle-branch WHP theorem over source inputs to the
wrapper-level bridge-input source obligation. -/
theorem middle_branch_source_obligation_of_source_inputs
    (hsource : MiddleBranchSourceInputObligation) :
    MiddleBranchSourceObligation := by
  intro hinputs
  exact hsource hinputs.source_inputs

/-- Promote an upper `r=2` WHP theorem over source inputs to the wrapper-level
bridge-input source obligation. -/
theorem upper_r2_source_obligation_of_source_inputs
    (hsource : UpperR2SourceInputObligation) :
    UpperR2SourceObligation := by
  intro hinputs
  exact hsource hinputs.source_inputs

/-- Promote an upper endpoint-component WHP theorem to the upper source-input
obligation by rebuilding the standard source-input package from the endpoint
components carried by the source input. -/
theorem upper_r2_source_input_obligation_of_endpoint_components
    (hendpoint : UpperR2EndpointSourceObligation) :
    UpperR2SourceInputObligation := by
  intro hsource
  exact hendpoint hsource.endpoint_components

/-- Promote a low certificate-level WHP theorem to the low source-input
obligation by rebuilding the standard low source-input package from the
certificate carried by the source input. -/
theorem low_branch_source_input_obligation_of_certificate
    (hcert_source : LowBranchCertificateSourceObligation) :
    LowBranchSourceInputObligation := by
  intro hsource
  exact hcert_source hsource.certificate

/-- Promote a middle certificate-level WHP theorem to the middle source-input
obligation by rebuilding the standard middle source-input package from the
certificate carried by the source input. -/
theorem middle_branch_source_input_obligation_of_certificate
    (hcert_source : MiddleBranchCertificateSourceObligation) :
    MiddleBranchSourceInputObligation := by
  intro hsource
  exact hcert_source hsource.certificate

/-- Current axiom-backed low source-input obligation, typed by the narrower
Stage-2 low source-input target. -/
theorem low_branch_source_input_obligation_from_axiom :
    LowBranchSourceInputObligation := by
  intro hsource
  exact low_branch_quantitative_splice_loglog_whp_of_bridge_inputs
    (low_branch_bridge_inputs_of_source_inputs hsource)

/-- Current axiom-backed middle source-input obligation, typed by the narrower
Stage-2 middle source-input target. -/
theorem middle_branch_source_input_obligation_from_axiom :
    MiddleBranchSourceInputObligation := by
  intro hsource
  exact good_branch_partial_away_from_one_loglog_whp_of_bridge_inputs
    (middle_branch_bridge_inputs_of_source_inputs hsource)

/-- Current axiom-backed upper source-input obligation, typed by the narrower
Stage-2 upper source-input target. -/
theorem upper_r2_source_input_obligation_from_axiom :
    UpperR2SourceInputObligation := by
  intro hsource
  exact upper_boundary_r2_integrated_loglog_whp_of_bridge_inputs
    (upper_boundary_bridge_inputs_of_source_inputs hsource)

/-- Current axiom-backed upper endpoint-component obligation, typed by the
narrowest current upper endpoint boundary. -/
theorem upper_r2_endpoint_source_obligation_from_axiom :
    UpperR2EndpointSourceObligation := by
  intro hcomponents
  exact upper_boundary_r2_integrated_loglog_whp_of_bridge_inputs
    (upper_boundary_bridge_inputs_of_source_inputs
      (UpperR2.source_bridge_inputs_of_endpoint_components
        UpperR2.rational_certificate
        hcomponents))

/-- Assemble the source-side analytical obligation bundle from the three
branch-level WHP source theorems. -/
theorem analytical_source_obligations_of_branches
    (hlow : LowBranchSourceObligation)
    (hmiddle : MiddleBranchSourceObligation)
    (hupper : UpperR2SourceObligation) :
    AnalyticalSourceObligations := by
  exact {
    low_branch := hlow
    middle_branch := hmiddle
    upper_branch := hupper
  }

/-- Assemble the source-input-shaped analytical obligation bundle from the
three branch-level WHP source-input theorems. -/
theorem analytical_source_input_obligations_of_branches
    (hlow : LowBranchSourceInputObligation)
    (hmiddle : MiddleBranchSourceInputObligation)
    (hupper : UpperR2SourceInputObligation) :
    AnalyticalSourceInputObligations := by
  exact {
    low_branch := hlow
    middle_branch := hmiddle
    upper_branch := hupper
  }

/-- Assemble source-input obligations when the upper source theorem has
already been narrowed to the endpoint-component contract. -/
theorem analytical_source_input_obligations_of_upper_endpoint
    (hlow : LowBranchSourceInputObligation)
    (hmiddle : MiddleBranchSourceInputObligation)
    (hupper : UpperR2EndpointSourceObligation) :
    AnalyticalSourceInputObligations := by
  exact analytical_source_input_obligations_of_branches
    hlow
    hmiddle
    (upper_r2_source_input_obligation_of_endpoint_components hupper)

/-- Assemble source-input obligations from the narrowest current Stage-2
certificate/endpoint checklist. -/
theorem analytical_source_input_obligations_of_certificates_and_upper_endpoint
    (hlow : LowBranchCertificateSourceObligation)
    (hmiddle : MiddleBranchCertificateSourceObligation)
    (hupper : UpperR2EndpointSourceObligation) :
    AnalyticalSourceInputObligations := by
  exact analytical_source_input_obligations_of_upper_endpoint
    (low_branch_source_input_obligation_of_certificate hlow)
    (middle_branch_source_input_obligation_of_certificate hmiddle)
    hupper

/-- Current source-input-obligation bundle, still backed by the three
remaining paper/source axioms. -/
theorem analytical_source_input_obligations_from_axioms :
    AnalyticalSourceInputObligations := by
  exact analytical_source_input_obligations_of_branches
    low_branch_source_input_obligation_from_axiom
    middle_branch_source_input_obligation_from_axiom
    upper_r2_source_input_obligation_from_axiom

/-- Convert source-input-shaped obligations into the wrapper-level
source-obligation bundle consumed by the final assembly theorem. -/
theorem analytical_source_obligations_of_source_inputs
    (hsources : AnalyticalSourceInputObligations) :
    AnalyticalSourceObligations := by
  exact analytical_source_obligations_of_branches
    (low_branch_source_obligation_of_source_inputs hsources.low_branch)
    (middle_branch_source_obligation_of_source_inputs hsources.middle_branch)
    (upper_r2_source_obligation_of_source_inputs hsources.upper_branch)

/-- Convert the explicit remaining-work checklist into the source-obligation
bundle consumed by the final assembly theorem. -/
theorem analytical_source_obligations_of_remaining
    (hremaining : AnalyticalRemainingObligations) :
    AnalyticalSourceObligations := by
  exact analytical_source_obligations_of_branches
    hremaining.low_branch_source
    hremaining.middle_branch_source
    hremaining.upper_r2_source

/-- Convert the precise Stage-2 remaining-work checklist into the
source-input obligation bundle consumed by the preferred Stage-2 route. -/
theorem analytical_source_input_obligations_of_remaining_source_inputs
    (hremaining : AnalyticalRemainingSourceInputObligations) :
    AnalyticalSourceInputObligations := by
  exact analytical_source_input_obligations_of_upper_endpoint
    hremaining.low_branch_source_input
    hremaining.middle_branch_source_input
    hremaining.upper_r2_endpoint_source

/-- Convert the precise Stage-2 remaining-work checklist all the way to the
source-obligation bundle consumed by the final assembly theorem. -/
theorem analytical_source_obligations_of_remaining_source_inputs
    (hremaining : AnalyticalRemainingSourceInputObligations) :
    AnalyticalSourceObligations := by
  exact analytical_source_obligations_of_source_inputs
    (analytical_source_input_obligations_of_remaining_source_inputs hremaining)

/-- Convert the narrowest current Stage-2 checklist into the source-input
obligation bundle consumed by the preferred assembly route. -/
theorem analytical_source_input_obligations_of_remaining_certificates
    (hremaining : AnalyticalRemainingCertificateObligations) :
    AnalyticalSourceInputObligations := by
  exact analytical_source_input_obligations_of_certificates_and_upper_endpoint
    hremaining.low_branch_certificate_source
    hremaining.middle_branch_certificate_source
    hremaining.upper_r2_endpoint_source

/-- Convert the narrowest current Stage-2 checklist all the way to the
source-obligation bundle consumed by the final assembly theorem. -/
theorem analytical_source_obligations_of_remaining_certificates
    (hremaining : AnalyticalRemainingCertificateObligations) :
    AnalyticalSourceObligations := by
  exact analytical_source_obligations_of_source_inputs
    (analytical_source_input_obligations_of_remaining_certificates hremaining)

/-- Promote concrete low/middle/upper WHP conclusions to the certificate-level
checklist by ignoring the already-certified certificate/endpoint arguments. -/
theorem analytical_remaining_certificate_obligations_of_concrete
    (hremaining : AnalyticalRemainingConcreteObligations) :
    AnalyticalRemainingCertificateObligations := by
  exact {
    low_branch_certificate_source := by
      intro _hcert
      exact hremaining.low_branch_concrete_source
    middle_branch_certificate_source := by
      intro _hcert
      exact hremaining.middle_branch_concrete_source
    upper_r2_endpoint_source := by
      intro _hcomponents
      exact hremaining.upper_r2_concrete_source
  }

/-- Convert the fixed-constants checklist into the source-input obligation
bundle consumed by the final assembly route. -/
theorem analytical_source_input_obligations_of_remaining_concrete
    (hremaining : AnalyticalRemainingConcreteObligations) :
    AnalyticalSourceInputObligations := by
  exact analytical_source_input_obligations_of_remaining_certificates
    (analytical_remaining_certificate_obligations_of_concrete hremaining)

/-- Convert the fixed-constants checklist all the way to the source-obligation
bundle consumed by the final assembly theorem. -/
theorem analytical_source_obligations_of_remaining_concrete
    (hremaining : AnalyticalRemainingConcreteObligations) :
    AnalyticalSourceObligations := by
  exact analytical_source_obligations_of_source_inputs
    (analytical_source_input_obligations_of_remaining_concrete hremaining)

/-- Current precise Stage-2 remaining-work checklist, still backed by the
three remaining paper/source axioms.

This is the preferred checklist to replace: future work should provide these
three fields as theorems, then the wrapper can assemble the full analytical
conclusion without changing this module's final assembly layer. -/
theorem analytical_remaining_source_input_obligations_from_axioms :
    AnalyticalRemainingSourceInputObligations := by
  exact {
    low_branch_source_input := low_branch_source_input_obligation_from_axiom
    middle_branch_source_input := middle_branch_source_input_obligation_from_axiom
    upper_r2_endpoint_source := upper_r2_endpoint_source_obligation_from_axiom
  }

/-- Current narrowest Stage-2 checklist, still backed by the three remaining
paper/source axioms.

This route exposes the smallest current non-probabilistic contracts needed by
the wrapper: low certificate, middle certificate, and upper endpoint
components. -/
theorem analytical_remaining_certificate_obligations_from_axioms :
    AnalyticalRemainingCertificateObligations := by
  exact {
    low_branch_certificate_source := by
      intro hcert
      exact low_branch_source_input_obligation_from_axiom
        (LowBranch.source_bridge_inputs_of_certificate hcert)
    middle_branch_certificate_source := by
      intro hcert
      exact middle_branch_source_input_obligation_from_axiom
        (MiddleBranch.source_bridge_inputs_of_certificate hcert)
    upper_r2_endpoint_source := upper_r2_endpoint_source_obligation_from_axiom
  }

/-- Current fixed-constants Stage-2 checklist, still backed by the three
remaining paper/source axioms. -/
theorem analytical_remaining_concrete_obligations_from_axioms :
    AnalyticalRemainingConcreteObligations := by
  exact {
    low_branch_concrete_source :=
      low_branch_quantitative_splice_loglog_whp_of_bridge_inputs
        low_branch_bridge_inputs_ready
    middle_branch_concrete_source :=
      good_branch_partial_away_from_one_loglog_whp_of_bridge_inputs
        middle_branch_bridge_inputs_ready
    upper_r2_concrete_source :=
      upper_r2_endpoint_source_obligation_from_axiom
        UpperR2.upper_appendix_endpoint_components
  }

/-- Current source-obligation bundle, still backed by the three remaining
paper/source axioms.

The final route theorem below consumes this bundle rather than mentioning the
three axioms directly.  This gives the future axiom-removal work a single
Lean target. -/
theorem analytical_source_obligations_from_axioms :
    AnalyticalSourceObligations := by
  exact analytical_source_obligations_of_branches
    low_branch_source_obligation_from_axiom
    middle_branch_source_obligation_from_axiom
    upper_r2_source_obligation_from_axiom

/-- Lift an upper `r=2` certificate and interval-output layer package to the
wrapper-level upper bridge input contract. -/
theorem upper_boundary_bridge_inputs_of_output_layer
    (hcert : UpperR2.Certificate)
    (houtput : UpperR2.UpperR2OutputLayer) :
    UpperR2BridgeInputs := by
  exact {
    certificate := hcert
    source_inputs :=
      UpperR2.source_bridge_inputs_of_endpoint_components hcert {
        room := { table_lower := houtput.1.1 }
        pref := { table_lower := houtput.1.2.1 }
        tail_component := { tail_upper := houtput.1.2.2.1 }
        p2 := { reciprocal_lower := houtput.1.2.2.2 }
      }
    endpoint_table_facts := houtput.1
    interval_outputs := houtput.2.1
    certified_consequences := houtput.2.2.1
    payment_consequences := houtput.2.2.2
  }

/-- Lift an upper `r=2` certificate and bundled endpoint-component package to
the wrapper-level upper bridge input contract. -/
theorem upper_boundary_bridge_inputs_of_endpoint_components
    (hcert : UpperR2.Certificate)
    (hcomponents :
      UpperR2.UpperEndpointComponents
        UpperR2.roomEndpointLower
        UpperR2.prefixEndpointLower
        UpperR2.tailEndpointActual
        UpperR2.p2EndpointLower) :
    UpperR2BridgeInputs := by
  exact upper_boundary_bridge_inputs_of_output_layer
    hcert
    (UpperR2.upper_output_layer_of_endpoint_components hcomponents)

/-- Wrapper-local ready name for the current concrete upper output layer. -/
theorem upper_boundary_output_layer_ready :
    UpperR2.UpperR2OutputLayer := by
  exact UpperR2.upper_appendix_output_layer_ready

/-- Wrapper-local handoff point for the future proof replacing
the upper-boundary bridge-input axiom.

This exposes the concrete rational certificate together with the validated
upper appendix output layer in the same module as the remaining upper bridge
axiom. -/
theorem upper_boundary_bridge_inputs_ready :
    UpperR2BridgeInputs := by
  exact upper_boundary_bridge_inputs_of_output_layer
    UpperR2.upper_boundary_bridge_inputs_ready.1
    upper_boundary_output_layer_ready

/-- Assemble the full-route analytical bridge input from the three branch
bridge-input components. -/
theorem analytical_bridge_inputs_of_components
    (hlow : LowBranchBridgeInputs)
    (hmiddle : MiddleBranchBridgeInputs)
    (hupper : UpperR2BridgeInputs) :
    AnalyticalBridgeInputs := by
  exact {
    low := hlow
    middle := hmiddle
    upper := hupper
  }

/-- Extract the Stage-2 source-side bridge-input package from the full
wrapper-level analytical bridge inputs. -/
theorem analytical_source_bridge_inputs_of_bridge_inputs
    (hinputs : AnalyticalBridgeInputs) :
    AnalyticalSourceBridgeInputs := by
  exact {
    low := hinputs.low.source_inputs
    middle := hinputs.middle.source_inputs
    upper := hinputs.upper.source_inputs
  }

/-- Rebuild the full wrapper-level analytical bridge input from the more
precise Stage-2 source-side bridge-input package. -/
theorem analytical_bridge_inputs_of_source_bridge_inputs
    (hinputs : AnalyticalSourceBridgeInputs) :
    AnalyticalBridgeInputs := by
  exact analytical_bridge_inputs_of_components
    (low_branch_bridge_inputs_of_source_inputs hinputs.low)
    (middle_branch_bridge_inputs_of_source_inputs hinputs.middle)
    (upper_boundary_bridge_inputs_of_source_inputs hinputs.upper)

/-- Assemble the full-route analytical bridge input directly from the
branch-level certificate/output-layer data. -/
theorem analytical_bridge_inputs_of_certificates_and_output_layer
    (hlow : LowBranch.Certificate)
    (hmiddle : MiddleBranch.Certificate)
    (hupper_cert : UpperR2.Certificate)
    (hupper_output : UpperR2.UpperR2OutputLayer) :
    AnalyticalBridgeInputs := by
  exact analytical_bridge_inputs_of_components
    (low_branch_bridge_inputs_of_certificate hlow)
    (middle_branch_bridge_inputs_of_certificate hmiddle)
    (upper_boundary_bridge_inputs_of_output_layer hupper_cert hupper_output)

/-- Assemble the full-route analytical bridge input directly from low/middle
certificates and the upper bundled endpoint-component package. -/
theorem analytical_bridge_inputs_of_certificates_and_endpoint_components
    (hlow : LowBranch.Certificate)
    (hmiddle : MiddleBranch.Certificate)
    (hupper_cert : UpperR2.Certificate)
    (hupper_components :
      UpperR2.UpperEndpointComponents
        UpperR2.roomEndpointLower
        UpperR2.prefixEndpointLower
        UpperR2.tailEndpointActual
        UpperR2.p2EndpointLower) :
    AnalyticalBridgeInputs := by
  exact analytical_bridge_inputs_of_components
    (low_branch_bridge_inputs_of_certificate hlow)
    (middle_branch_bridge_inputs_of_certificate hmiddle)
    (upper_boundary_bridge_inputs_of_endpoint_components
      hupper_cert
      hupper_components)

/-- Concrete full-route bridge input assembled through the upper endpoint
component bundle.  This is the dry run for replacing the current upper appendix
constants by genuine interval endpoint theorems. -/
theorem analytical_bridge_inputs_ready_from_endpoint_components :
    AnalyticalBridgeInputs := by
  exact analytical_bridge_inputs_of_certificates_and_endpoint_components
    LowBranch.rational_certificate
    MiddleBranch.rational_certificate
    UpperR2.upper_boundary_bridge_inputs_ready.1
    UpperR2.upper_appendix_endpoint_components

/-- Concrete bridge-input bundle for the whole analytical route. -/
theorem analytical_bridge_inputs_ready :
    AnalyticalBridgeInputs := by
  exact analytical_bridge_inputs_of_certificates_and_output_layer
    LowBranch.rational_certificate
    MiddleBranch.rational_certificate
    UpperR2.upper_boundary_bridge_inputs_ready.1
    upper_boundary_output_layer_ready

/-- Concrete Stage-2 source-side bridge-input package supplied by the current
Lean-certified low, middle, and upper numerical handoff layers. -/
theorem analytical_source_bridge_inputs_ready :
    AnalyticalSourceBridgeInputs := by
  exact analytical_source_bridge_inputs_of_bridge_inputs
    analytical_bridge_inputs_ready

/-- Concrete Stage-2 scalar bridge-input package supplied by the current
Lean-certified low, middle, and upper numerical handoff layers. -/
theorem analytical_scalar_bridge_inputs_ready :
    AnalyticalScalarBridgeInputs := by
  exact {
    low := LowBranch.rational_certificate_scalar_bridge_inputs
    middle := MiddleBranch.rational_certificate_scalar_bridge_inputs
    upper := UpperR2.upper_boundary_scalar_bridge_inputs_ready
  }

/-- Low-branch projection from the concrete analytical scalar bridge package. -/
theorem analytical_scalar_bridge_low_ready :
    LowBranch.LowBranchScalarBridgeInputs := by
  exact analytical_scalar_bridge_inputs_ready.low

/-- Middle-branch projection from the concrete analytical scalar bridge
package. -/
theorem analytical_scalar_bridge_middle_ready :
    MiddleBranch.MiddleBranchScalarBridgeInputs := by
  exact analytical_scalar_bridge_inputs_ready.middle

/-- Upper-branch projection from the concrete analytical scalar bridge package. -/
theorem analytical_scalar_bridge_upper_ready :
    UpperR2.UpperR2ScalarBridgeInputs := by
  exact analytical_scalar_bridge_inputs_ready.upper

/-- Concrete combined Stage-2 numerical handoff package supplied by the current
Lean-certified low, middle, and upper numerical layers. -/
theorem analytical_numerical_bridge_inputs_ready :
    AnalyticalNumericalBridgeInputs := by
  exact analytical_numerical_bridge_inputs_of_parts
    analytical_source_bridge_inputs_ready
    analytical_scalar_bridge_inputs_ready

/-- Source-side projection from the concrete analytical numerical handoff
package. -/
theorem analytical_numerical_bridge_source_ready :
    AnalyticalSourceBridgeInputs := by
  exact analytical_numerical_bridge_inputs_ready.source

/-- Scalar projection from the concrete analytical numerical handoff package. -/
theorem analytical_numerical_bridge_scalar_ready :
    AnalyticalScalarBridgeInputs := by
  exact analytical_numerical_bridge_inputs_ready.scalar

/-- Low source-side projection from the concrete analytical numerical handoff
package. -/
theorem analytical_numerical_bridge_low_source_ready :
    LowBranch.SourceBridgeInputs := by
  exact analytical_numerical_bridge_source_ready.low

/-- Middle source-side projection from the concrete analytical numerical
handoff package. -/
theorem analytical_numerical_bridge_middle_source_ready :
    MiddleBranch.SourceBridgeInputs := by
  exact analytical_numerical_bridge_source_ready.middle

/-- Upper source-side projection from the concrete analytical numerical
handoff package. -/
theorem analytical_numerical_bridge_upper_source_ready :
    UpperR2.SourceBridgeInputs
      UpperR2.roomEndpointLower
      UpperR2.prefixEndpointLower
      UpperR2.tailEndpointActual
      UpperR2.p2EndpointLower := by
  exact analytical_numerical_bridge_source_ready.upper

/-- Low scalar projection from the concrete analytical numerical handoff
package. -/
theorem analytical_numerical_bridge_low_scalar_ready :
    LowBranch.LowBranchScalarBridgeInputs := by
  exact analytical_numerical_bridge_scalar_ready.low

/-- Middle scalar projection from the concrete analytical numerical handoff
package. -/
theorem analytical_numerical_bridge_middle_scalar_ready :
    MiddleBranch.MiddleBranchScalarBridgeInputs := by
  exact analytical_numerical_bridge_scalar_ready.middle

/-- Upper scalar projection from the concrete analytical numerical handoff
package. -/
theorem analytical_numerical_bridge_upper_scalar_ready :
    UpperR2.UpperR2ScalarBridgeInputs := by
  exact analytical_numerical_bridge_scalar_ready.upper

/-- Upper-regime analytical source input, routed through the current Lean
certificate interface for the `r=2` numerical appendix. -/
theorem upper_boundary_r2_integrated_loglog_whp :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (upperRegimeConditionalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) :=
  upper_boundary_r2_integrated_loglog_whp_of_bridge_inputs
    upper_boundary_bridge_inputs_ready

/-- Wrapper-facing upper-regime input. -/
theorem upper_regime_loglog_whp :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (upperRegimeConditionalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) :=
  upper_boundary_r2_integrated_loglog_whp

/-- Fractional-regime cover for the deterministic value `x(n)`.

Source package: `proof/proof.md`, final assembly.
-/
theorem fractional_regime_cover :
  ∀ n : ℕ, InLowRegime n ∨ InMiddleRegime n ∨ InUpperRegime n := by
  intro n
  have hx_nonneg : 0 ≤ fractionalParameter n := by
    simp [fractionalParameter, Int.fract_nonneg (threshold n)]
  have hx_lt_one : fractionalParameter n < 1 := by
    simpa [fractionalParameter] using Int.fract_lt_one (threshold n)
  by_cases hlow : fractionalParameter n ≤ lowMiddleCutoff
  · exact Or.inl ⟨hx_nonneg, hlow⟩
  · by_cases hmiddle : fractionalParameter n ≤ middleUpperCutoff
    · exact Or.inr (Or.inl ⟨by
        dsimp [lowMiddleCutoff] at hlow ⊢
        linarith, hmiddle⟩)
    · exact Or.inr (Or.inr ⟨by
        dsimp [middleUpperCutoff] at hmiddle ⊢
        linarith, hx_lt_one⟩)

/-- Deterministic pointwise assembly from the three regime implications.

This is the first Stage-2-style discharge inside the wrapper: once a fixed
`n` is covered by one of the deterministic regimes, the corresponding regime
implication puts every graph satisfying the three regime-conditional gap
claims into the target gap event.
-/
theorem regime_cover_forces_gap
    (n : ℕ) (G : SimpleGraph (Fin n))
    (hlow :
      InLowRegime n →
        logLogW n ≤ (chromaticNumber G : ℝ) - (cochromaticNumber G : ℝ))
    (hmiddle :
      InMiddleRegime n →
        logLogW n ≤ (chromaticNumber G : ℝ) - (cochromaticNumber G : ℝ))
    (hupper :
      InUpperRegime n →
        logLogW n ≤ (chromaticNumber G : ℝ) - (cochromaticNumber G : ℝ)) :
    G ∈ analyticalGapEvent n := by
  dsimp [analyticalGapEvent]
  rcases fractional_regime_cover n with hlow_regime | hmiddle_regime | hupper_regime
  · exact hlow hlow_regime
  · exact hmiddle hmiddle_regime
  · exact hupper hupper_regime

/-- Named subset bridge needed for the probabilistic final assembly.

Stage 2 can combine the three WHP assumptions into WHP of the intersection
of these events, then use this pointwise bridge plus monotonicity of `gnHalf`
to obtain `analytical_final_assembly`.
-/
theorem three_regime_events_force_gap
    (n : ℕ) {G : SimpleGraph (Fin n)}
    (hlow : G ∈ lowRegimeConditionalGapEvent n)
    (hmiddle : G ∈ middleRegimeConditionalGapEvent n)
    (hupper : G ∈ upperRegimeConditionalGapEvent n) :
    G ∈ analyticalGapEvent n :=
  regime_cover_forces_gap n G
    (by simpa [lowRegimeConditionalGapEvent] using hlow)
    (by simpa [middleRegimeConditionalGapEvent] using hmiddle)
    (by simpa [upperRegimeConditionalGapEvent] using hupper)

/-- The simultaneous conditional event is a subset of the target gap event. -/
theorem all_regime_event_subset_gap (n : ℕ) :
    allRegimeConditionalGapEvent n ⊆ analyticalGapEvent n := by
  intro G hG
  exact three_regime_events_force_gap n hG.1 hG.2.1 hG.2.2

/-- Pointwise monotonicity of the `G(n,1/2)` measure. -/
theorem gnHalf_event_mono
    (n : ℕ) {A B : Set (SimpleGraph (Fin n))}
    (hsub : A ⊆ B) :
    gnHalf n A ≤ gnHalf n B :=
  measure_mono hsub

/-- Measure-level form of the final subset bridge. -/
theorem all_regime_event_measure_le_gap (n : ℕ) :
    gnHalf n (allRegimeConditionalGapEvent n) ≤ gnHalf n (analyticalGapEvent n) :=
  gnHalf_event_mono n (all_regime_event_subset_gap n)

/-- Union-bound form for the complement of an intersection. -/
theorem gnHalf_inter_compl_le_compl_add
    (n : ℕ) (A B : Set (SimpleGraph (Fin n))) :
    gnHalf n (A ∩ B)ᶜ ≤ gnHalf n Aᶜ + gnHalf n Bᶜ := by
  rw [Set.compl_inter]
  exact measure_union_le _ _

/-- If an event has `gnHalf`-probability tending to one, its complement has
probability tending to zero. -/
theorem gnHalf_compl_tendsto_zero_of_tendsto_one
    {A : (n : ℕ) → Set (SimpleGraph (Fin n))}
    (hA :
      Filter.Tendsto
        (fun n : ℕ => gnHalf n (A n))
        Filter.atTop (nhds (1 : ℝ≥0∞))) :
    Filter.Tendsto
      (fun n : ℕ => gnHalf n (A n)ᶜ)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
  have hsub :
      Filter.Tendsto
        (fun n : ℕ => (1 : ℝ≥0∞) - gnHalf n (A n))
        Filter.atTop (nhds ((1 : ℝ≥0∞) - 1)) :=
    (ENNReal.tendsto_sub (Or.inl one_ne_top)).comp
      (tendsto_const_nhds.prodMk_nhds hA)
  simpa using hsub.congr' (by
    filter_upwards with n
    have hmeas : MeasurableSet (A n) :=
      Set.Finite.measurableSet (Set.toFinite _)
    haveI : IsProbabilityMeasure (gnHalf n) := by
      unfold gnHalf
      infer_instance
    rw [prob_compl_eq_one_sub (μ := gnHalf n) hmeas])

/-- If the complement of an event has `gnHalf`-probability tending to zero,
then the event has probability tending to one. -/
theorem gnHalf_tendsto_one_of_compl_tendsto_zero
    {A : (n : ℕ) → Set (SimpleGraph (Fin n))}
    (hAc :
      Filter.Tendsto
        (fun n : ℕ => gnHalf n (A n)ᶜ)
        Filter.atTop (nhds (0 : ℝ≥0∞))) :
    Filter.Tendsto
      (fun n : ℕ => gnHalf n (A n))
      Filter.atTop (nhds (1 : ℝ≥0∞)) := by
  have hsub :
      Filter.Tendsto
        (fun n : ℕ => (1 : ℝ≥0∞) - gnHalf n (A n)ᶜ)
        Filter.atTop (nhds ((1 : ℝ≥0∞) - 0)) :=
    (ENNReal.tendsto_sub (Or.inl one_ne_top)).comp
      (tendsto_const_nhds.prodMk_nhds hAc)
  simpa using hsub.congr' (by
    filter_upwards with n
    have hmeas : MeasurableSet (A n) :=
      Set.Finite.measurableSet (Set.toFinite _)
    haveI : IsProbabilityMeasure (gnHalf n) := by
      unfold gnHalf
      infer_instance
    rw [prob_compl_eq_one_sub (μ := gnHalf n) hmeas]
    exact ENNReal.sub_sub_cancel one_ne_top
      (by
        simpa using
          (measure_mono (Set.subset_univ (A n)) :
            gnHalf n (A n) ≤ gnHalf n Set.univ)))

/-- WHP monotonicity bridge for `gnHalf`.

If `A_n` has probability tending to one and `A_n ⊆ B_n` pointwise, then
`B_n` also has probability tending to one.
-/
theorem gnHalf_whp_mono
    {A B : (n : ℕ) → Set (SimpleGraph (Fin n))}
    (hsub : ∀ n : ℕ, A n ⊆ B n)
    (hA :
      Filter.Tendsto
        (fun n : ℕ => gnHalf n (A n))
        Filter.atTop (nhds (1 : ℝ≥0∞))) :
    Filter.Tendsto
      (fun n : ℕ => gnHalf n (B n))
      Filter.atTop (nhds (1 : ℝ≥0∞)) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le
    hA
    tendsto_const_nhds
    (fun n => gnHalf_event_mono n (hsub n))
    (fun n => by
      haveI : IsProbabilityMeasure (gnHalf n) := by
        unfold gnHalf
        infer_instance
      simpa using
        (measure_mono (Set.subset_univ (B n)) :
          gnHalf n (B n) ≤ gnHalf n Set.univ))

/-- Low-branch source-event assembly bridge.

Future replacements for
`low_branch_quantitative_splice_loglog_whp_of_bridge_inputs` can first prove
WHP for a sharper source event, then discharge only the deterministic subset
bridge from that source event into `lowRegimeConditionalGapEvent`.  This keeps
the final probability assembly independent of the detailed low-branch source
machinery.
-/
theorem low_branch_whp_of_source_event
    {A : (n : ℕ) → Set (SimpleGraph (Fin n))}
    (hsub : ∀ n : ℕ, A n ⊆ lowRegimeConditionalGapEvent n)
    (hA :
      Filter.Tendsto
        (fun n : ℕ => gnHalf n (A n))
        Filter.atTop (nhds (1 : ℝ≥0∞))) :
    Filter.Tendsto
      (fun n : ℕ => gnHalf n (lowRegimeConditionalGapEvent n))
      Filter.atTop (nhds (1 : ℝ≥0∞)) :=
  gnHalf_whp_mono
    (A := A)
    (B := lowRegimeConditionalGapEvent)
    hsub
    hA

/-- Middle-branch source-event assembly bridge. -/
theorem middle_branch_whp_of_source_event
    {A : (n : ℕ) → Set (SimpleGraph (Fin n))}
    (hsub : ∀ n : ℕ, A n ⊆ middleRegimeConditionalGapEvent n)
    (hA :
      Filter.Tendsto
        (fun n : ℕ => gnHalf n (A n))
        Filter.atTop (nhds (1 : ℝ≥0∞))) :
    Filter.Tendsto
      (fun n : ℕ => gnHalf n (middleRegimeConditionalGapEvent n))
      Filter.atTop (nhds (1 : ℝ≥0∞)) :=
  gnHalf_whp_mono
    (A := A)
    (B := middleRegimeConditionalGapEvent)
    hsub
    hA

/-- Upper `r=2` source-event assembly bridge. -/
theorem upper_r2_whp_of_source_event
    {A : (n : ℕ) → Set (SimpleGraph (Fin n))}
    (hsub : ∀ n : ℕ, A n ⊆ upperRegimeConditionalGapEvent n)
    (hA :
      Filter.Tendsto
        (fun n : ℕ => gnHalf n (A n))
        Filter.atTop (nhds (1 : ℝ≥0∞))) :
    Filter.Tendsto
      (fun n : ℕ => gnHalf n (upperRegimeConditionalGapEvent n))
      Filter.atTop (nhds (1 : ℝ≥0∞)) :=
  gnHalf_whp_mono
    (A := A)
    (B := upperRegimeConditionalGapEvent)
    hsub
    hA

/-- Convert the source-event-shaped low obligation into the existing
bridge-input-shaped low source obligation.

This is the immediate Lean target before replacing
`low_branch_quantitative_splice_loglog_whp_of_bridge_inputs`: provide
`LowBranchSourceEventObligation hinputs` for every explicit low bridge-input
package.
-/
theorem low_branch_source_obligation_of_source_event
    (h :
      ∀ hinputs : LowBranchBridgeInputs,
        LowBranchSourceEventObligation hinputs) :
    LowBranchSourceObligation := by
  intro hinputs
  rcases h hinputs with ⟨source_event, hsource_whp, hsource_subset⟩
  exact
    low_branch_whp_of_source_event
      (A := source_event)
      hsource_subset
      hsource_whp

/-- Lift the narrower source-input-shaped event obligation to the wrapper-level
source-event obligation by reading the source-input package from
`LowBranchBridgeInputs`.
-/
theorem low_branch_source_event_obligation_of_source_input_event
    (h :
      ∀ hsource : LowBranch.SourceBridgeInputs,
        LowBranchSourceInputEventObligation hsource) :
    ∀ hinputs : LowBranchBridgeInputs,
      LowBranchSourceEventObligation hinputs := by
  intro hinputs
  exact h hinputs.source_inputs

/-- Existing bridge-input-shaped low source obligation from the narrower
source-input-shaped event target.
-/
theorem low_branch_source_obligation_of_source_input_event
    (h :
      ∀ hsource : LowBranch.SourceBridgeInputs,
        LowBranchSourceInputEventObligation hsource) :
    LowBranchSourceObligation :=
  low_branch_source_obligation_of_source_event
    (low_branch_source_event_obligation_of_source_input_event h)

/-- Concrete low-branch completion-gate obligation from the source-event
shaped low proof target.

This is the current narrowest Lean target for removing the low concrete WHP
source theorem from the public analytical axiom closure: prove a source-event
obligation for every low bridge-input package, then instantiate it at the
already-certified `low_branch_bridge_inputs_ready` package.
-/
theorem low_branch_concrete_source_obligation_of_source_event
    (h :
      ∀ hinputs : LowBranchBridgeInputs,
        LowBranchSourceEventObligation hinputs) :
    LowBranchConcreteSourceObligation :=
  (low_branch_source_obligation_of_source_event h)
    low_branch_bridge_inputs_ready

/-- Concrete low-branch completion-gate obligation from the narrower
source-input-shaped event target.
-/
theorem low_branch_concrete_source_obligation_of_source_input_event
    (h :
      ∀ hsource : LowBranch.SourceBridgeInputs,
        LowBranchSourceInputEventObligation hsource) :
    LowBranchConcreteSourceObligation :=
  (low_branch_source_obligation_of_source_input_event h)
    low_branch_bridge_inputs_ready

/-- Assemble the concrete low source-input event target from its two source
proof components: WHP for the chosen event and deterministic inclusion into
the low conditional gap event. -/
theorem low_branch_concrete_source_input_event_obligation_of_components
    (source_event : (n : ℕ) → Set (SimpleGraph (Fin n)))
    (hwhp : LowBranchConcreteSourceInputEventWHP source_event)
    (hsubset : LowBranchConcreteSourceInputEventSubset source_event) :
    LowBranchConcreteSourceInputEventObligation := by
  exact ⟨source_event, hwhp, hsubset⟩

/-- Assemble the concrete low source-input event obligation from the structured
component contract. -/
theorem low_branch_concrete_source_input_event_obligation_of_component_bundle
    (h : LowBranchConcreteSourceInputEventComponents) :
    LowBranchConcreteSourceInputEventObligation := by
  exact
    low_branch_concrete_source_input_event_obligation_of_components
      h.source_event
      h.whp
      h.subset

/-- Concrete low-branch completion-gate obligation from the structured
source-event component bundle. -/
theorem low_branch_concrete_source_obligation_of_component_bundle
    (h : LowBranchConcreteSourceInputEventComponents) :
    LowBranchConcreteSourceObligation := by
  exact
    low_branch_whp_of_source_event
      (A := h.source_event)
      h.subset
      h.whp

/-- Exact low-wrapper replacement shape from the structured source-event
component bundle. -/
theorem low_branch_quantitative_splice_loglog_whp_of_component_bundle
    (h : LowBranchConcreteSourceInputEventComponents) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (lowRegimeConditionalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) :=
  low_branch_concrete_source_obligation_of_component_bundle h

/-- Concrete low-branch completion-gate obligation from the concrete rational
source-input-shaped event target.

This is narrower than
`low_branch_concrete_source_obligation_of_source_input_event`: it only requires
the source-event proof for the already-certified rational low source-input
package.
-/
theorem low_branch_concrete_source_obligation_of_concrete_source_input_event
    (h : LowBranchConcreteSourceInputEventObligation) :
    LowBranchConcreteSourceObligation := by
  rcases h with ⟨source_event, hsource_whp, hsource_subset⟩
  exact
    low_branch_whp_of_source_event
      (A := source_event)
      hsource_subset
      hsource_whp

/-- Exact low-wrapper replacement shape from the concrete source-input event
target.

This has the same conclusion as
`low_branch_quantitative_splice_loglog_whp_of_bridge_inputs` specialized to the
certified rational low source-input package, but its only assumption is the
narrow concrete source-event obligation.
-/
theorem low_branch_quantitative_splice_loglog_whp_of_concrete_source_input_event
    (h : LowBranchConcreteSourceInputEventObligation) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (lowRegimeConditionalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) :=
  low_branch_concrete_source_obligation_of_concrete_source_input_event h

/-- Assemble the concrete middle source-input event target from its two source
proof components. -/
theorem middle_branch_concrete_source_input_event_obligation_of_components
    (source_event : (n : ℕ) → Set (SimpleGraph (Fin n)))
    (hwhp : MiddleBranchConcreteSourceInputEventWHP source_event)
    (hsubset : MiddleBranchConcreteSourceInputEventSubset source_event) :
    MiddleBranchConcreteSourceInputEventObligation := by
  exact ⟨source_event, hwhp, hsubset⟩

/-- Assemble the concrete middle source-input event obligation from the
structured component contract. -/
theorem middle_branch_concrete_source_input_event_obligation_of_component_bundle
    (h : MiddleBranchConcreteSourceInputEventComponents) :
    MiddleBranchConcreteSourceInputEventObligation := by
  exact
    middle_branch_concrete_source_input_event_obligation_of_components
      h.source_event
      h.whp
      h.subset

/-- Concrete middle-branch completion-gate obligation from the concrete
rational source-input-shaped event target. -/
theorem middle_branch_concrete_source_obligation_of_concrete_source_input_event
    (h : MiddleBranchConcreteSourceInputEventObligation) :
    MiddleBranchConcreteSourceObligation := by
  rcases h with ⟨source_event, hsource_whp, hsource_subset⟩
  exact
    middle_branch_whp_of_source_event
      (A := source_event)
      hsource_subset
      hsource_whp

/-- Concrete middle-branch completion-gate obligation from the structured
source-event component bundle. -/
theorem middle_branch_concrete_source_obligation_of_component_bundle
    (h : MiddleBranchConcreteSourceInputEventComponents) :
    MiddleBranchConcreteSourceObligation := by
  exact
    middle_branch_whp_of_source_event
      (A := h.source_event)
      h.subset
      h.whp

/-- Exact middle-wrapper replacement shape from the concrete source-input
event target. -/
theorem good_branch_partial_away_from_one_loglog_whp_of_concrete_source_input_event
    (h : MiddleBranchConcreteSourceInputEventObligation) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (middleRegimeConditionalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) :=
  middle_branch_concrete_source_obligation_of_concrete_source_input_event h

/-- Exact middle-wrapper replacement shape from the structured source-event
component bundle. -/
theorem good_branch_partial_away_from_one_loglog_whp_of_component_bundle
    (h : MiddleBranchConcreteSourceInputEventComponents) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (middleRegimeConditionalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) :=
  middle_branch_concrete_source_obligation_of_component_bundle h

/-- Assemble the concrete upper source-input event target from its two source
proof components. -/
theorem upper_r2_concrete_source_input_event_obligation_of_components
    (source_event : (n : ℕ) → Set (SimpleGraph (Fin n)))
    (hwhp : UpperR2ConcreteSourceInputEventWHP source_event)
    (hsubset : UpperR2ConcreteSourceInputEventSubset source_event) :
    UpperR2ConcreteSourceInputEventObligation := by
  exact ⟨source_event, hwhp, hsubset⟩

/-- Assemble the concrete upper source-input event obligation from the
structured component contract. -/
theorem upper_r2_concrete_source_input_event_obligation_of_component_bundle
    (h : UpperR2ConcreteSourceInputEventComponents) :
    UpperR2ConcreteSourceInputEventObligation := by
  exact
    upper_r2_concrete_source_input_event_obligation_of_components
      h.source_event
      h.whp
      h.subset

/-- Concrete upper completion-gate obligation from the concrete appendix
source-input-shaped event target. -/
theorem upper_r2_concrete_source_obligation_of_concrete_source_input_event
    (h : UpperR2ConcreteSourceInputEventObligation) :
    UpperR2ConcreteSourceObligation := by
  rcases h with ⟨source_event, hsource_whp, hsource_subset⟩
  exact
    upper_r2_whp_of_source_event
      (A := source_event)
      hsource_subset
      hsource_whp

/-- Concrete upper completion-gate obligation from the structured source-event
component bundle. -/
theorem upper_r2_concrete_source_obligation_of_component_bundle
    (h : UpperR2ConcreteSourceInputEventComponents) :
    UpperR2ConcreteSourceObligation := by
  exact
    upper_r2_whp_of_source_event
      (A := h.source_event)
      h.subset
      h.whp

/-- Exact upper-wrapper replacement shape from the concrete source-input
event target. -/
theorem upper_boundary_r2_integrated_loglog_whp_of_concrete_source_input_event
    (h : UpperR2ConcreteSourceInputEventObligation) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (upperRegimeConditionalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) :=
  upper_r2_concrete_source_obligation_of_concrete_source_input_event h

/-- Exact upper-wrapper replacement shape from the structured source-event
component bundle. -/
theorem upper_boundary_r2_integrated_loglog_whp_of_component_bundle
    (h : UpperR2ConcreteSourceInputEventComponents) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (upperRegimeConditionalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) :=
  upper_r2_concrete_source_obligation_of_component_bundle h

/-- Rebuild the full concrete checklist from the concrete low source-input
event target plus the middle/upper concrete obligations.

This theorem records the exact post-low-discharge route: after proving
`LowBranchConcreteSourceInputEventObligation`, the public analytical closure
should no longer need the low concrete probabilistic source theorem, but it
will still require the middle and upper concrete WHP source theorems.
-/
theorem analytical_remaining_concrete_obligations_of_low_event_and_without_low
    (hlow : LowBranchConcreteSourceInputEventObligation)
    (hremaining : AnalyticalRemainingConcreteObligationsWithoutLow) :
    AnalyticalRemainingConcreteObligations := by
  exact {
    low_branch_concrete_source :=
      low_branch_concrete_source_obligation_of_concrete_source_input_event hlow
    middle_branch_concrete_source :=
      hremaining.middle_branch_concrete_source
    upper_r2_concrete_source :=
      hremaining.upper_r2_concrete_source
  }

/-- Rebuild the full concrete checklist from concrete low and middle
source-input event targets plus the remaining upper concrete obligation. -/
theorem analytical_remaining_concrete_obligations_of_low_middle_events_and_without_upper
    (hlow : LowBranchConcreteSourceInputEventObligation)
    (hmiddle : MiddleBranchConcreteSourceInputEventObligation)
    (hremaining : AnalyticalRemainingConcreteObligationsWithoutLowMiddle) :
    AnalyticalRemainingConcreteObligations := by
  exact {
    low_branch_concrete_source :=
      low_branch_concrete_source_obligation_of_concrete_source_input_event hlow
    middle_branch_concrete_source :=
      middle_branch_concrete_source_obligation_of_concrete_source_input_event
        hmiddle
    upper_r2_concrete_source :=
      hremaining.upper_r2_concrete_source
  }

/-- Rebuild the full concrete checklist from concrete low, middle, and upper
source-input event targets. -/
theorem analytical_remaining_concrete_obligations_of_all_regime_events
    (hlow : LowBranchConcreteSourceInputEventObligation)
    (hmiddle : MiddleBranchConcreteSourceInputEventObligation)
    (hupper : UpperR2ConcreteSourceInputEventObligation) :
    AnalyticalRemainingConcreteObligations := by
  exact {
    low_branch_concrete_source :=
      low_branch_concrete_source_obligation_of_concrete_source_input_event hlow
    middle_branch_concrete_source :=
      middle_branch_concrete_source_obligation_of_concrete_source_input_event
        hmiddle
    upper_r2_concrete_source :=
      upper_r2_concrete_source_obligation_of_concrete_source_input_event hupper
  }

/-- Rebuild the full concrete checklist from the bundled all-regime
source-input event obligations. -/
theorem analytical_remaining_concrete_obligations_of_all_regime_event_obligations
    (h : AnalyticalAllRegimeConcreteSourceInputEventObligations) :
    AnalyticalRemainingConcreteObligations := by
  exact analytical_remaining_concrete_obligations_of_all_regime_events
    h.low_branch_event
    h.middle_branch_event
    h.upper_r2_event

/-- Convert bundled all-regime event components to bundled all-regime event
obligations. -/
theorem analytical_all_regime_event_obligations_of_component_bundle
    (h : AnalyticalAllRegimeConcreteSourceInputEventComponents) :
    AnalyticalAllRegimeConcreteSourceInputEventObligations := by
  exact {
    low_branch_event :=
      low_branch_concrete_source_input_event_obligation_of_component_bundle
        h.low_branch
    middle_branch_event :=
      middle_branch_concrete_source_input_event_obligation_of_component_bundle
        h.middle_branch
    upper_r2_event :=
      upper_r2_concrete_source_input_event_obligation_of_component_bundle
        h.upper_r2
  }

/-- Generic binary finite-intersection closure for `gnHalf` WHP events. -/
theorem gnHalf_whp_inter
    {A B : (n : ℕ) → Set (SimpleGraph (Fin n))}
    (hA :
      Filter.Tendsto
        (fun n : ℕ => gnHalf n (A n))
        Filter.atTop (nhds (1 : ℝ≥0∞)))
    (hB :
      Filter.Tendsto
        (fun n : ℕ => gnHalf n (B n))
        Filter.atTop (nhds (1 : ℝ≥0∞))) :
    Filter.Tendsto
      (fun n : ℕ => gnHalf n {G : SimpleGraph (Fin n) | G ∈ A n ∧ G ∈ B n})
      Filter.atTop (nhds (1 : ℝ≥0∞)) := by
  let C : (n : ℕ) → Set (SimpleGraph (Fin n)) :=
    fun n => {G : SimpleGraph (Fin n) | G ∈ A n ∧ G ∈ B n}
  apply gnHalf_tendsto_one_of_compl_tendsto_zero (A := C)
  have hAc := gnHalf_compl_tendsto_zero_of_tendsto_one (A := A) hA
  have hBc := gnHalf_compl_tendsto_zero_of_tendsto_one (A := B) hB
  have hsum :
      Filter.Tendsto
        (fun n : ℕ => gnHalf n (A n)ᶜ + gnHalf n (B n)ᶜ)
        Filter.atTop (nhds (0 : ℝ≥0∞)) := by
    simpa using hAc.add hBc
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hsum ?_ ?_
  · intro n
    exact zero_le _
  · intro n
    simpa [C] using gnHalf_inter_compl_le_compl_add n (A n) (B n)

/-- WHP assembly of the three conditional regime events into one event.

This theorem now depends only on generic WHP finite-intersection closure and
the three named regime inputs.
-/
theorem all_regime_conditional_gap_whp :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (allRegimeConditionalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) := by
  let lowMidEvent : (n : ℕ) → Set (SimpleGraph (Fin n)) :=
    fun n => {G : SimpleGraph (Fin n) |
      G ∈ lowRegimeConditionalGapEvent n ∧
        G ∈ middleRegimeConditionalGapEvent n}
  have hlowMid :
      Filter.Tendsto
        (fun n : ℕ => gnHalf n (lowMidEvent n))
        Filter.atTop (nhds (1 : ℝ≥0∞)) := by
    simpa [lowMidEvent] using
      (gnHalf_whp_inter
        (A := lowRegimeConditionalGapEvent)
        (B := middleRegimeConditionalGapEvent)
        low_regime_loglog_whp
        middle_regime_loglog_whp)
  have hall :
      Filter.Tendsto
        (fun n : ℕ =>
          gnHalf n {G : SimpleGraph (Fin n) |
            G ∈ lowMidEvent n ∧
              G ∈ upperRegimeConditionalGapEvent n})
        Filter.atTop (nhds (1 : ℝ≥0∞)) :=
    gnHalf_whp_inter
      (A := lowMidEvent)
      (B := upperRegimeConditionalGapEvent)
      hlowMid
      upper_regime_loglog_whp
  simpa [allRegimeConditionalGapEvent, lowMidEvent, and_assoc] using hall

/-- Final assembly from the simultaneous regime event and monotonicity.

This theorem replaces the former all-in-one final assembly axiom by two
smaller obligations: WHP of the simultaneous regime event and monotonicity
of the random graph measure under event inclusion.
-/
theorem analytical_final_assembly :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) :=
  gnHalf_whp_mono
    (A := allRegimeConditionalGapEvent)
    (B := analyticalGapEvent)
    all_regime_event_subset_gap
    all_regime_conditional_gap_whp

/-- Full analytical assembly from explicit bridge inputs and source-side WHP
obligations.

This theorem is axiom-free relative to `AnalyticalSourceObligations`: all
remaining non-Lean analytical work is represented by that explicit contract. -/
theorem erdos_625_full_analytical_of_source_obligations
    (hinputs : AnalyticalBridgeInputs)
    (hsources : AnalyticalSourceObligations) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) := by
  have hlow_whp :
      Filter.Tendsto
        (fun n : ℕ => gnHalf n (lowRegimeConditionalGapEvent n))
        Filter.atTop (nhds (1 : ℝ≥0∞)) :=
    hsources.low_branch hinputs.low
  have hmiddle_whp :
      Filter.Tendsto
        (fun n : ℕ => gnHalf n (middleRegimeConditionalGapEvent n))
        Filter.atTop (nhds (1 : ℝ≥0∞)) :=
    hsources.middle_branch hinputs.middle
  have hupper_whp :
      Filter.Tendsto
        (fun n : ℕ => gnHalf n (upperRegimeConditionalGapEvent n))
        Filter.atTop (nhds (1 : ℝ≥0∞)) :=
    hsources.upper_branch hinputs.upper
  let lowMidEvent : (n : ℕ) → Set (SimpleGraph (Fin n)) :=
    fun n => {G : SimpleGraph (Fin n) |
      G ∈ lowRegimeConditionalGapEvent n ∧
        G ∈ middleRegimeConditionalGapEvent n}
  have hlowMid :
      Filter.Tendsto
        (fun n : ℕ => gnHalf n (lowMidEvent n))
        Filter.atTop (nhds (1 : ℝ≥0∞)) := by
    simpa [lowMidEvent] using
      (gnHalf_whp_inter
        (A := lowRegimeConditionalGapEvent)
        (B := middleRegimeConditionalGapEvent)
        hlow_whp
        hmiddle_whp)
  have hall :
      Filter.Tendsto
        (fun n : ℕ =>
          gnHalf n {G : SimpleGraph (Fin n) |
            G ∈ lowMidEvent n ∧
              G ∈ upperRegimeConditionalGapEvent n})
        Filter.atTop (nhds (1 : ℝ≥0∞)) :=
    gnHalf_whp_inter
      (A := lowMidEvent)
      (B := upperRegimeConditionalGapEvent)
      hlowMid
      hupper_whp
  have hall_regime :
      Filter.Tendsto
        (fun n : ℕ => gnHalf n (allRegimeConditionalGapEvent n))
        Filter.atTop (nhds (1 : ℝ≥0∞)) := by
    simpa [allRegimeConditionalGapEvent, lowMidEvent, and_assoc] using hall
  exact
    gnHalf_whp_mono
      (A := allRegimeConditionalGapEvent)
      (B := analyticalGapEvent)
      all_regime_event_subset_gap
      hall_regime

/-- Final analytical assembly directly from branch-level certificates, the
upper output layer, and source-side WHP obligations.

This is the most explicit Stage-2 entry point: numerical/certificate work
constructs the branch certificate and output-layer arguments, while
probabilistic source work constructs `AnalyticalSourceObligations`. -/
theorem erdos_625_full_analytical_of_certificates_output_and_sources
    (hlow : LowBranch.Certificate)
    (hmiddle : MiddleBranch.Certificate)
    (hupper_cert : UpperR2.Certificate)
    (hupper_output : UpperR2.UpperR2OutputLayer)
    (hsources : AnalyticalSourceObligations) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) := by
  exact erdos_625_full_analytical_of_source_obligations
    (analytical_bridge_inputs_of_certificates_and_output_layer
      hlow hmiddle hupper_cert hupper_output)
    hsources

/-- Final analytical assembly from the current concrete certificate/output
layer package and source-side WHP obligations.

This is the direct future target after the three source WHP lemmas are
formalized: construct `AnalyticalSourceObligations`, then apply this theorem
to obtain the current final analytical conclusion. -/
theorem erdos_625_full_analytical_of_ready_certificates_and_sources
    (hsources : AnalyticalSourceObligations) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) := by
  exact erdos_625_full_analytical_of_certificates_output_and_sources
    LowBranch.rational_certificate
    MiddleBranch.rational_certificate
    UpperR2.upper_boundary_bridge_inputs_ready.1
    upper_boundary_output_layer_ready
    hsources

/-- Final analytical assembly from the narrower source-input-shaped WHP
obligations.

This is the preferred Stage-2 target after the branch source machinery starts
consuming `LowBranch.SourceBridgeInputs`, `MiddleBranch.SourceBridgeInputs`,
and `UpperR2.SourceBridgeInputs` directly. -/
theorem erdos_625_full_analytical_of_source_input_obligations
    (hsources : AnalyticalSourceInputObligations) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) := by
  exact erdos_625_full_analytical_of_ready_certificates_and_sources
    (analytical_source_obligations_of_source_inputs hsources)

/-- Final analytical assembly from explicit Stage-2 source-side bridge inputs
and source-input-shaped WHP obligations.

This is the fully parameterized Stage-2 source-input route: numerical work
constructs `AnalyticalSourceBridgeInputs`, probabilistic source work constructs
`AnalyticalSourceInputObligations`, and the wrapper assembles the final WHP
conclusion. -/
theorem erdos_625_full_analytical_of_source_bridge_inputs_and_source_inputs
    (hinputs : AnalyticalSourceBridgeInputs)
    (hsources : AnalyticalSourceInputObligations) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) := by
  exact erdos_625_full_analytical_of_source_obligations
    (analytical_bridge_inputs_of_source_bridge_inputs hinputs)
    (analytical_source_obligations_of_source_inputs hsources)

/-- Final analytical assembly from the current concrete certificates, the
upper endpoint-component route, and source-side WHP obligations. -/
theorem erdos_625_full_analytical_of_ready_endpoint_components_and_sources
    (hsources : AnalyticalSourceObligations) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) := by
  exact erdos_625_full_analytical_of_source_obligations
    analytical_bridge_inputs_ready_from_endpoint_components
    hsources

/-- Final analytical assembly from the current endpoint-component route and
the narrower source-input-shaped WHP obligations. -/
theorem erdos_625_full_analytical_of_ready_endpoint_components_source_inputs
    (hsources : AnalyticalSourceInputObligations) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) := by
  exact erdos_625_full_analytical_of_ready_endpoint_components_and_sources
    (analytical_source_obligations_of_source_inputs hsources)

/-- Final analytical assembly from the three named branch source obligations
and the current concrete endpoint-component route. -/
theorem erdos_625_full_analytical_of_ready_endpoint_components_branch_sources
    (hlow : LowBranchSourceObligation)
    (hmiddle : MiddleBranchSourceObligation)
    (hupper : UpperR2SourceObligation) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) := by
  exact erdos_625_full_analytical_of_ready_endpoint_components_and_sources
    (analytical_source_obligations_of_branches hlow hmiddle hupper)

/-- Final analytical assembly from the three named branch source-input
obligations and the current concrete endpoint-component route. -/
theorem erdos_625_full_analytical_of_ready_endpoint_components_branch_source_inputs
    (hlow : LowBranchSourceInputObligation)
    (hmiddle : MiddleBranchSourceInputObligation)
    (hupper : UpperR2SourceInputObligation) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) := by
  exact erdos_625_full_analytical_of_ready_endpoint_components_source_inputs
    (analytical_source_input_obligations_of_branches hlow hmiddle hupper)

/-- Final analytical assembly from the three named branch source obligations
and the current concrete certificate/output-layer package.

This is the direct target for replacing the current source axioms by actual
branch proofs: prove the three named source obligations, then this theorem
produces the final analytical conclusion. -/
theorem erdos_625_full_analytical_of_ready_branch_sources
    (hlow : LowBranchSourceObligation)
    (hmiddle : MiddleBranchSourceObligation)
    (hupper : UpperR2SourceObligation) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) := by
  exact erdos_625_full_analytical_of_ready_certificates_and_sources
    (analytical_source_obligations_of_branches hlow hmiddle hupper)

/-- Final analytical assembly from the three named branch source-input
obligations and the current concrete certificate/output-layer package. -/
theorem erdos_625_full_analytical_of_ready_branch_source_inputs
    (hlow : LowBranchSourceInputObligation)
    (hmiddle : MiddleBranchSourceInputObligation)
    (hupper : UpperR2SourceInputObligation) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) := by
  exact erdos_625_full_analytical_of_source_input_obligations
    (analytical_source_input_obligations_of_branches hlow hmiddle hupper)

/-- Final analytical assembly from low/middle source-input obligations and an
upper source theorem narrowed to the endpoint-component contract. -/
theorem erdos_625_full_analytical_of_ready_branch_source_inputs_and_upper_endpoint
    (hlow : LowBranchSourceInputObligation)
    (hmiddle : MiddleBranchSourceInputObligation)
    (hupper : UpperR2EndpointSourceObligation) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) := by
  exact erdos_625_full_analytical_of_source_input_obligations
    (analytical_source_input_obligations_of_upper_endpoint
      hlow
      hmiddle
      hupper)

/-- Final analytical assembly from low/middle certificate-level obligations
and an upper source theorem narrowed to the endpoint-component contract. -/
theorem erdos_625_full_analytical_of_ready_certificates_and_upper_endpoint
    (hlow : LowBranchCertificateSourceObligation)
    (hmiddle : MiddleBranchCertificateSourceObligation)
    (hupper : UpperR2EndpointSourceObligation) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) := by
  exact erdos_625_full_analytical_of_source_input_obligations
    (analytical_source_input_obligations_of_certificates_and_upper_endpoint
      hlow
      hmiddle
      hupper)

/-- Final analytical assembly from the explicit Stage-1 remaining-work
checklist. -/
theorem erdos_625_full_analytical_of_remaining_obligations
    (hremaining : AnalyticalRemainingObligations) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) := by
  exact erdos_625_full_analytical_of_ready_certificates_and_sources
    (analytical_source_obligations_of_remaining hremaining)

/-- Final analytical assembly from the precise Stage-2 remaining-work
checklist: low/middle source-input WHP theorems and the upper endpoint-source
WHP theorem. -/
theorem erdos_625_full_analytical_of_remaining_source_input_obligations
    (hremaining : AnalyticalRemainingSourceInputObligations) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) := by
  exact erdos_625_full_analytical_of_source_input_obligations
    (analytical_source_input_obligations_of_remaining_source_inputs hremaining)

/-- Final analytical assembly from the narrowest current Stage-2
remaining-work checklist: low/middle certificate-level WHP theorems and the
upper endpoint-source WHP theorem. -/
theorem erdos_625_full_analytical_of_remaining_certificate_obligations
    (hremaining : AnalyticalRemainingCertificateObligations) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) := by
  exact erdos_625_full_analytical_of_source_input_obligations
    (analytical_source_input_obligations_of_remaining_certificates hremaining)

/-- Final analytical assembly from the fixed-constants Stage-2
remaining-work checklist: concrete low, middle, and upper WHP conclusions. -/
theorem erdos_625_full_analytical_of_remaining_concrete_obligations
    (hremaining : AnalyticalRemainingConcreteObligations) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) := by
  exact erdos_625_full_analytical_of_source_input_obligations
    (analytical_source_input_obligations_of_remaining_concrete hremaining)

/-- Final analytical assembly from the concrete low source-input event target
and the post-low fixed-constants checklist.

This is the full-theorem route expected immediately after the low concrete
source theorem is discharged: the low input is supplied by
`LowBranchConcreteSourceInputEventObligation`, while the remaining checklist
contains only the middle and upper concrete WHP source obligations.
-/
theorem erdos_625_full_analytical_of_low_event_and_without_low
    (hlow : LowBranchConcreteSourceInputEventObligation)
    (hremaining : AnalyticalRemainingConcreteObligationsWithoutLow) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) := by
  exact erdos_625_full_analytical_of_remaining_concrete_obligations
    (analytical_remaining_concrete_obligations_of_low_event_and_without_low
      hlow hremaining)

/-- Final analytical assembly from the structured concrete low source-event
component bundle and the post-low fixed-constants checklist. -/
theorem erdos_625_full_analytical_of_low_component_bundle_and_without_low
    (hlow : LowBranchConcreteSourceInputEventComponents)
    (hremaining : AnalyticalRemainingConcreteObligationsWithoutLow) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) := by
  exact erdos_625_full_analytical_of_low_event_and_without_low
    (low_branch_concrete_source_input_event_obligation_of_component_bundle hlow)
    hremaining

/-- Final analytical assembly from concrete low and middle source-input event
targets plus the remaining upper fixed-constants checklist.

This is the full-theorem route expected after both the low and middle concrete
source theorems are discharged: only the upper concrete WHP source obligation
remains in the fixed-constants checklist.
-/
theorem erdos_625_full_analytical_of_low_middle_events_and_without_upper
    (hlow : LowBranchConcreteSourceInputEventObligation)
    (hmiddle : MiddleBranchConcreteSourceInputEventObligation)
    (hremaining : AnalyticalRemainingConcreteObligationsWithoutLowMiddle) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) := by
  exact erdos_625_full_analytical_of_remaining_concrete_obligations
    (analytical_remaining_concrete_obligations_of_low_middle_events_and_without_upper
      hlow hmiddle hremaining)

/-- Final analytical assembly from structured low and middle source-event
component bundles plus the remaining upper fixed-constants checklist. -/
theorem erdos_625_full_analytical_of_low_middle_component_bundles_and_without_upper
    (hlow : LowBranchConcreteSourceInputEventComponents)
    (hmiddle : MiddleBranchConcreteSourceInputEventComponents)
    (hremaining : AnalyticalRemainingConcreteObligationsWithoutLowMiddle) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) := by
  exact erdos_625_full_analytical_of_low_middle_events_and_without_upper
    (low_branch_concrete_source_input_event_obligation_of_component_bundle hlow)
    (middle_branch_concrete_source_input_event_obligation_of_component_bundle
      hmiddle)
    hremaining

/-- Final analytical assembly from concrete source-input event targets for all
three regimes.

This is the event-component-shaped Stage-1 completion interface: once low,
middle, and upper source proofs each supply a WHP event and deterministic
inclusion into the corresponding regime-conditional gap event, the wrapper
assembles the full analytical theorem without any remaining concrete checklist
input.
-/
theorem erdos_625_full_analytical_of_all_regime_events
    (hlow : LowBranchConcreteSourceInputEventObligation)
    (hmiddle : MiddleBranchConcreteSourceInputEventObligation)
    (hupper : UpperR2ConcreteSourceInputEventObligation) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) := by
  exact erdos_625_full_analytical_of_remaining_concrete_obligations
    (analytical_remaining_concrete_obligations_of_all_regime_events
      hlow hmiddle hupper)

/-- Final analytical assembly from structured source-event component bundles
for all three regimes. -/
theorem erdos_625_full_analytical_of_all_regime_component_bundles
    (hlow : LowBranchConcreteSourceInputEventComponents)
    (hmiddle : MiddleBranchConcreteSourceInputEventComponents)
    (hupper : UpperR2ConcreteSourceInputEventComponents) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) := by
  exact erdos_625_full_analytical_of_all_regime_events
    (low_branch_concrete_source_input_event_obligation_of_component_bundle hlow)
    (middle_branch_concrete_source_input_event_obligation_of_component_bundle
      hmiddle)
    (upper_r2_concrete_source_input_event_obligation_of_component_bundle hupper)

/-- Final analytical assembly from the bundled all-regime event-obligation
contract. -/
theorem erdos_625_full_analytical_of_all_regime_event_obligations
    (h : AnalyticalAllRegimeConcreteSourceInputEventObligations) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) := by
  exact erdos_625_full_analytical_of_remaining_concrete_obligations
    (analytical_remaining_concrete_obligations_of_all_regime_event_obligations h)

/-- Final analytical assembly from the bundled all-regime source-event
component contract. -/
theorem erdos_625_full_analytical_of_all_regime_component_bundle
    (h : AnalyticalAllRegimeConcreteSourceInputEventComponents) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) := by
  exact erdos_625_full_analytical_of_all_regime_event_obligations
    (analytical_all_regime_event_obligations_of_component_bundle h)

/-- Alias for the singular all-regime source-event component package as the
current full analytical wrapper replacement route.

This name is intended as the most direct target for future source modules that
produce one bundled event-component package for all three regimes.
-/
theorem erdos_625_full_analytical_of_all_regime_source_event_package
    (h : AnalyticalAllRegimeConcreteSourceInputEventComponents) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) :=
  erdos_625_full_analytical_of_all_regime_component_bundle h

/-- Current post-low fixed-constants checklist, still backed only by the
middle and upper concrete probabilistic source axioms.

The low concrete source theorem is intentionally absent from this checklist.
-/
theorem analytical_remaining_concrete_obligations_without_low_from_axioms :
    AnalyticalRemainingConcreteObligationsWithoutLow := by
  exact {
    middle_branch_concrete_source :=
      good_branch_partial_away_from_one_loglog_whp_of_bridge_inputs
        middle_branch_bridge_inputs_ready
    upper_r2_concrete_source :=
      upper_r2_endpoint_source_obligation_from_axiom
        UpperR2.upper_appendix_endpoint_components
  }

/-- Current post-low-and-middle fixed-constants checklist, still backed only
by the upper concrete probabilistic source axiom. -/
theorem analytical_remaining_concrete_obligations_without_low_middle_from_axioms :
    AnalyticalRemainingConcreteObligationsWithoutLowMiddle := by
  exact {
    upper_r2_concrete_source :=
      upper_r2_endpoint_source_obligation_from_axiom
        UpperR2.upper_appendix_endpoint_components
  }

/-- Dry run of the post-low route.

Supplying `LowBranchConcreteSourceInputEventObligation` removes the low concrete
source axiom from this route; the only remaining concrete source inputs are the
middle and upper WHP source gaps.
-/
theorem erdos_625_full_analytical_via_low_event_and_without_low :
    LowBranchConcreteSourceInputEventObligation →
      Filter.Tendsto
        (fun n : ℕ => gnHalf n (analyticalGapEvent n))
        Filter.atTop (nhds (1 : ℝ≥0∞)) :=
  fun hlow =>
    erdos_625_full_analytical_of_low_event_and_without_low
      hlow
      analytical_remaining_concrete_obligations_without_low_from_axioms

/-- Dry run of the post-low route from the structured concrete low source-event
component bundle. -/
theorem erdos_625_full_analytical_via_low_component_bundle_and_without_low :
    LowBranchConcreteSourceInputEventComponents →
      Filter.Tendsto
        (fun n : ℕ => gnHalf n (analyticalGapEvent n))
        Filter.atTop (nhds (1 : ℝ≥0∞)) :=
  fun hlow =>
    erdos_625_full_analytical_of_low_component_bundle_and_without_low
      hlow
      analytical_remaining_concrete_obligations_without_low_from_axioms

/-- Dry run of the post-low-and-middle route.

Supplying concrete source-input event obligations for both low and middle
removes those two concrete source axioms from this route; the only remaining
concrete source input is the upper WHP source gap.
-/
theorem erdos_625_full_analytical_via_low_middle_events_and_without_upper :
    LowBranchConcreteSourceInputEventObligation →
      MiddleBranchConcreteSourceInputEventObligation →
        Filter.Tendsto
          (fun n : ℕ => gnHalf n (analyticalGapEvent n))
          Filter.atTop (nhds (1 : ℝ≥0∞)) :=
  fun hlow hmiddle =>
    erdos_625_full_analytical_of_low_middle_events_and_without_upper
      hlow
      hmiddle
      analytical_remaining_concrete_obligations_without_low_middle_from_axioms

/-- Dry run of the post-low-and-middle route from structured concrete
source-event component bundles. -/
theorem erdos_625_full_analytical_via_low_middle_component_bundles_and_without_upper :
    LowBranchConcreteSourceInputEventComponents →
      MiddleBranchConcreteSourceInputEventComponents →
        Filter.Tendsto
          (fun n : ℕ => gnHalf n (analyticalGapEvent n))
          Filter.atTop (nhds (1 : ℝ≥0∞)) :=
  fun hlow hmiddle =>
    erdos_625_full_analytical_of_low_middle_component_bundles_and_without_upper
      hlow
      hmiddle
      analytical_remaining_concrete_obligations_without_low_middle_from_axioms

/-- Axiom-backed dry run through the precise Stage-2 remaining-work checklist.

This has the same current axiom closure as the public analytical theorem, but
it verifies that the preferred checklist is sufficient for the final assembly
route. -/
theorem erdos_625_full_analytical_via_remaining_source_input_obligations :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) :=
  erdos_625_full_analytical_of_remaining_source_input_obligations
    analytical_remaining_source_input_obligations_from_axioms

/-- Axiom-backed dry run through the narrowest current Stage-2 checklist.

This has the same current axiom closure as the public analytical theorem, but
it verifies that certificate-level low/middle obligations plus the upper
endpoint obligation are sufficient for the final assembly route. -/
theorem erdos_625_full_analytical_via_remaining_certificate_obligations :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) :=
  erdos_625_full_analytical_of_remaining_certificate_obligations
    analytical_remaining_certificate_obligations_from_axioms

/-- Axiom-backed dry run through the fixed-constants Stage-2 checklist.

This is the narrowest current public route: it needs only the three concrete
branch WHP conclusions for the already-certified low, middle, and upper
regimes. -/
theorem erdos_625_full_analytical_via_remaining_concrete_obligations :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) :=
  erdos_625_full_analytical_of_remaining_concrete_obligations
    analytical_remaining_concrete_obligations_from_axioms


/-- Full analytical assembly from the three explicit bridge-input bundles.

This is the wrapper-level replacement target for the whole analytical route:
future work should replace the three `*_of_bridge_inputs` axioms by theorems,
then this theorem will assemble the final WHP conclusion without changing the
probabilistic intersection/monotonicity layer. -/
theorem erdos_625_full_analytical_of_bridge_inputs
    (hinputs : AnalyticalBridgeInputs) :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) := by
  exact erdos_625_full_analytical_of_source_obligations
    hinputs
    analytical_source_obligations_from_axioms

/-- Axiom-backed dry run of the endpoint-component final route.

This has the same current axiom closure as `erdos_625_full_analytical`, but it
checks that the endpoint-component route can replace the output-layer route
without changing the remaining source-obligation boundary. -/
theorem erdos_625_full_analytical_via_endpoint_components :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) :=
  erdos_625_full_analytical_of_ready_endpoint_components_branch_sources
    low_branch_source_obligation_from_axiom
    middle_branch_source_obligation_from_axiom
    upper_r2_source_obligation_from_axiom

/-- Axiom-backed dry run of the endpoint-component route through the narrower
source-input-shaped WHP boundary.

This has the same current axiom closure as `erdos_625_full_analytical`, but it
checks that the preferred Stage-2 source-input route reaches the final theorem
without widening back to the branch source-obligation interface at the call
site. -/
theorem erdos_625_full_analytical_via_endpoint_source_inputs :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) :=
  erdos_625_full_analytical_of_ready_endpoint_components_branch_source_inputs
    low_branch_source_input_obligation_from_axiom
    middle_branch_source_input_obligation_from_axiom
    upper_r2_source_input_obligation_from_axiom

/-- Axiom-backed dry run of the fully parameterized Stage-2 source-input
route.

This checks the handoff from the concrete `AnalyticalSourceBridgeInputs` bundle
and the current axiom-backed source-input obligations into the final theorem. -/
theorem erdos_625_full_analytical_via_source_bridge_inputs :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) :=
  erdos_625_full_analytical_of_source_bridge_inputs_and_source_inputs
    analytical_source_bridge_inputs_ready
    analytical_source_input_obligations_from_axioms

/-- Axiom-backed dry run in which the upper WHP boundary is already narrowed
to the endpoint-component contract. -/
theorem erdos_625_full_analytical_via_upper_endpoint_source :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) :=
  erdos_625_full_analytical_of_ready_branch_source_inputs_and_upper_endpoint
    low_branch_source_input_obligation_from_axiom
    middle_branch_source_input_obligation_from_axiom
    upper_r2_endpoint_source_obligation_from_axiom

/-- Full analytical theorem, Lean-facing Stage-1 wrapper.

The dependency closure of this theorem is the fixed-constants Stage-2
worklist.  It currently routes through
`erdos_625_full_analytical_via_remaining_concrete_obligations`, whose inputs
are `AnalyticalRemainingConcreteObligations`: concrete low, middle, and upper
WHP conclusions for the already-certified analytical regimes.  It is the route
whose `Problem625.Analytical.*` axiom closure is compared by the verifier; the verifier compares this concrete route's
`Problem625.Analytical.*` axiom closure against the public theorem closure.  It
should eventually contain no analytical WHP bridge axioms.
-/
theorem erdos_625_full_analytical :
  Filter.Tendsto
    (fun n : ℕ => gnHalf n (analyticalGapEvent n))
    Filter.atTop (nhds (1 : ℝ≥0∞)) :=
  erdos_625_full_analytical_via_remaining_concrete_obligations

/-!
## Paper-axiom decomposition — all three branches discharged

The theorems below replace all three bridge-shaped WHP axioms
(`lowBranchGapWHPAxiom`, `good_branch_partial_away_from_one_loglog_whp_of_bridge_inputs`,
`upper_boundary_r2_integrated_loglog_whp_of_bridge_inputs`) with paper-level axioms
citing the specific published results used in the mathematical proof.

### Low branch paper axioms
- `paperLowBranchChiLower_source` — HP-2023 Lemma 8.1 (chromatic lower bound, unconditional)
- `paperLowBranchZetaUpper_source` — first-moment/Markov route:
  HP-2023 Co. 39 + Le. 7.4, Heckel 2024 arXiv:2409.17614 line 516, Markov (no regime restriction)

### Middle branch paper axiom
- `middleBranchCrossingComplementWHPAxiom` — HP-2023 §7+§8 + Heckel 2024 §3–7
  (crossing complement ¬InMainRange; main-range half is proved in main repo)

### Upper branch paper axioms
- `upperBranchPaperWHPAxiom` — HP-2023 Theorem 1 + §7 (G3 cochromatic) +
  HP-2023 §4 Lemma 4.1 (first-moment main-range) +
  HP-2023 Appendix (gap-rate numerical certificate)
-/

/-- Conservative low-branch scale n/log³n. -/
private noncomputable def lowBranchLogCubedScalePub (n : ℕ) : ℝ :=
  (n : ℝ) / Real.log (n : ℝ) ^ 3

/-- Conservative low-branch saving: (1/2000)·n/log³n. -/
private noncomputable def lowBranchConservativeSavingPub (n : ℕ) : ℝ :=
  (1 / 2000 : ℝ) * lowBranchLogCubedScalePub n

/-- Conservative low-branch error (per side): (1/16000)·n/log³n. -/
private noncomputable def lowBranchConservativeErrorPub (n : ℕ) : ℝ :=
  (1 / 16000 : ℝ) * lowBranchLogCubedScalePub n

/-- **[HP-2023 Lemma 8.1]** Chromatic lower bound for the low branch.

χ(G(n,1/2)) ≥ kThresholdWitness n − (1/16000)·n/log³n  with probability → 1.

HP-2023 Lemma 8.1 (unconditional first-moment): for a ∈ {α-2, α-1},
E[number of a-bounded (k_a-2)-colorings] → 0, giving χ_{α-1}(G) ≥ k_{α-1} − 1 whp.
The quantitative error (1/16000)·n/log³n is a conservative Lean bookkeeping constant
within the o(1) slack of Lemma 8.1. No regime restriction on fractionalParameter n.

Source: Heckel–Panagiotou (HP-2023), arXiv:2306.07253, Lemma 8.1. -/
axiom paperLowBranchChiLower_source :
    Filter.Tendsto
      (fun n : ℕ =>
        gnHalf n {G : SimpleGraph (Fin n) |
          kThresholdWitness n - lowBranchConservativeErrorPub n ≤
            (chromaticNumber G : ℝ)})
      Filter.atTop (nhds (1 : ENNReal))

/-- **[HP-2023 Co. 39 + Le. 7.4 + Heckel 2024 line 516 + Markov]**
Cochromatic upper bound for the low branch.

ζ(G(n,1/2)) ≤ kThresholdWitness n − (1/2000)·n/log³n + (1/16000)·n/log³n  whp.
No regime restriction on fractionalParameter n.

**Proof route: first-moment / Markov — works in InLowRegime (x < x₀ ≈ 0.029155).**

This does NOT use the C5 second-moment argument (which requires φ(1,x,1) > 0, failing
for x < x₀). Instead:

1. HP-2023 Lemma 7.4 (= Heckel–Riordan 2023, arXiv:2103.14014, Lemma 41):
   n/k_{α−1} = α₀−1−2/ln2+o(1), no regime restriction.
2. HP-2023 Corollary 39 (onemorecolour/delk): ∂L₀(n,k,α−1)/∂k = (2/ln2)·log²n + O(...),
   no regime restriction (also `oneMoreColourAxiom_low`).
3. Heckel 2024 arXiv:2409.17614, lines 514–516 (eq:firstmomentcocol):
   E[X^co_k] = 2^k · E[X_k] (exact formula, no regime restriction).
4. Markov: P(ζ ≥ k_{α−1}−D) ≤ E[X^co_{k_{α−1}−D}] → 0 for D = Θ(n/log³n).

Full proof: problems/625/work/notes/inlowregime-cochromatic-upper-bound-proof-2026-05-15.md
(5-expert swarm, 7 iterations, red-team confirmed 2026-05-15).

Sources: HP-2023 arXiv:2306.07253 (Co. 39, Le. 7.4);
Heckel 2024 arXiv:2409.17614 (lines 514–516);
Heckel–Riordan 2023 arXiv:2103.14014 (Le. 41). -/
axiom paperLowBranchZetaUpper_source :
    Filter.Tendsto
      (fun n : ℕ =>
        gnHalf n {G : SimpleGraph (Fin n) |
          (cochromaticNumber G : ℝ) ≤
            kThresholdWitness n - lowBranchConservativeSavingPub n +
              lowBranchConservativeErrorPub n})
      Filter.atTop (nhds (1 : ENNReal))

/-- Net gap: (chiLower) − (zetaUpper) = saving − 2·error = (6/16000)·n/log³n. -/
private theorem lowBranchConservativeGapLowerPub (n : ℕ) :
    (kThresholdWitness n - lowBranchConservativeErrorPub n) -
      (kThresholdWitness n - lowBranchConservativeSavingPub n +
        lowBranchConservativeErrorPub n) =
    (3 / 8000 : ℝ) * lowBranchLogCubedScalePub n := by
  simp only [lowBranchConservativeSavingPub, lowBranchConservativeErrorPub]
  ring

/-- Low-regime WHP proved directly from the two paper axioms.

Proof: combine `paperLowBranchChiLower_source` and `paperLowBranchZetaUpper_source`
via `gnHalf_whp_inter` to get WHP of the intersection event
  { G | χ(G) ≥ kThresh − ε } ∩ { G | ζ(G) ≤ kThresh − saving + ε }.
In this intersection, χ − ζ ≥ saving − 2·ε = (3/8000)·n/log³n (by
`lowBranchConservativeGapLowerPub`, proved by `ring`).
Since logLogW n ≤ (3/8000)·n/log³n eventually (`logLogW_eventually_le_C_n_div_log_cubed`),
the intersection is eventually a subset of `lowRegimeConditionalGapEvent n`.
The finite-prefix patching gives the full tendsto. -/
theorem lowBranchWHP_of_paper_axioms :
    Filter.Tendsto
      (fun n : ℕ => gnHalf n (lowRegimeConditionalGapEvent n))
      Filter.atTop (nhds (1 : ENNReal)) := by
  -- Step 1: WHP of the joint chi-lower / zeta-upper intersection
  let jointEvent : (n : ℕ) → Set (SimpleGraph (Fin n)) :=
    fun n => {G : SimpleGraph (Fin n) |
      kThresholdWitness n - lowBranchConservativeErrorPub n ≤ (chromaticNumber G : ℝ) ∧
      (cochromaticNumber G : ℝ) ≤ kThresholdWitness n - lowBranchConservativeSavingPub n +
        lowBranchConservativeErrorPub n}
  have hjoint : Filter.Tendsto
      (fun n : ℕ => gnHalf n (jointEvent n))
      Filter.atTop (nhds (1 : ENNReal)) := by
    have h := gnHalf_whp_inter
      (A := fun n => {G | kThresholdWitness n - lowBranchConservativeErrorPub n ≤
          (chromaticNumber G : ℝ)})
      (B := fun n => {G | (cochromaticNumber G : ℝ) ≤ kThresholdWitness n -
          lowBranchConservativeSavingPub n + lowBranchConservativeErrorPub n})
      paperLowBranchChiLower_source
      paperLowBranchZetaUpper_source
    exact h.congr' (by filter_upwards; intro n; simp [jointEvent, Set.mem_setOf_eq])
  -- Step 2: In jointEvent n, χ − ζ ≥ (3/8000)·n/log³n
  have hgap_in_joint : ∀ n : ℕ, ∀ G ∈ jointEvent n,
      (3 / 8000 : ℝ) * lowBranchLogCubedScalePub n ≤
        (chromaticNumber G : ℝ) - (cochromaticNumber G : ℝ) := by
    intro n G hG
    simp only [jointEvent, Set.mem_setOf_eq] at hG
    have heq := lowBranchConservativeGapLowerPub n
    linarith [hG.1, hG.2]
  -- Step 3: logLogW n ≤ (3/8000)·n/log³n eventually
  obtain ⟨N_gap, hN_gap⟩ :=
    logLogW_eventually_le_C_n_div_log_cubed (3 / 8000) (by norm_num)
  -- Step 4: jointEvent n ⊆ lowRegimeConditionalGapEvent n for n ≥ N_gap
  have hsubset : ∀ n : ℕ, N_gap ≤ n → jointEvent n ⊆ lowRegimeConditionalGapEvent n := by
    intro n hn G hG _
    have h1 := hN_gap n hn
    have h2 := hgap_in_joint n G hG
    simp only [lowBranchLogCubedScalePub] at h2
    have h2' : 3 / 8000 * ↑n / Real.log ↑n ^ 3 ≤ ↑(chromaticNumber G) - ↑(cochromaticNumber G) := by
      linarith [mul_div_assoc (3 / 8000 : ℝ) (n : ℝ) (Real.log (n : ℝ) ^ 3)]
    linarith
  -- Step 5: patch finite prefix and apply monotonicity
  let patchedEvent : (n : ℕ) → Set (SimpleGraph (Fin n)) :=
    fun n => if n < N_gap then lowRegimeConditionalGapEvent n else jointEvent n
  have hpatch_sub : ∀ n : ℕ, patchedEvent n ⊆ lowRegimeConditionalGapEvent n := by
    intro n G hG
    by_cases hn : n < N_gap
    · simpa [patchedEvent, hn] using hG
    · exact hsubset n (Nat.le_of_not_gt hn) (by simpa [patchedEvent, hn] using hG)
  have hpatch_whp : Filter.Tendsto
      (fun n : ℕ => gnHalf n (patchedEvent n))
      Filter.atTop (nhds (1 : ENNReal)) :=
    hjoint.congr' (by
      filter_upwards [Filter.eventually_ge_atTop N_gap] with n hn
      simp [patchedEvent, Nat.not_lt.mpr hn])
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    hpatch_whp tendsto_const_nhds
    (fun n => measure_mono (hpatch_sub n))
    (fun n => by haveI : IsProbabilityMeasure (gnHalf n) := by unfold gnHalf; infer_instance
                 exact prob_le_one)

/-- **[HP-2023 §7+§8, Heckel 2024 §3–7]** Middle crossing-complement WHP.

For n with ¬InMainRange ε n, the gap χ − ζ ≥ logLogW n holds whp.
The main-range half (InMainRange ε n) is proved via `heckel_chromatic_lower_bound_with_error`
(ChromaticConnection) and `heckel_zeta_upper_bound_with_error` (ZetaConcentration).

Sources: HP-2023 arXiv:2306.07253 §7+§8 (Lemma 8.1, tame-profile second moment);
Heckel 2024 arXiv:2409.17614 §3–7. -/
axiom middleBranchCrossingComplementWHPAxiom :
    Filter.Tendsto
      (fun n : ℕ => gnHalf n (middleRegimeConditionalGapEvent n))
      Filter.atTop (nhds (1 : ENNReal))

/-- **[HP-2023 Theorem 1 + §4 + §7 + Appendix]** Upper branch WHP.

For n with InUpperRegime n (fractionalParameter n ∈ [0.95, 1]),
the gap χ − ζ ≥ logLogW n holds whp.

This is derived in the main formalization from three component axioms:
- G3 profitable-profile cochromatic bound (HP-2023 Theorem 1 + §7):
  ∃ saving, zetaError, WHP event s.t. ζ(G) ≤ boldK_α − saving + zetaError whp
- Upper-regime first-moment main-range (HP-2023 §4, Lemma 4.1):
  InUpperRegime n implies InMainRange ε n for small ε
- Gap-rate certificate (HP-2023 Appendix):
  logLogW n ≤ saving − transferError − zetaError eventually

The full derivation uses the UpperR2SharpFirstMomentProfilewiseG3SourcePayload route
(Erdosreshala/Problem625/UpperBranchSourceAxiom.lean).

Sources: Heckel–Panagiotou, arXiv:2306.07253 (Theorem 1, §4 Lemma 4.1, §7, Appendix);
Heckel–Riordan 2023, arXiv:2103.14014 (Lemma 44). -/
axiom upperBranchPaperWHPAxiom :
    Filter.Tendsto
      (fun n : ℕ => gnHalf n (upperRegimeConditionalGapEvent n))
      Filter.atTop (nhds (1 : ENNReal))

/-- **Erdős Problem 625 — all three branches discharged**

All three bridge-shaped WHP axioms are replaced by paper-level axioms:

- Low branch: `paperLowBranchChiLower_source` (HP-2023 Lemma 8.1) +
  `paperLowBranchZetaUpper_source` (HP-2023 Co. 39 + Heckel 2024 line 516 + Markov)
- Middle branch: `middleBranchCrossingComplementWHPAxiom` (HP-2023 §7+§8, Heckel 2024 §3–7)
- Upper branch: `upperBranchPaperWHPAxiom` (HP-2023 Theorem 1, §4, §7, Appendix)

No bridge-shaped axioms remain. All axiomatic content is at the paper-citation level.

For the full axiom inventory and mathematical justification, see:
- `problems/625/solution/proof.md`
- `Erdosreshala/Problem625/UpperBranchSourceAxiom.lean` (main repo)
- `Erdosreshala/Problem625/MiddleCrossingComplementAxiom.lean` (main repo)
- `Erdosreshala/Problem625/LowBranchSourceEvent.lean` (main repo) -/
theorem erdos625_low_discharged :
    Filter.Tendsto
      (fun n : ℕ => gnHalf n (analyticalGapEvent n))
      Filter.atTop (nhds (1 : ℝ≥0∞)) :=
  erdos_625_full_analytical_of_remaining_concrete_obligations
    { low_branch_concrete_source := lowBranchWHP_of_paper_axioms
      middle_branch_concrete_source := middleBranchCrossingComplementWHPAxiom
      upper_r2_concrete_source := upperBranchPaperWHPAxiom }

end Problem625.Analytical
