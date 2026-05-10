# Paper Sources for the 3 Axioms

This file records the precise paper citations for the three admitted axioms in the
formalization of Erdős Problem 625.

## Axiom 1 — Part B average-class lower criterion

**Lean name**: `paperPartBThresholdAverageClassAsymptoticLowerCriterionTarget_source`
**File**: `Erdos625/PartBProfileBridge.lean`

**Paper**: Heckel, A. & Panagiotou, K. (2023). *Colouring random graphs: Tame colourings*.
arXiv:2306.07253.

**Source**: Lemma 5 (LaTeX cross-reference: `lemma:averagecolourclass`) and the associated
equation `eq:wert`. This controls the leading-order behavior of the expected t-bounded coloring
count near the first-moment threshold k*.

## Axiom 2 — Part B decay control

**Lean name**: `paperPartBExactNoEmptyDenomBinaryLowerControlledLhsDecayTarget_source`
**File**: `Erdos625/PartBProfileBridge.lean`

**Paper**: Heckel, A. & Panagiotou, K. (2023). *Colouring random graphs: Tame colourings*.
arXiv:2306.07253.

**Source**: Equation `eq:wert2`. This controls the sub-leading decay factor needed to establish
the chromatic lower bound at the threshold with the stated probability 1 − ε.

## Axiom 3 — Part C second-moment bound

**Lean name**: `heckel_cochromatic_second_moment`
**File**: `Erdos625/ZetaConcentration.lean`

**Paper**: Heckel, A. (2024). *The difference between the chromatic and the cochromatic number
of a random graph*. arXiv:2409.17614.

**Source**: Proposition 5(b). The bound is E[Z]²/E[Z²] > exp(−n^{0.99}), where Z counts
cochromatic colorings of G(n,1/2) with at most ⌊k* − n^{1−ε/2}⌋ colors. In Lean, this is
formalized in sum form as `exp(−n^{0.99}) · (∑_G Z(G)²) · |Ω| < (∑_G Z(G))²` under the
uniform measure `gnHalf`.

## Non-reachable axioms (do not affect the 3-axiom count)

The following `axiom` declarations exist in the repository but are **not** in the dependency
closure of `erdos_625` and will not appear in `#print axioms Problem625.Publishable.erdos_625`.
A reader running `grep "^axiom" Erdos625/*.lean` will find all of these in addition to the
3 paper axioms above.

**In `PartBProfileBridge.lean`**:
- `profileLogCoreBridgeTarget_source` — used only by the legacy Theorem 1 chain
  (`gnHalf_gap_ge_n_pow_one_minus_eps`); not by `erdos_625`.
- `paperPartBEndpointClosedVectorTailMomentQBoundedProductProfilePDenomAffineHalfLogSlackSmallClosedUniformAsymptoticNegOneStirlingFactorialUpperSplitAtBotTarget_source` — an alternative
  Stirling-endpoint discharge route for Part B; not on the dependency path of `erdos_625`.

**In `ChromaticConnection.lean`**:
- `threshold_tBoundedColoringError_le_with_error` — the direct axiom form of the coloring-error
  bound; used by alternative chromatic lower bound chains, not by `erdos_625`.
- `kThresholdWitness_le_n_div_threshold` — a threshold comparison axiom used by alternative
  route chains (the wired and via-threshold proofs); not by `erdos_625`.
- `threshold_decay_axiom` — a real-analysis decay axiom used by alternative chains; its
  content is proved as a theorem (`threshold_decay_axiom_discharge`) and the proved version
  is what the `erdos_625` chain uses.

**In `ZetaConcentration.lean`**:
- `heckel_zeta_upper_tail`, `heckel_zeta_lower_tail` — alternative derivation routes for
  ζ tail bounds; not used in the main proof.
