# Red-Team Critique — proof/proof.md ↔ PublishableProof.lean Link

**Target**: `proof/proof.md` ↔ `Erdos625/PublishableProof.lean` (+ dependencies)
**Date**: 2026-05-10
**Scope**: Adversarial verification that the human-readable proof document faithfully describes the machine-checked Lean formalization.

**Files read**:
- `proof/proof.md` (161 lines)
- `Erdos625/PublishableProof.lean` (341 lines, full)
- `Erdos625/RouteD2.lean` (lines 228–277, key theorem)
- `Erdos625/ChromaticConnection.lean` (selective: key theorem/axiom names, sorry location)
- `Erdos625/ZetaConcentration.lean` (selective: key theorem/axiom names, Azuma signature, sorry location)
- `Erdos625/GapArithmetic.lean` (selective: theorem signature)
- `Erdos625/PartBProfileBridge.lean` (axiom declarations)
- `Erdos625/Defs.lean` (threshold, thresholdFloor, InMainRange definitions)
- `Erdos625/FirstMomentThreshold.lean` (selective: kThresholdWitness, tBoundedColoringCount)

---

## Summary Verdict

**0 CRITICAL issues, 2 MINOR issues, 1 RECOMMENDATION.** The proof.md document is highly faithful to the Lean formalization. All theorem names, axiom names, proof structure, exponent values, and sorry/axiom counts are correct. Two minor inaccuracies exist: a factor-of-2 omission in the Azuma tail formula and an oversimplified description of the class-size parameter t. Both are correctable without affecting the mathematical validity of the argument.

---

## CRITICAL Issues

None.

---

## MINOR Issues

### M1 — Azuma tail formula drops a factor of 2

**Severity**: MINOR

**Location**: `proof/proof.md`, Part C section, lines 70–72.

**Evidence**: proof.md says:
> "P[ζ ≥ E[ζ] + s] ≤ exp(−s²/(2n)); setting s = n^{0.999} gives tail probability **exp(−n^{0.998}) = o(ε)**"

The Lean theorem `zeta_azuma_tail_bound` (ZetaConcentration.lean:1134–1138) has type:
```lean
theorem zeta_azuma_tail_bound (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 ≤ t) :
    (gnHalf n).real {G | E[ζ] + t ≤ cochromaticNumber G} ≤
      Real.exp (-(t ^ 2) / (2 * (n : ℝ)))
```

With s = t = n^{0.999}, the formula gives:
- `exp(-(n^{0.999})^2 / (2 * n)) = exp(-n^{1.998} / (2n)) = exp(-n^{0.998} / 2)`

The correct expression is `exp(-n^{0.998}/2)`, not `exp(-n^{0.998})`. The factor of 2 from the denominator `2n` is dropped.

**Impact**: The conclusion "= o(ε)" is correct either way (both go to 0). The error is in the stated formula, not the conclusion. A careful reader checking the Lean proof will see the discrepancy.

**Resolution**: Change "exp(−n^{0.998})" to "exp(−n^{0.998}/2)" in proof.md.

---

### M2 — t defined as ⌊2 log₂ n⌋ but Lean uses thresholdFloor n − 1

**Severity**: MINOR

**Location**: `proof/proof.md`, Statement section, line 24.

**Evidence**: proof.md says:
> "For this proof, t = ⌊2 log₂ n⌋."

The actual Lean definition (Defs.lean:155–161):
```lean
noncomputable def threshold (n : ℕ) : ℝ :=
  let logn := (n : ℝ).log / (2 : ℝ).log
  2 * logn - 2 * (logn.log / (2 : ℝ).log) + 2 * ((Real.exp 1 / 2).log / (2 : ℝ).log) + 1

noncomputable def thresholdFloor (n : ℕ) : ℕ := ⌊threshold n⌋₊
```

The class size used in coloring proofs is `t = thresholdFloor n - 1` (ChromaticConnection.lean line 688 comment: "when `t = thresholdFloor n - 1`").

So `t = ⌊2log₂(n) − 2log₂(log₂(n)) + 2log₂(e/2) + 1⌋₊ − 1`, which is asymptotically ≈ 2log₂(n) but differs by O(log log n) lower-order terms.

**Impact**: The description `t = ⌊2 log₂ n⌋` is an accepted asymptotic shorthand in the probabilistic combinatorics community and does not cause a mathematical error. However, a reader attempting to reconstruct the exact Lean definition from proof.md would be led to the wrong formula. The simplification is not qualified with "approximately."

**Resolution**: Add a qualification: change "t = ⌊2 log₂ n⌋" to "t ≈ 2 log₂ n (precisely: `thresholdFloor n − 1` in Lean, where `thresholdFloor n = ⌊2log₂(n) − 2log₂(log₂(n)) + O(1)⌋`)" — or at minimum add a parenthetical "(approximately)".

---

## RECOMMENDATIONS

### R1 — PublishableProof.lean "Non-reachable axioms" note is incomplete

**Evidence**: `PublishableProof.lean` lines 329–333 says:
> **Non-reachable axioms**: `heckel_zeta_upper_tail` and `heckel_zeta_lower_tail` (ZetaConcentration.lean, ...) are genuine `axiom` declarations in ZetaConcentration.lean, but they are NOT on the dependency path of `erdos_625`.

This mentions only 2 of the 7 non-reachable axioms. The other 5 (confirmed by `grep "^axiom"` on the Lean files):
- `profileLogCoreBridgeTarget_source` (PartBProfileBridge.lean)
- `paperPartBEndpointClosedVectorTailMoment…_source` (PartBProfileBridge.lean)
- `threshold_tBoundedColoringError_le_with_error` (ChromaticConnection.lean)
- `kThresholdWitness_le_n_div_threshold` (ChromaticConnection.lean)
- `threshold_decay_axiom` (ChromaticConnection.lean)

are not mentioned in this note.

**Mitigating factor**: proof.md (external document) correctly lists all 7 non-reachable axioms, and the note in PublishableProof.lean (line 34–35) says "see proof.md for the full audit trail." A reader following this pointer gets the correct list.

**Resolution**: Either (a) expand the PublishableProof.lean "Non-reachable axioms" note to list all 7, or (b) add a parenthetical "(see `proof/proof.md` for the complete list of 7 non-reachable axioms)" to the note as-is. Option (b) is lower friction.

---

## Verified Correct (no issues)

| Claim | Lean Evidence |
|-------|---------------|
| Theorem statement: `∃ n₀, ∀ n ≥ n₀, InMainRange → 1−2ε ≤ P[χ−ζ ≥ n^{1−ε}]` | `erdos_625` type (PublishableProof.lean:250–254) — exact match |
| 3 paper axioms, names exactly as stated | `grep "^axiom" Erdos625/*.lean` — all 3 confirmed at correct locations |
| 7 non-reachable axioms, names exactly as stated | All 7 confirmed by grep across PartBProfileBridge, ChromaticConnection, ZetaConcentration |
| 2 architectural sorrys off proof path, correct names | `decay_exponent_eventually_le_neg` (ChromaticConnection:3744), `heckel_zeta_mean_bound_from_upper_tail` (ZetaConcentration:1767) |
| `heckel_chromatic_lower_bound_of_exactNoEmpty` exists | ChromaticConnection.lean:3230 — confirmed |
| `heckel_zeta_upper_bound` exists | ZetaConcentration.lean:1865 — confirmed |
| `heckel_zeta_mean_upper_bound` exists and has 0 sorry | ZetaConcentration.lean:1588 — confirmed; sorry is only in the separate `heckel_zeta_mean_bound_from_upper_tail` |
| Named steps `part_B`, `part_C`, `joint_bound` | PublishableProof.lean:125, 141, 165 — confirmed |
| Exponents 0.9ε, ε/2, 999/1000, 99/100 | RouteD2.lean:243–247 uses exactly these; GapArithmetic:52–54 confirmed |
| `PublishableProof.lean` imports `RouteD2` | PublishableProof.lean:1 — `import Erdos625.RouteD2` |
| `MeasureTheory.measure_mono` used in union bound | PublishableProof.lean:283 — confirmed |
| File roles table accurate | All 7 named files exist with described contents — confirmed |

---

## Compact Ledger

| ID | Severity | Category | Description |
|----|----------|----------|-------------|
| M1 | MINOR | Formula inaccuracy | Azuma tail: `exp(-n^{0.998})` should be `exp(-n^{0.998}/2)` |
| M2 | MINOR | Oversimplification | `t = ⌊2 log₂ n⌋` not qualified; actual Lean: `thresholdFloor n − 1 ≈ ⌊2log₂n − O(log log n)⌋` |
| R1 | REC | Completeness | PublishableProof.lean "Non-reachable axioms" note lists 2 of 7; delegates to proof.md |

**Publication-ready?** Yes. The two MINOR issues are cosmetic corrections that don't affect mathematical validity. All load-bearing claims (theorem statement, axiom names, theorem names, sorry counts, exponent values) are correct. Fix M1 and M2 before release; R1 is optional but helpful.

---

## Ordered Fix List

1. **M1**: proof.md Part C: change "exp(−n^{0.998})" → "exp(−n^{0.998}/2)"
2. **M2**: proof.md Statement: add "(approximately)" or precise Lean definition for t
3. **R1**: PublishableProof.lean: add "(see `proof/proof.md` for the complete list of 7 non-reachable axioms)" to the non-reachable axioms note

---

## Provenance

- **Generated**: 2026-05-11 / 2026-05-12 development window.
- **Worker model**: `claude-opus-4-7[1m]` (Claude Opus 4.7, 1M-context variant).
- **Operator orchestrator**: `operator` (https://github.com/uthunderbird/vibechord); codex-brain adapter ran `gpt-5.3-codex-spark` at `effort=low`.
- **Same-model caveat**: this artefact was produced by the same LLM-agent pipeline that produced the proof being critiqued; it is an **internal adversarial audit**, not a third-party review. LLM-generated proofs may exhibit plausibility-driven failure modes that survive same-model critique because the proof author and the critic share training-data blind spots. See `../../README.md` Provenance and `../../DEVELOPMENT.md` ADR-10 / ADR-11 / ADR-12 for the full methodology disclosure. External verification by an unrelated reader, a different model, or a human mathematician is encouraged.
- **Footer added**: round-2 publish-readiness repair, 2026-05-12 (P1-7).
