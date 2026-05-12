# Red-Team Strict Lemma-by-Lemma Audit — `publish/erdos-625/`

> **Note (2026-05-12 post-rename):** Throughout this audit, `partBThresholdWitness` (and the variant `kThresholdAlphaMinus2` used in mixed passages) refers to the Lean identifier now named `kThresholdAlphaMinusOne` (see `../../DEVELOPMENT.md` ADR-9). This audit is the one that surfaced the rename; the pre-rename name is preserved here for historical context. The mathematical content (the $(\alpha-1)$-bounded first-moment threshold $\mathbf{k}_{\alpha-1}$) is unchanged.

**Date**: 2026-05-12
**Auditor**: Swarm Red Team (Lamport · Avigad · Alon · Heckel · Tao)
**Target**: `Problem625.Publishable.erdos_625_full_clean`
**Build state**: GREEN (verified by `lake env lean axiomCheckFullClean.lean`)
**Mode**: Maximum rigor. Lemma-by-lemma N/S walk down to 4 paper axioms.

---

## Headline Verdict

**P0 = 0  ·  P1 = 2 (both PRE-DISCLOSED in Lean source)  ·  P2 = 3**

**Recommendation**: **CLEAR FOR PUBLICATION** (no blocking defects).

The flagship theorem `erdos_625_full_clean` is mechanically correct given its 4
paper axioms + 3 Lean kernel axioms. Every load-bearing inequality direction,
quantifier order, threshold convention, slack-arithmetic step, case-split branch,
and union-bound coefficient was verified by direct source inspection. The two
P1 findings are already DISCLOSED in the Lean axiom docstrings and in the
2026-05-12 per-axiom audit; no new defects were uncovered.

`#print axioms` ground truth:

```
'Problem625.Publishable.erdos_625_full_clean' depends on axioms: [propext,
 Classical.choice,
 Problem625.chi_alphaMinusTwo_lower_bound_whp,
 Problem625.partB_alphaMinusTwo_firstMomentBelowOne_source,
 Problem625.zeta_alphaMinusTwo_upper_bound_whp,
 Quot.sound,
 lemma_7_20_modified]
```

Matches the package's stated 4 paper + 3 kernel = 7 axioms exactly.

---

## P0 Findings

**None.**

The hunted failure modes did not materialize:

| Hunted defect | Verdict | Evidence |
|---|---|---|
| Sign error `χ−ζ` vs `ζ−χ` | NOT FOUND | All `linarith` discharges use `χ − ζ ≥ X` consistently; both branches and the corollary preserve sign. |
| Exponent direction `n^{1-ε}` vs `n^{1+ε}` | NOT FOUND | `1 − 2ε < 1 − ε < 1` for `ε ∈ (0, 0.001)`; corollary correctly *weakens* by lowering the exponent. |
| Threshold convention slip | NOT FOUND | `kThresholdAlphaMinus2Level = max 1 (α − 2)` and `partBThresholdLevel = max 1 (α − 1)`; smaller level ⇒ more restrictive ⇒ LARGER threshold; consistent with HP-2023 `boldk_a`. |
| Quantifier order `∀ε ∃n₀ ∀n` vs `∃n₀ ∀ε ∀n` | NOT FOUND | `theorem erdos_625_full_clean (ε : ℝ) ... : ∃ n₀, ...` — `n₀` is in scope under `ε`. Proof binds `n_full, n_arith` to ε-dependent existentials. |
| Hypothesis–conclusion direction (χ_a vs χ) | NOT FOUND | Both axioms target `χ` (not `χ_a`) directly: `chi_alphaMinusTwo_lower_bound_whp` concludes `kThr − n^{0.99} ≤ χ`; no χ_a inversion. |
| Slack arithmetic `n^{1−ε} − 2·n^{0.99} ≥ n^{1−2ε}` | VERIFIED | `rpow_clean_bound_eventually` proof is sound (see N/S audit below). |
| Case split (good vs crossing) | VERIFIED | `by_cases hmod : InMainRangeMod ε n` produces hmod (good ⇒ `erdos_625_97`) and ¬hmod (crossing ⇒ 3 axioms); both branches discharge the goal. |
| Union bound `1 − 2ε` arithmetic | VERIFIED | `gnHalf(Aᶜ) ≤ ε`, `gnHalf(Bᶜ) ≤ ε` ⇒ `gnHalf(A ∩ B) ≥ 1 − 2ε`. Exactly `1 − 2ε`, not `1 − ε` or `1 − 4ε`. |

---

## P1 Findings (both PRE-DISCLOSED — no new defects)

### P1-1 (PRE-DISCLOSED). HYBRID nature of `lemma_7_20_modified`

- **File:line**: `Erdos625/PublishableProof.lean:378-397`, axiom at line 398.
- **Claim**: Axiom statement combines HP-2023 §7 / Lemma 7.20 (peer-reviewed) with
  an OWN Lipschitz numerical certificate `lemma_7_10_ext` covering ϕ > 0 on
  `[x₀+ε, 0.04)`.
- **Why P1**: The package is honest — the docstring carries an explicit "red-team
  P1-A, 2026-05-11" disclosure, lists the numerical certificate parameters
  (min ϕ ≈ 6.5×10⁻⁷ on 1086-cell grid, Lipschitz bound L = 7.49×10⁻³, envelope
  6.15×10⁻⁷), and proposes the optional follow-up (formalize `lemma_7_10_ext`
  via `decide` on a fine rational grid). For arXiv this should be cited as
  Heckel 2024's conjectural `x₀ ≈ 0.02905` PLUS our certificate, not as a
  literal HP-2023 lemma. **Already correctly disclosed.** The corresponding
  documentation in `proof/proof.md` and `paper/main.tex` should preserve this
  framing — per the user's brief, the 2026-05-12 audit fix already aligned
  these.
- **Action required for publication**: NONE beyond confirming the paper still
  carries the disclosure (which the prior audit confirmed). P1 is informational.

### P1-2 (PRE-DISCLOSED). α−2 extrapolation of `zeta_alphaMinusTwo_upper_bound_whp`

- **File:line**: `Erdos625/CrossingPartB.lean:265-292`, axiom at line 293.
- **Claim**: Heckel-2024 explicitly restricts its second-moment construction to
  (α−1)-bounded profiles (Heckel 2024 §3 line 341, §5.1 line 529). The (α−2)
  adaptation used here is **not literally written** in Heckel 2024.
- **Why P1**: The axiom is a "natural symmetric extrapolation of a published
  result via the published proof technique", not a literal citation. The
  transfer rests on (a) HP-2023 §8 explicitly using the same machinery at both
  `a ∈ {α−2, α−1}`, (b) Heckel-2024 §3 importing HP-2023 techniques, and (c)
  numerical verification (`r2b-step1-results-2026-05-11.md`, min margin 0.4832
  at n=108). **Already disclosed in the docstring.** This is the most
  intellectually load-bearing risk in the package; if a reviewer rejects the
  extrapolation, the (α−2)-side ζ upper bound would have to be re-derived
  from HP-2023 §6.3/6.4/6.5 directly.
- **Action required for publication**: ensure the paper / proof.md mirror this
  disclosure prominently (per prior audit, this is now done). P1
  informational.

---

## P1 — Top 3 (consolidated)

1. **P1-1**: HYBRID `lemma_7_20_modified` (numerical Lipschitz certificate
   filling [x₀+ε, 0.04)). Disclosed. Optional formalization upgrade.
2. **P1-2**: (α−2) extrapolation of Heckel-2024 (α−1) second-moment machinery.
   Disclosed. Most reviewer-exposed claim.
3. **P1-3 (minor)**: Crossing axioms (`chi`/`zeta` at α−2) cover BOTH halves of
   `¬ InMainRangeMod ε n` — i.e. both the deep-crossing regime (`µ < n^{x₀+ε}`)
   AND the high regime (`µ > n^{1−ε}`). The docstring motivations focus on the
   deep-crossing side via `µ_{α−2} = Θ(n²/log²n · µ_α)`. The high-regime
   coverage is "absorbed by fiat" inside the axiom statement. This is a
   correctness concern only if the axiom is later replaced by a proved
   theorem; for the current axiomatic status, it is sound. Disclose as
   `r2b-step1-results-2026-05-11.md` already does.

---

## P2 Findings

- **P2-1**: `kThresholdAlphaMinus2Level n = max 1 (thresholdFloor n − 2)`. For tiny n where `thresholdFloor n ≤ 2`, level collapses to 1 and the (α−2)/(α−1) gap vanishes. Harmless because absorbed by the `∃ n₀` quantifier in `partB_alphaMinusTwo_firstMomentBelowOne_source`. Cosmetic / documentation only.
- **P2-2**: `lemma_7_20_modified` and the crossing axioms all carry `hε_small : ε < 0.001`; the threshold-gap lemma `kThreshold_gap_alpha_minus_2` only requires `0 < ε`. Asymmetric hypothesis surfaces are intentional but worth noting in a future "axiom surface" section.
- **P2-3**: `rpow_clean_bound_eventually` proof uses `ε < 0.001` only via `0 < 0.01 − ε`. A wider corollary `ε < 0.01` is provable verbatim; current `ε < 0.001` matches the flagship's stricter range, so no defect, just unused slack.

---

## Lemma-by-Lemma N/S Walk (Load-Bearing Path)

### Step 1 — `erdos_625_full_clean` (PublishableProof.lean:694–726)

- **Hypotheses**: `(ε : ℝ) (hε_pos : 0 < ε) (hε_small : ε < 0.001)`.
- **Conclusion**: `∃ n₀, ∀ n ≥ n₀, 1 − ENNReal.ofReal (2ε) ≤ gnHalf n {G | n^{1−2ε} ≤ χ − ζ}`.
- **Body**: extracts `n_full, h_full` from `erdos_625_full`, and `n_arith, h_arith` from `rpow_clean_bound_eventually`; takes `max`. For `n ≥ n₀`, derives `n^{1-2ε} ≤ n^{1-ε} − 2·n^{0.99} ≤ χ − ζ` via `linarith` on `MeasureTheory.measure_mono`.
- **N**: All five hypotheses (`hε_pos, hε_small, hn_full, hn_arith, hGap, h_arith_n`) are used. Removing any breaks `linarith`.
- **S**: Goal `n^{1-2ε} ≤ χ − ζ` follows from `n^{1-2ε} ≤ n^{1-ε} − 2·n^{0.99}` and `n^{1-ε} − 2·n^{0.99} ≤ χ − ζ` by transitivity. `linarith` is sufficient.
- **Verdict**: **PASS**.

### Step 2 — `rpow_clean_bound_eventually` (PublishableProof.lean:613–676)

- **Hypotheses**: `(ε : ℝ) (hε_pos : 0 < ε) (hε_small : ε < 0.001)`.
- **Conclusion**: `∀ᶠ n in atTop, n^{1−2ε} ≤ n^{1-ε} − 2·n^{0.99}`.
- **Body**: factors RHS as `n^{1-ε} · (n^{-ε} + 2·n^{ε-0.01})`; shows each summand → 0 (using `tendsto_rpow_neg_atTop` and `0.01 − ε > 0`); concludes sum ≤ 1 eventually; multiplies by `n^{1-ε} > 0`.
- **N**: `hε_pos` needed for first decay; `hε_small` (via `ε < 0.001 < 0.01`) needed for second decay. Both load-bearing.
- **S**: `nlinarith [h_rpow_pos, h_sum]` closes `r·s ≤ r − 2·(r·t)` given `r > 0, s + 2t ≤ 1`. Equivalent to `r(s + 2t) ≤ r`. Standard. Verified by `lake env lean`.
- **Verdict**: **PASS**.

### Step 3 — `erdos_625_full` (PublishableProof.lean:500–596)

- **Hypotheses**: same `ε`.
- **Conclusion**: `∃ n₀, ∀ n ≥ n₀, 1 − 2ε ≤ gnHalf n {G | n^{1-ε} − 2·n^{0.99} ≤ χ − ζ}`.
- **Body**: case-split on `InMainRangeMod ε n`.
  - **Good branch** (`hmod` true): uses `erdos_625_97` → `1 − 2ε ≤ gnHalf {n^{1-ε} ≤ χ − ζ}`; weakens via set-monotonicity using `0 ≤ n^{0.99}`; `linarith`.
  - **Crossing branch** (`¬ hmod`): defines `A = {kThr − n^{0.99} ≤ χ}`, `B = {ζ ≤ partBThr + n^{0.99}}`. From axioms: `gnHalf A ≥ 1 − ε`, `gnHalf B ≥ 1 − ε`. Union bound: `gnHalf (A∩B)ᶜ ≤ 2ε` ⇒ `gnHalf (A∩B) ≥ 1 − 2ε`. Promotes to target via deterministic threshold gap `n^{1-ε} ≤ kThr − partBThr` (from `kThreshold_gap_alpha_minus_2`); `linarith`.
- **N**: All four axioms used. `lemma_7_20_modified` reached only via `erdos_625_97` (good branch). Crossing 3 used only on `¬hmod` branch.
- **S**: Both branches independently establish `gnHalf {n^{1-ε} − 2·n^{0.99} ≤ χ − ζ} ≥ 1 − 2ε`. Union of branches covers all n. `linarith` discharges both arithmetic steps.
- **Verdict**: **PASS**. Union bound is exactly `1 − ε − ε = 1 − 2ε`. **No** off-by-factor error.

### Step 4 — `kThreshold_gap_alpha_minus_2` (CrossingWindowProof.lean:94–103)

- **Hypotheses**: `(ε : ℝ) (hε : 0 < ε)`.
- **Conclusion**: `∃ n₀, ∀ n ≥ n₀, n^{1-ε} ≤ kThresholdAlphaMinus2 n − partBThresholdWitness n`.
- **Body**: combines `kThresholdGapSource` (= `n/log²n ≤ kThr − partBThr`) with `n_div_log_sq_ge_rpow` (= `n^{1-ε} ≤ n/log²n`) by transitivity.
- **N**: Both ingredients required.
- **S**: Transitivity sound. `n_div_log_sq_ge_rpow` itself is a clean `o(·)`-based argument using `isLittleO_log_rpow_rpow_atTop`. Verified.
- **Verdict**: **PASS**.

### Step 5 — `kThresholdGapSource` / `partB_crossing_lower_bound_alpha_minus_two_source` (CrossingPartB.lean:184–186)

- **Conclusion**: `KThresholdGapSource` = `∃ n₀, ∀ n ≥ n₀, n/log²n ≤ kThr_{α−2} − partBThr_{α−1}`.
- **Body**: `:= partB_alphaMinusTwo_cumulant_gap_source` (a proved combinator deriving from the narrower `partB_alphaMinusTwo_firstMomentBelowOne_source` axiom via the `Nat.find` definition of `firstMomentThreshold` — see legacy proof at lines 190-226 for full content).
- **N**: The narrower axiom is necessary (no proved replacement).
- **S**: The combinator is the contrapositive of `Nat.find`'s defining property: "if E < 1 for all k < K, then `Nat.find (1 ≤ E) ≥ K`". Standard. Verified by build.
- **Verdict**: **PASS**.

### Step 6 — Four axioms (terminal nodes)

| Axiom | File:line | Conclusion shape | Verdict |
|---|---|---|---|
| `lemma_7_20_modified` | PublishableProof.lean:398 | `∃ n₀, ∀ n ≥ n₀, InMainRangeMod ε n → joint χLower/ζUpper bound ≥ 1−2ε` | `axiom` keyword confirmed; used at flagship-via-`erdos_625_97`. P1 disclosed (HYBRID). |
| `partB_alphaMinusTwo_firstMomentBelowOne_source` | PartBAlphaMinusTwoFirstMomentAxiom.lean:50 | First-moment `< 1` over window of width `⌈n/log²n⌉` above `partBThresholdWitness`. | `axiom` confirmed. Used by combinator. Citation: HP-2023 Lemma 8.1 proof, narrowed. PASS. |
| `chi_alphaMinusTwo_lower_bound_whp` | CrossingPartB.lean:251 | `∃ n₀, ∀ n ≥ n₀, ¬InMainRangeMod ε n → gnHalf {kThr_{α−2} − n^{0.99} ≤ χ} ≥ 1−ε` | `axiom` confirmed. Hypothesis `¬InMainRangeMod` matches use site. PASS. |
| `zeta_alphaMinusTwo_upper_bound_whp` | CrossingPartB.lean:293 | `∃ n₀, ∀ n ≥ n₀, ¬InMainRangeMod ε n → gnHalf {ζ ≤ partBThr_{α−1} + n^{0.99}} ≥ 1−ε` | `axiom` confirmed. P1 disclosed (α−2 extrapolation). PASS. |

All four are `axiom`, not `theorem`. Conclusions match use sites verbatim. Hypothesis surfaces (`hε_pos, hε_small, ¬InMainRangeMod ε n` resp. `InMainRangeMod ε n`) are supplied correctly at every use site.

---

## Mechanism Audit

- **Q1 — What does the target explicitly promise?**
  `P[χ(G(n,1/2)) − ζ(G(n,1/2)) ≥ n^{1−2ε}] ≥ 1 − 2ε` eventually in n, for any
  ε ∈ (0, 0.001), unconditionally on `InMainRange`.
- **Q2 — What does the mechanism actually guarantee?**
  Exactly the same statement, conditional on 4 paper axioms + 3 Lean kernel
  axioms. `#print axioms` verifies.
- **Q3 — Where does the stronger reading fail?**
  Two axioms have disclosed gaps versus "literal peer-reviewed citation":
  `lemma_7_20_modified` is HYBRID (own Lipschitz certificate);
  `zeta_alphaMinusTwo_upper_bound_whp` is an (α−1)→(α−2) extrapolation.
  Neither breaks the Lean proof, but both should be carried with their
  disclosures into the paper.
- **Q4 — Minimal fix set?**
  **P0**: none. **P1**: confirm `proof/proof.md` and `paper/main.tex` carry the
  HYBRID and α−2-extrapolation disclosures with the same framing as the Lean
  docstrings (per prior audit, this is already done).

---

## Routing Ledger

- **Route 1 (flagship statement & quantifier order)**: CLOSED. Verdict PASS.
- **Route 2 (rpow slack arithmetic)**: CLOSED. Verdict PASS.
- **Route 3 (case split + union bound)**: CLOSED. Verdict PASS.
- **Route 4 (threshold convention α−2 vs α−1)**: CLOSED. Verdict PASS.
- **Route 5 (axiom statement vs use site)**: CLOSED. Verdict PASS.
- **Route 6 (mechanism audit)**: CLOSED. Verdict PASS with 2 P1 disclosures.

---

## Final Verdict

**CLEAR FOR PUBLICATION.**

No P0 defects. 2 P1 findings, both already disclosed in Lean source.
3 P2 cosmetic notes. The proof of `Problem625.Publishable.erdos_625_full_clean`
is mechanically correct given its 4 stated paper axioms and 3 Lean kernel
axioms. The chain from flagship → `erdos_625_full` → (good branch via
`erdos_625_97` + `lemma_7_20_modified`) ∪ (crossing branch via 3 (α−2)
axioms + proved deterministic gap) is structurally sound and survives a
strict lemma-by-lemma adversarial walk. The union bound delivers `1 − 2ε`
exactly. The rpow slack `n^{1−ε} − 2·n^{0.99} ≥ n^{1−2ε}` is provable
eventually in n for the stated `ε ∈ (0, 0.001)` range.

**Build state**: GREEN.
**Axiom inventory**: matches package claim.
**Recommendation**: ship.

---

## Provenance

- **Generated**: 2026-05-11 / 2026-05-12 development window.
- **Worker model**: `claude-opus-4-7[1m]` (Claude Opus 4.7, 1M-context variant).
- **Operator orchestrator**: `operator` (https://github.com/uthunderbird/vibechord); codex-brain adapter ran `gpt-5.3-codex-spark` at `effort=low`.
- **Same-model caveat**: this artefact was produced by the same LLM-agent pipeline that produced the proof being critiqued; it is an **internal adversarial audit**, not a third-party review. LLM-generated proofs may exhibit plausibility-driven failure modes that survive same-model critique because the proof author and the critic share training-data blind spots. See `../../README.md` Provenance and `../../DEVELOPMENT.md` ADR-10 / ADR-11 / ADR-12 for the full methodology disclosure. External verification by an unrelated reader, a different model, or a human mathematician is encouraged.
- **Footer added**: round-2 publish-readiness repair, 2026-05-12 (P1-7).
