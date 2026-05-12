# Red Team Critique — `proof.md` (2026-05-12)

**Target document:** `proof/proof.md` (publish-package relative; originally cited as the absolute author-side path).
**Scope:** Adversarial audit of the published proof.md AS A WRITTEN DOCUMENT
(text-level claims), not the underlying Lean code (which has its own red-team
session at `red-team-erdos-625-full-2026-05-11.md`).

**Evidence base (read and grounded against):**
- `proof.md` (lines 1–279)
- `red-team/red-team-erdos-625-full-2026-05-11.md`
- `red-team/erdos-625-full-axiom-check-2026-05-11.md`
- `red-team/lemma-7-10-ext-disclosure-2026-05-11.md`
- `red-team/heckel2024-alpha-minus-two-transfer-audit-2026-05-11.md`
- `red-team/lemma_7_10_ext.md`
- `red-team/r2b-step1-results-2026-05-11.md`

## Verdict — document SURVIVES

**No P0 findings.** Six P1 findings of varying severity: one arithmetic
mis-claim that propagates from the source disclosure (F3), one numerical
exponent claim that is literally false at the worst-margin crossing n
(F1), and four disclosure-framing concerns (F2, F4, F5, F6).

None of the P1 findings invalidate the Lean theorem or the proof structure.
All P1 findings are addressable by editing prose in proof.md (and, for F3,
the upstream `lemma-7-10-ext-disclosure-2026-05-11.md` whose number proof.md
mirrors).

## Result typing

| ID | Severity | Type | Section |
|---|---|---|---|
| F1 | P1 | verified issue | Step 3 + Sub-spike audit item 2 |
| F2 | P1 | bounded concern | Step 2 heading "+1 paper axiom" |
| F3 | P1 | verified issue | Step 2 "6 orders-of-magnitude positivity margin" |
| F4 | P1 | verified issue | Statement intro + "Does establish" |
| F5 | P1 | bounded concern | "Does not establish" prize-bound item |
| F6 | P1 | bounded concern | "Does not establish" 12–24 month/axiom item |

## Findings

### F1 (P1, verified issue) — n^{1.65} sub-spike bound is false at the worst-margin crossing n

**Claim in proof.md (Step 3, lines 102–106 and Sub-spike audit item 2, lines 204–207):**
> "For μ_α ≥ 1 (the worst crossing case): μ_{α−2} ≥ Θ(n² / log²n) ≥ n^{1.65}
> for n ≥ 100 (numerically verified)."
> "μ_{α−2} = Θ(n²/log²n · μ_α) ≥ n^{1.65} for any crossing n, verified
> numerically over n ∈ [100, 10⁶]"

**Ground truth (`r2b-step1-results-2026-05-11.md`):**
- Worst-margin bad n is n = 108 with `x_{α−2} = 1.533244`, NOT ≥ 1.65.
- What R2B Step 1 actually verified is `x_{α−2}(n) ≥ 1.05` (the
  HP-2023 §8 application threshold) with min margin 0.483 over n ∈ [100, 10⁶].
- The "1.65–1.80" figure in the red-team R1 narrative is the SLOPE
  `x_{α−2} − x_α` at n ∈ {10⁷, …, 10¹²}, not the value `x_{α−2}`
  uniformly bounded below.

**Why this is P1 not P0:** the load-bearing application condition is
`μ_{α−2} ≥ n^{1.05}` (HP-2023 Lemma 8.1 §8 condition), which IS satisfied
with margin ≥ 0.48 for all n ∈ [100, 10⁶] and asymptotically n→∞.
Proof correctness depends on the n^{1.05} threshold, not on n^{1.65}.

**Fix:** replace "≥ n^{1.65}" with "≥ n^{1.05+δ} for some δ ≥ 0.48" or
simply "comfortably above HP-2023 §8's n^{1.05} application threshold,
with margin ≥ 0.48 verified at n ∈ [100, 10⁶]". The n^{1.65} figure can
be cited as the asymptotic slope, NOT as a uniform-in-n lower bound.

### F2 (P1, bounded concern) — "+1 paper axiom" phrasing in Step 2 heading

**Claim in proof.md (line 68):**
> "### Step 2 — `erdos_625_97` (97% n; +1 paper axiom)"

**Ground truth (`erdos-625-full-axiom-check-2026-05-11.md` table):**
`erdos_625_97` has **1** paper axiom total (`lemma_7_20_modified`),
having shed the 3 axioms of `erdos_625` and replaced them with the
single hybrid axiom. It is not "+1" relative to the 95% baseline;
it is a refactor that yields 1 axiom net.

A casual reader can interpret "+1" as monotone accumulation
(95% had 3, 97% has 4) which is incorrect.

**Fix:** rephrase to "1 paper axiom" or "1 hybrid paper axiom" without the
"+" sign. Mirror the table convention (column = absolute count).

(Analogously Step 3 "+3 paper axioms" is correct as an increment 1→4,
but it inherits the same ambiguity. The cleanest fix is consistent
absolute counts in all headings.)

### F3 (P1, verified issue) — "6 orders-of-magnitude positivity margin" is arithmetically inconsistent

**Claim in proof.md (Step 2, lines 88–92):**
> "It has a 6 orders-of-magnitude positivity margin (min ϕ ≈ 6.5 × 10⁻⁷
> on a 1086-cell grid with Lipschitz bound L = 7.49 × 10⁻³; envelope
> lower bound 6.15 × 10⁻⁷)."

**Ground truth (`lemma-7-10-ext-disclosure-2026-05-11.md`):**
> "Margin: `envelope_lb > 0` by **6 orders of magnitude** vs the
> `L · h / 2 ≈ 3.74×10⁻⁸` slack term."

Arithmetic check:
- envelope_lb / slack = 6.150 × 10⁻⁷ / 3.74 × 10⁻⁸ ≈ **16.4**
- log₁₀(16.4) ≈ **1.2** — not 6.
- envelope_lb itself is 6.15 × 10⁻⁷, i.e. ~6 in units of 10⁻⁷, but
  that is a sig-figure count, not "6 orders of magnitude above zero".

The "6 orders of magnitude" appears to be a number-misreading
(confusing the **leading digit** 6.15 with **6 orders**). The actual
envelope-to-slack ratio is roughly **1 order of magnitude (~16×)**.

**Why this is P1 not P0:** the envelope IS positive (6.15 × 10⁻⁷ > 0),
which is the only fact the proof requires. The "6 orders of magnitude"
phrasing inflates the apparent margin but does not affect the
mathematical conclusion. However, it propagates a quantitatively
**wrong claim** into a published proof.md and a red-team disclosure
artefact.

**Fix:** replace with "positivity margin of envelope_lb ≈ 6.15 × 10⁻⁷,
roughly 16× the Lipschitz slack L·h/2 ≈ 3.74 × 10⁻⁸ (i.e. ~1.2 orders
of magnitude)". Apply the same correction in
`lemma-7-10-ext-disclosure-2026-05-11.md`.

### F4 (P1, verified issue) — Borel–Cantelli a.s. step is in "Does establish" but is not in load-bearing Lean

**Claim in proof.md:**
- Statement (lines 19–20): "In particular χ(G) − ζ(G) → ∞ in
  probability (and a.s. by Borel–Cantelli with ε_n = 1/log n, modulo
  a routine Lean follow-up)."
- "Does establish" (lines 244–249): "Almost-sure convergence follows
  by Borel–Cantelli with ε_n = 1/log n (routine Lean follow-up)."

**Ground truth:** the Lean flagship theorem `erdos_625_full_clean`
proves a **fixed-ε** statement `P[χ − ζ ≥ n^{1−2ε}] ≥ 1 − 2ε`. To
upgrade to a.s. convergence one needs:
- Variable ε_n → 0 (e.g. 1/log n), AND
- A non-trivial verification that the Borel–Cantelli condition
  Σ P[bad_n] < ∞ holds with the chosen ε_n.

This is "routine" in the literature sense but **not** a
proof-script-trivial Lean step. It is not in the load-bearing
chain and not in the `#print axioms` budget. Per memory note
`p625-scope-clarification-2026-05-10.md`, the density-1 ≠ a.s.
distinction has historically been blurred in this repo; the prize
question literally asks "almost surely".

**Why this is P1 not P0:** the in-probability statement does answer
the Erdős–Gimbel question in spirit, and the Borel–Cantelli upgrade
is correctly flagged as a follow-up. But putting the a.s. claim in
"Does establish" while the Lean proof only delivers in-probability
is a presentation-vs-reality drift.

**Fix:** Move "a.s. by Borel–Cantelli" from "Does establish" to a
new "Does not yet establish in Lean" bullet OR explicitly label it
"(claimed; Lean proof in progress)". The parenthetical in the
statement is fine; the "Does establish" bullet should be tightened
to read "in probability" only.

### F5 (P1, bounded concern) — Prize / $100 bound gap not labeled as such

**Claim in proof.md (lines 252–253):**
> "The conjectural sharp rate of Heckel (Θ(n / log³n)) — our bound is
> n^{1-2ε}(1 + o(1)), much weaker than Heckel's conjecture."

**Ground truth:** the Erdős $100 question is for the **statement is
true**, which this proof addresses; the sharp rate Θ(n/log³n) is
Heckel's conjecture, not Erdős's. The user-supplied context flags
the prize-bound gap as a key disclosure item. proof.md is honest
about the rate gap but doesn't relate it to the prize structure.

**Fix:** optional — add one sentence: "Note: the Erdős $100 question
asks for the *existence* of unbounded gap (which this proof
delivers); the sharp Θ(n/log³n) rate is a separate Heckel
conjecture and is out of scope."

### F6 (P1, bounded concern) — "12–24 months per axiom" is a fabricated per-axiom inflation

**Claim in proof.md (lines 261–262):**
> "estimated at 12–24 months per axiom for the Lemma 7.20 / 8.1 / Prop 5(b)
> machinery."

**Ground truth (`erdos-625-full-axiom-check-2026-05-11.md` line 125):**
> "estimated at 12–24 months of formalization effort per the 2026-05-10
> roadmap."

The axiom-check source gives one global estimate. proof.md silently
converts this to **per-axiom**, multiplying total effort by 4×. There
is no roadmap citation supporting per-axiom granularity.

**Why this is P1 not P0:** estimates of formalization effort are
necessarily fuzzy; over-stating is pessimistic, not deceptive in
direction. But "per axiom" is a fabricated number.

**Fix:** replace "12–24 months per axiom" with "12–24 months total
for the Lemma 7.20 / 8.1 / Prop 5(b) machinery (per the 2026-05-10
roadmap)".

## Mechanism Audit

1. **What does the proof.md explicitly promise?**
   A Lean-machine-checked proof of `χ−ζ ≥ n^{1−2ε}` whp ≥ 1−2ε for all
   sufficiently large n and ε ∈ (0, 0.001); 4 paper axioms + 3 kernel
   axioms; honest P1-A / P1-B disclosures of the two non-purely-paper-backed
   axioms; positively answers the Erdős–Gimbel question.

2. **What does the mechanism (the prose) actually guarantee?**
   - The four theorem claims match the Lean theorem statements per the
     axiom-check artefact (consistent).
   - The axiom inventory table (7 entries, 4 paper + 3 kernel, no sorryAx)
     matches the literal `#print axioms` output recorded in the axiom-check
     note (consistent).
   - The P1-A / P1-B disclosures (Step 2 / Step 3 "Honest disclosure"
     blocks) preserve the substance of the upstream disclosure artefacts
     (consistent in framing).
   - The spike-bug audit reproduction (Sub-spike audit section) matches
     R1–R6 of `red-team-erdos-625-full-2026-05-11.md` (consistent, modulo F1).

3. **Where does the stronger reading fail?**
   - F1: numerical exponent (n^{1.65}) is a slope, not a uniform bound;
     the load-bearing condition is the (correct) n^{1.05} threshold.
   - F3: "6 orders of magnitude" is arithmetically off by a factor of ~5
     in log space.
   - F4: a.s. convergence is in "Does establish" but not in the load-bearing
     Lean chain.
   - F2, F5, F6: framing inflations or under-clarifications.

4. **Minimal fix set:**
   - **P0:** none.
   - **P1:** apply F1, F3, F4 corrections (substantive numeric / scope
     fixes); F2, F5, F6 are stylistic and may be deferred.

## Checks the master agent requested — explicit verdicts

1. **Four theorems characterized correctly?** YES, modulo F2 (the "+1 / +3"
   heading convention is colloquial; the table itself is correct).
2. **Axiom inventory accurate vs `#print axioms`?** YES — proof.md table
   (4 paper + 3 kernel = 7 entries) matches the literal output recorded
   in `erdos-625-full-axiom-check-2026-05-11.md`.
3. **P1 disclosures honestly framed?** Mostly YES. P1-A and P1-B have
   substantive disclosure blocks in Step 2 and Step 3. F3 (the "6 orders
   of magnitude" inflation) is the one substantive disclosure error,
   inherited from the upstream P1-A disclosure note.
4. **Sleight-of-hand overclaim of coverage / exponent / peer review?**
   No coverage overclaim (95/97/100/100 matches artefacts).
   F1 is an exponent mis-statement (n^{1.65} vs n^{1.05+margin}); not a
   coverage overclaim but a numerical mis-quote.
   No peer-review overclaim — "Heckel 2024 §Discussion explicitly
   conjectures the underlying fact" (Step 2) and "not literally a
   one-citation paper-backed axiom" (Step 3) are honest framings.
5. **"Does not establish" honest re: prize bound and 0-axiom proof?**
   Mostly YES: rate gap (n vs n/log³n) and 4 paper axioms are listed.
   GAPS: a.s. convergence (F4) is in "Does establish" but should be in
   "Does not yet establish in Lean"; per-axiom 12–24 month inflation (F6).
6. **Spike-bug audit reproduction correct?** YES on decidability,
   exhaustiveness, no third regime, no sub-spike at α−2 (qualitatively).
   F1 (the specific numeric n^{1.65} claim) is the one quantitative
   correction needed within this section.

## Route trace

| Route | Concern | Verdict |
|---|---|---|
| R-claims | Cross-walk of all 17 substantive claims | CLOSED — 11 consistent, 6 P1 (F1–F6) |
| R-mechanism | Promise vs. guarantee | CLOSED — no P0 |
| R-spike-bug | Audit reproduction faithfulness | CLOSED — faithful modulo F1 |
| R-prize | $100 / a.s. scope | CLOSED — F4 disclosure tightening recommended |

## Termination

Per `red-team-overrides.md` and the master-agent contract, the document
**survives** with **no P0 findings**. Six P1 findings are listed above
with specific fix recommendations. The main agent may apply F1, F3, F4
(substantive) immediately and defer F2, F5, F6 (stylistic).

The Lean proof itself remains GREEN and prize-eligible-in-probability
modulo the cited disclosures.

## Artefact provenance

- Red-team session: 2026-05-12.
- Inputs read: proof.md and all six artefacts in `red-team/` (see Evidence
  base above).
- No Lean execution this session; ground truth is the literal
  `#print axioms` output recorded in `erdos-625-full-axiom-check-2026-05-11.md`
  line 50–57.

---

## Provenance

- **Generated**: 2026-05-11 / 2026-05-12 development window.
- **Worker model**: `claude-opus-4-7[1m]` (Claude Opus 4.7, 1M-context variant).
- **Operator orchestrator**: `operator` (https://github.com/uthunderbird/vibechord); codex-brain adapter ran `gpt-5.3-codex-spark` at `effort=low`.
- **Same-model caveat**: this artefact was produced by the same LLM-agent pipeline that produced the proof being critiqued; it is an **internal adversarial audit**, not a third-party review. LLM-generated proofs may exhibit plausibility-driven failure modes that survive same-model critique because the proof author and the critic share training-data blind spots. See `../../README.md` Provenance and `../../DEVELOPMENT.md` ADR-10 / ADR-11 / ADR-12 for the full methodology disclosure. External verification by an unrelated reader, a different model, or a human mathematician is encouraged.
- **Footer added**: round-2 publish-readiness repair, 2026-05-12 (P1-7).
