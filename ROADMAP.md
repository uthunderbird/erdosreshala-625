# Publication Roadmap

This document tracks the state of the formalization and the path toward a
fully verified, peer-reviewable publication.

**Last update**: 2026-05-17 (all three branches discharged to paper-cited axioms in `erdos625_low_discharged`; see §Analytical wrapper status).

---

## Contents

1. [Current state](#current-state)
2. [Analytical wrapper status (not Lean-certified)](#analytical-wrapper-status-not-lean-certified)
3. [Honest scope limitations](#honest-scope-limitations-carry-into-any-preprint)
4. [Optional next-step projects](#optional-next-step-projects)
5. [Build prerequisites and reproducibility](#build-prerequisites-and-reproducibility)
6. [Paper length note](#paper-length-note)
7. [Disclosure summary](#disclosure-summary)

---

## Current state

| Theorem | Status | Coverage | Axioms |
|---|---|---|---|
| `erdos_625` | ✅ proved | $\sim 95\%$ n (InMainRange) | 3 paper + 3 kernel |
| `erdos_625_97` | ✅ proved | $\sim 97\%$ n (InMainRangeMod) | 1 paper + 3 kernel |
| `erdos_625_full` | ✅ proved | $100\%$ n, bound $n^{1-\varepsilon}-2n^{0.99}$ | 4 paper + 3 kernel |
| **`erdos_625_full_clean`** | ✅ proved | $\boldsymbol{100\%}$ n, bound $\boldsymbol{n^{1-2\varepsilon}}$ | 4 paper + 3 kernel |

*Axioms A1 and A4 have disclosure caveats; see §Honest scope limitations below.*

`lake build` GREEN (approximately 2925 jobs). `#print axioms erdos_625_full_clean`
returns exactly the 7 entries; **0 `sorryAx` on the proof path** of
`erdos_625_full_clean`.  The former non-reachable helper placeholders in
`PartBProfileBridge.lean`, `ChromaticConnection.lean`, and
`ZetaConcentration.lean` have been converted to named source seams tracked by
source-axiom snapshots; they are not local proof placeholders. (A 'source seam' is a named axiom declaration tracking an admitted mathematical fact from a published paper; a 'local proof placeholder' is an internal `sorry` used during development. Source seams remain in the final build by design; sorry-based placeholders do not.) Five internal adversarial-audit passes (same
LLM-agent pipeline; Lean theorem, `proof.md`, `paper/main.tex` ×2,
strict lemma-by-lemma), all zero Priority-0 (blocking) in their respective rounds. A per-axiom paper-correspondence audit was performed on 2026-05-12 by the same LLM-agent pipeline.

See [Disclosure summary](#disclosure-summary) below for prize, LLM
provenance, and LLM-pipeline shared-blind-spot limitations (see §Disclosure summary); the full canonical
disclosure stack is in `README.md` §Lean boundary and §Lemma and axiom source audit.

## Analytical wrapper status

`Erdos625.AnalyticalWrapper` exposes two theorems proving the same statement
(gnHalf n (analyticalGapEvent n) → 1):

**`erdos_625_full_analytical_of_source_obligations`**: the original dependency-closure
interface. Not Lean-certified: depends on three bridge-shaped WHP obligations
(`lowBranchGapWHPAxiom`, `good_branch_partial_away_from_one_loglog_whp_of_bridge_inputs`,
`upper_boundary_r2_integrated_loglog_whp_of_bridge_inputs`).

**`erdos625_low_discharged`** (added 2026-05-17): all three bridge obligations are
replaced by paper-cited axiom leaves — no bridge-shaped axioms remain in its dependency
chain. The four paper-cited leaves are:
- `paperLowBranchChiLower_source` — HP-2023 Lemma 8.1 (chromatic lower bound)
- `paperLowBranchZetaUpper_source` — HP-2023 Co. 39 + Le. 7.4 + Heckel 2024
  lines 514–516 + Markov (first-moment/Markov cochromatic upper bound; no C5)
- `middleBranchCrossingComplementWHPAxiom` — HP-2023 §7+§8, Heckel 2024 §3–7
- `upperBranchPaperWHPAxiom` — HP-2023 Thm 1 + §4 Le. 4.1 + §7 + Appendix;
  Heckel–Riordan 2023 Le. 44

The wiring from axioms to the final theorem is fully proved in Lean
(`lowBranchWHP_of_paper_axioms`, `erdos625_low_discharged`).

**2026-05-15 update**: The low-branch (Regime I, `x ∈ [0, 0.029155]`) source argument was
revised from the C5-based source note to the first-moment (Markov) method using HP-2023
Le. 7.4, Le. 7.3, Le. 8.1, and Heckel 2024 line 516. The prior C5-based source is
superseded and no longer used in the proof.

See `proof/ANALYTICAL_WRAPPER_AXIOM_SNAPSHOT.txt` for the full axiom snapshot.

---

## Honest scope limitations (carry into any preprint)

1. **Almost-sure convergence ("for all large n")** — the literal
   Erdős–Gimbel question and the form the \$100 prize is offered for.
   Our fixed-$\varepsilon$ in-probability bound can be promoted to
   a.s. via a Borel–Cantelli / diagonal-subsequence argument, but the
   step is **not trivial** (direct BC-1 with $\varepsilon_n=1/\log n$
   fails, $\sum 2/\log n$ diverges; a subsequence-plus-monotonicity or
   coupling argument is required) and is not yet in Lean. See the N1 section below.
   The in-probability corollary (the $\varepsilon\to 0$ limit of the
   per-$\varepsilon$ Lean theorem) is also not in the Lean chain
   itself, though it is a one-line measure-theoretic step.
2. **Heckel's conjectured sharp rate** $\Theta(n/\log^3 n)$. Our
   $n^{1-2\varepsilon}$ is strictly weaker.
3. **Hybrid axiom #1** (`lemma_7_20_modified`): combines HP-2023
   Lemma 7.20 with our in-repository numerical certificate
   `lemma_7_10_ext` (1086-cell grid, $\sim 1.2$ orders of magnitude
   positivity margin). Heckel 2024 §Discussion explicitly conjectures
   the underlying fact. (Numerical certificate scripts are not shipped in this publish package; see ADR-12 in `DEVELOPMENT.md` for background.)
4. **Extrapolation axiom #4** (`zeta_alphaMinusTwo_upper_bound_whp`):
   Heckel 2024 Prop 5(b) at $\alpha-1$, transferred to $\alpha-2$ via
   HP-2023's general-$a$ second-moment lemmas. Not a literal one-citation
   paper axiom. (See ADR-11 in `DEVELOPMENT.md` for the extrapolation authorship breakdown.)

Axioms #2 (`partB_alphaMinusTwo_firstMomentBelowOne_source`) and
#3 (`chi_alphaMinusTwo_lower_bound_whp`) are literal HP-2023 citations.

---

## Optional next-step projects

These are tracked as future work, not as blockers for the current
submission. Each is independent.

### N1. Almost-sure upgrade (open measure-theoretic work)

Prove $\chi(G_{n,1/2})-\zeta(G_{n,1/2}) \to \infty$ almost surely
(for all large $n$) from the existing fixed-$\varepsilon$ bound. This
is **not** a one-line application of Borel–Cantelli: with the
natural choice $\varepsilon_n = 1/\log n$ the series $\sum 2/\log n$
diverges, so Borel–Cantelli 1 does not directly close the gap. The
upgrade requires either (i) a subsequence-plus-monotonicity argument
(pick a subsequence $n_k$ on which $\varepsilon_{n_k}$ is bounded
away from $0$ in segments and combine with monotonicity of
$\chi-\zeta$ along the subsequence) or (ii) a coupling argument that
yields independence across $n$ for the bad events, allowing BC-2.
Either route is non-trivial measure-theoretic / random-graph work,
not just a Lean translation of a textbook proof. Estimated effort:
several weeks of math plus Lean formalization. Also includes
formalizing the simpler $\varepsilon \to 0$ in-probability corollary,
which is also currently absent from the Lean chain.

### N2. Formalize `lemma_7_10_ext` numerical certificate (~4–8 weeks Lean)

Replace the hybrid status of axiom A1 by a Lean-internal proof. The
certificate is a $\varphi$-positivity statement on a finite grid plus
a Lipschitz envelope; doable via `decide` on rationals after careful
truncated-series arithmetic. Closes the hybrid-axiom (A1) disclosure gap.

### N3. Formalize the $(\alpha-2)$-version of Heckel 2024 Prop 5(b) (~2–3 months math + Lean)

Write out the explicit $(\alpha-2)$-bounded second-moment chain by
specializing HP-2023's general-$a$ second-moment lemmas (Lemmas 6.3–6.5
in HP-2023). This closes the extrapolation-axiom (A4) disclosure gap: axiom #4 becomes a
literal one-citation paper axiom plus a finite multinomial-coefficient
specialization, no extrapolation needed.

### N4. Sharper rate / approach to Heckel's conjecture (open math)

Heckel 2024 conjectures $\chi-\zeta = \Theta(n/\log^3 n)$. The current
proof's $n^{1-2\varepsilon}$ rate is much weaker; a sharp bound requires
new ideas beyond what this repository contains. Not a formalization
project; an open mathematical question.

### N5. Reachability-based deletion of unused infrastructure (~1–2 weeks Lean)

`PartBProfileBridge.lean` (~29.6 K lines (29597)) carries substantial supporting
infrastructure, only part of which is reachable from
`erdos_625_full_clean`. A careful reachability analysis could delete
sub-trees that are only used by the legacy `erdos_625` chain (which is
itself superseded by `erdos_625_97`/`erdos_625_full_clean`). No changes to the underlying mathematical argument.

---

## Build prerequisites and reproducibility

- `lean-toolchain`: `leanprover/lean4:v4.29.0-rc8`
- `lake-manifest.json` pins Mathlib4 at the matching revision.
- `lake exe cache get` + `lake build` should give GREEN in ~5 minutes
  on a fresh checkout with internet access.
- The axiom snapshot for `erdos_625_full_clean` is **not separately committed**
  in this package as a standalone file.  To reproduce it, run
  `#print axioms Problem625.Publishable.erdos_625_full_clean` in a local
  Lean build against the pinned toolchain.  The axiom snapshot for the
  analytical wrapper is committed as
  `proof/ANALYTICAL_WRAPPER_AXIOM_SNAPSHOT.txt`.
- Numerical certificate scripts (`num-gap-lemma710-extension-2026-05-10.py`,
  `r2b_step1_scan.py`) are **not shipped** in this publish package.
  The methodology is described in `DEVELOPMENT.md` ADR-11 and ADR-12.
- Local agent harness dumps are intentionally not shipped in this
  publication package; the methodology and cross-model-auditing caveats
  are summarized in `README.md`, `DEVELOPMENT.md`, and `paper/main.tex`.
- A CI workflow (`.github/workflows/build.yml`) running `lake build`
  on each push is **committed** and is currently passing on the repository's default branch; see the workflow file at the
  repository root.

---

## Paper length note

The companion paper `paper/main.tex` is 8–10 pp (range reflects LaTeX compilation options and bibliography style variations) — at the short end of
arXiv math.PR conventions for results of this scope. This is a
deliberate choice: clarity and tight axiom-to-paper correspondence have
been prioritized over expansion. Readers wanting the full step-by-step
derivation should consult `proof/proof.md` (Markdown writeup) and the
Lean source under `Erdos625/` directly; the paper is intended as the
peer-reviewable summary, not as the verbose walkthrough.

---

## Disclosure summary

(Full canonical disclosure stack lives in `README.md` §Lean boundary and §Lemma and axiom source audit. The
condensed form here is for readers who arrived via `ROADMAP.md`
directly.)

This work does **not** claim the Erdős \$100 prize for Problem 625.
The prize is for an affirmative proof of
$\chi(G) - \zeta(G) \to \infty$ **almost surely** as $n \to \infty$;
the flagship Lean theorem `erdos_625_full_clean` establishes the
strictly weaker **in-probability** form (in fact the per-$\varepsilon$
quantitative form, of which "in probability" is the $\varepsilon \to 0$
corollary; the corollary itself is also not in the Lean chain). The
almost-sure upgrade requires a Borel–Cantelli-style argument that is
**not trivial**. See §N1 (Almost-sure upgrade) above for the Borel–Cantelli obstruction detail.

This formalization and all five red-team audit passes were produced by
an LLM-agent pipeline under human supervision; the audits are internal, not
third-party. The pipeline used Anthropic Claude Opus 4.7 (`claude-opus-4-7[1m]`,
1M-context variant; **note**: this model identifier may not be publicly verifiable
at time of reading), orchestrated by the `operator` agent at
[https://github.com/uthunderbird/vibechord](https://github.com/uthunderbird/vibechord)
whose codex-brain adapter ran `gpt-5.3-codex-spark` at `effort=low`
(**note**: internal codename, may not correspond to a publicly documented model
version). The 1M-context variant was load-bearing:
`PartBProfileBridge.lean` is 29597 lines (~1.59 MB). See ADR-10 in
`DEVELOPMENT.md` for full provenance details.
