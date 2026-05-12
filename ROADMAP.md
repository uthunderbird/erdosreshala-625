# Publication Roadmap

This document tracks the state of the formalization and the path to a
fully verified, peer-reviewable publication.

**Last update**: 2026-05-12 (post-flagship-rewrite).

---

## Current state

| Theorem | Status | Coverage | Axioms |
|---|---|---|---|
| `erdos_625` | ✅ proved | $\sim 95\%$ n (InMainRange) | 3 paper + 3 kernel |
| `erdos_625_97` | ✅ proved | $\sim 97\%$ n (InMainRangeMod) | 1 paper + 3 kernel |
| `erdos_625_full` | ✅ proved | $100\%$ n, bound $n^{1-\varepsilon}-2n^{0.99}$ | 4 paper + 3 kernel |
| **`erdos_625_full_clean`** | ✅ proved | $\boldsymbol{100\%}$ n, bound $\boldsymbol{n^{1-2\varepsilon}}$ | 4 paper + 3 kernel |

`lake build` GREEN (2925 jobs). `#print axioms erdos_625_full_clean`
returns exactly the 7 entries; **0 `sorryAx` on the proof path** of
`erdos_625_full_clean`. (Seven literal `sorry` tokens remain in
`private` helper lemmas in non-reachable supporting modules —
`PartBProfileBridge.lean` ×5, `ChromaticConnection.lean` ×1,
`ZetaConcentration.lean` ×1 — none reachable from any of the four
publishable theorems.) Five internal adversarial-audit passes (same
LLM-agent pipeline; Lean theorem, `proof.md`, `paper/main.tex` ×2,
strict lemma-by-lemma), all 0 P0 in their respective rounds. Per-axiom
paper-correspondence audit 2026-05-12.

See [Disclosure summary](#disclosure-summary) below for prize, LLM
provenance, and shared-blind-spot caveats; the full canonical
disclosure stack is in `README.md` § Caveats.

---

## Honest scope limitations (carry into any preprint)

1. **Almost-sure convergence ("for all large n")** — the literal
   Erdős–Gimbel question and the form the \$100 prize is offered for.
   Our fixed-$\varepsilon$ in-probability bound can be promoted to
   a.s. via a Borel–Cantelli / diagonal-subsequence argument, but the
   step is **not trivial** (direct BC-1 with $\varepsilon_n=1/\log n$
   fails, $\sum 2/\log n$ diverges; a subsequence-plus-monotonicity or
   coupling argument is required) and is not yet in Lean. See §N1.
   The in-probability corollary (the $\varepsilon\to 0$ limit of the
   per-$\varepsilon$ Lean theorem) is also not in the Lean chain
   itself, though it is a one-line measure-theoretic step.
2. **Heckel's conjectured sharp rate** $\Theta(n/\log^3 n)$. Our
   $n^{1-2\varepsilon}$ is strictly weaker.
3. **Hybrid axiom #1** (`lemma_7_20_modified`): combines HP-2023
   Lemma 7.20 with our in-repository numerical certificate
   `lemma_7_10_ext` (1086-cell grid, $\sim 1.2$ orders of magnitude
   positivity margin). Heckel 2024 §Discussion explicitly conjectures
   the underlying fact. See `proof/red-team/lemma-7-10-ext-disclosure-2026-05-11.md`.
4. **Extrapolation axiom #4** (`zeta_alphaMinusTwo_upper_bound_whp`):
   Heckel 2024 Prop 5(b) at $\alpha-1$, transferred to $\alpha-2$ via
   HP-2023's general-$a$ second-moment lemmas. Not a literal one-citation
   paper axiom. See `proof/red-team/heckel2024-alpha-minus-two-transfer-audit-2026-05-11.md`.

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
truncated-series arithmetic. Closes the P1-A disclosure.

### N3. Formalize the $(\alpha-2)$-version of Heckel 2024 Prop 5(b) (~2–3 months math + Lean)

Write out the explicit $(\alpha-2)$-bounded second-moment chain by
specializing HP-2023's general-$a$ second-moment lemmas (Lemmas 6.3–6.5
in HP-2023). This closes the P1-B disclosure: axiom #4 becomes a
literal one-citation paper axiom plus a finite multinomial-coefficient
specialization, no extrapolation needed.

### N4. Sharper rate / approach to Heckel's conjecture (open math)

Heckel 2024 conjectures $\chi-\zeta = \Theta(n/\log^3 n)$. The current
proof's $n^{1-2\varepsilon}$ rate is much weaker; a sharp bound requires
new ideas beyond what this repository contains. Not a formalization
project; an open mathematical question.

### N5. Reachability-based deletion of unused infrastructure (~1–2 weeks Lean)

`PartBProfileBridge.lean` (29 K LOC) carries substantial supporting
infrastructure, only part of which is reachable from
`erdos_625_full_clean`. A careful reachability analysis could delete
sub-trees that are only used by the legacy `erdos_625` chain (which is
itself superseded by `erdos_625_97`/`erdos_625_full_clean`). Pure
cleanup, no math change.

---

## Build prerequisites and reproducibility

- `lean-toolchain`: `leanprover/lean4:v4.29.0-rc8`
- `lake-manifest.json` pins Mathlib4 at the matching revision.
- `lake exe cache get` + `lake build` should give GREEN in ~5 minutes
  on a fresh checkout with internet access.
- `proof/AXIOM_SNAPSHOT.txt` commits the verbatim
  `#print axioms erdos_625_full_clean` output captured against the
  pinned toolchain on 2026-05-12; a fresh clone should reproduce it
  byte-identically (modulo whitespace).
- `proof/red-team/` carries the numerical certificate scripts
  (`num-gap-lemma710-extension-2026-05-10.py`, `r2b_step1_scan.py`).
  Each is reproducible via `python3 <script>`.
- Local agent harness dumps are intentionally not shipped in this
  publication package; the methodology and cross-model-auditing caveats
  are summarized in `README.md`, `DEVELOPMENT.md`, and `paper/main.tex`.
- A CI workflow (`.github/workflows/build.yml`) running `lake build`
  on each push is **committed**; see the workflow file at the
  repository root.

---

## Paper length note

The companion paper `paper/main.tex` is ~8–10 pp — at the short end of
arXiv math.PR conventions for results of this scope. This is a
deliberate choice: clarity and tight axiom-to-paper correspondence have
been prioritized over expansion. Readers wanting the full step-by-step
derivation should consult `proof/proof.md` (Markdown writeup) and the
Lean source under `Erdos625/` directly; the paper is intended as the
peer-reviewable summary, not as the verbose walkthrough.

---

## Disclosure summary

(Full canonical disclosure stack lives in `README.md` § Caveats. The
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
**not trivial** — a direct application of Borel–Cantelli 1 to the
events $\{\chi - \zeta < n^{1-2\varepsilon_n}\}$ with
$\varepsilon_n = 1/\log n$ does **not** work ($\sum 2/\log n$
diverges); the actual upgrade needs a subsequence + monotonicity
argument or a coupling step. See §N1 above.

This formalization and all five red-team audit passes were produced by
an LLM-agent pipeline (Anthropic Claude Opus 4.7, model id
`claude-opus-4-7[1m]`, the 1M-context variant, plus the `operator`
agent orchestrator at
[https://github.com/uthunderbird/vibechord](https://github.com/uthunderbird/vibechord)
whose codex-brain adapter ran `gpt-5.3-codex-spark` at `effort=low`)
under human supervision. The audits are internal, not third-party. The
1M-context variant was load-bearing: `PartBProfileBridge.lean` is
29512 lines (~1.59 MB).
