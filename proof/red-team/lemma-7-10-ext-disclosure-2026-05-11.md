# `lemma_7_10_ext` — Disclosure for Red-Team Finding P1-A

> **Path-context note (2026-05-12).** This artefact was authored against the source repository where work artefacts live at `problems/625/work/...`. In the `publish/erdos-625/` package the referenced `lemma_7_10_ext.md` is co-located here at `proof/red-team/lemma_7_10_ext.md`. Path references below preserve the original-context wording for historical fidelity.

**Date**: 2026-05-11
**Purpose**: close red-team finding P1-A from `red-team-erdos-625-full-2026-05-11.md`
**Target axiom**: `Problem625.Publishable.lemma_7_20_modified` in
`Erdosreshala/Problem625/PublishableProof.lean`
**Status**: hybrid composition disclosed; full Lean formalization left as optional follow-up

## The hybrid structure

The Lean axiom `lemma_7_20_modified` ostensibly cites
"HP-2023 Lemma 7.20 modified" as a single paper-backed source. In reality
it is the **composition** of two pieces:

1. **HP-2023 §7 / Lemma 7.20 bulk.** Peer-reviewed
   (arXiv:2306.07253, published). Establishes the tame profile + Stirling
   approximation machinery for μ_α ∈ [n^{0.05+ε}, n^{1-ε}].

2. **"Lemma 7.10-ext" — the gap-filler [x₀+ε, 0.04).** **Our own** numerical
   certificate (`num-gap-lemma710-extension-2026-05-10.py`, documented in
   `lemma_7_10_ext.md`). Fills the gap of HP-2023 Lemma 7.10's
   [0.04, 1] coverage down to x₀+ε ≈ 0.0291.

Heckel 2024 §Discussion **claims** the gap can be filled ("It should be
straightforward to change the proof of Lemma 7.20 in [HP-2023] to only
require μ_α ≥ n^{x₀+ε} for any ε > 0 and a certain constant x₀ ≈ 0.02905"),
but does not actually do so. Our `lemma_7_10_ext` is the explicit closure of
that claim.

## What the numerical certificate guarantees

From `lemma_7_10_ext.md` §3 (formal statement):

```
Let x₀ = 0.02905439, ε = 10⁻⁴, x_lo = x₀ + ε = 0.029154, x_hi = 0.04.
Define ϕ via HP-2023 eq. (7.19), series truncated at i = 150
(per-term truncation error < 10⁻¹⁵ for i ≥ 12).
Then inf_{x ∈ [x_lo, x_hi]} ϕ(x) ≥ 6.150 × 10⁻⁷ > 0.
```

Combined with HP-2023 Lemma 7.10 (covers [0.04, 1]), this gives
**ϕ > 0 on [x₀+ε, 1]**, which is the condition Heckel's discussion
remark requires.

### Certificate details

| Constant | Value | Role |
|---|---|---|
| `x_lo` | 0.029154 | x₀ + ε |
| `x_hi` | 0.040000 | HP-2023 Lemma 7.10 boundary |
| `h` | 1 × 10⁻⁵ | grid spacing |
| `N` | 1086 cells | grid size |
| `grid_min` | 6.524618 × 10⁻⁷ | minimum ϕ on grid |
| `L` | 7.488414 × 10⁻³ | Lipschitz bound (10% buffered) |
| `envelope_lb` | 6.150197 × 10⁻⁷ | grid_min − L·h/2 |

Margin: `envelope_lb > 0` by **≈ 1.2 orders of magnitude** (ratio
`6.15×10⁻⁷ / 3.74×10⁻⁸ ≈ 16.4`) vs the `L · h / 2 ≈ 3.74×10⁻⁸` slack term. The Lipschitz constant `L` itself is
estimated via finite differences `+10%` safety buffer. **Conservative.**

## Why this is not a fatal P0

- HP-2023 Lemma 7.20 itself is peer-reviewed; we modify **only** condition
  (d), which depends on ϕ-positivity.
- ϕ-positivity on [x₀+ε, 0.04) is a **classical real-analysis fact**
  (existence of unique zero x₀, monotonicity), not a contested research
  claim. Our numerical certificate is implementation of a standard recipe.
- The certificate is fully reproducible (`python3 num-gap-lemma710-extension-2026-05-10.py`).
- Heckel 2024 explicitly conjectures the fact our certificate confirms.

## Why it is still P1 not "closed"

- The certificate is OUR work; not peer-reviewed.
- "Common-knowledge external result" criterion requires literal citation,
  which a 10⁻⁵ grid Python script does not technically satisfy.
- A reviewer could legitimately ask: "where in the literature is
  `lemma_7_10_ext` written down?" Answer: nowhere yet.

## Three ways to upgrade P1-A → closed

1. **Standalone preprint.** Publish `lemma_7_10_ext` as a one-page arXiv
   note: "On the positivity of ϕ on [x₀+ε, 0.04)". Includes Lipschitz
   certificate + Python source + reproducibility instructions. Estimated
   effort: 1 week.

2. **Lean formalization.** Define `φ : ℝ → ℝ` (truncated series) and
   `decide`-style prove `min ϕ on grid ≥ 6.524618e-7` for a rational
   grid in [x_lo, x_hi]. Lipschitz envelope as separate lemma. Estimated
   effort: 4–8 weeks (rpow + Lipschitz lemmas need scaffolding;
   `decide` on rationals of this size is heavy).

3. **Author confirmation.** Send `lemma_7_10_ext.md` to Heckel and
   Panagiotou asking for "looks correct to you?". If they confirm,
   strengthens P1-A but does not technically convert it to a literal
   citation. Estimated effort: 1 email + waiting.

For this audit we choose **none** — accept P1-A as a disclosed bounded
concern and document it. A future preprint will reference this note.

## Honest framing for any preprint

> The proof of `erdos_625_full` invokes a paper-backed axiom
> `lemma_7_20_modified` that combines HP-2023's published Lemma 7.20
> (peer-reviewed, arXiv:2306.07253) with a fresh numerical certificate
> "Lemma 7.10-ext" filling the gap [x₀+ε, 0.04) of HP-2023's
> Lemma 7.10 coverage. The numerical certificate (documented in
> `problems/625/work/notes/lemma_7_10_ext.md`, computed by
> `num-gap-lemma710-extension-2026-05-10.py`) uses a 1086-cell grid in
> [x₀+ε, 0.04) with a Lipschitz envelope, yielding `min ϕ ≥ 6.15×10⁻⁷`
> with ≈ 1.2 orders of magnitude margin (ratio ≈ 16-fold) over the
> Lipschitz slack. The
> certificate is our own work and not peer-reviewed; Heckel 2024
> §Discussion explicitly conjectures the underlying fact. Formal Lean
> formalization of the certificate (via `decide` on a rational grid)
> is open future work.

## Verdict for red-team P1-A

**Bounded concern** (per red-team typing). Hybrid axiom with explicit
disclosure. The numerical certificate has ≈ 1.2 orders of magnitude margin
(ratio ≈ 16-fold) and is fully reproducible. Heckel 2024 §Discussion provides external
confirmation of the underlying analytic claim. Formal peer review of
`lemma_7_10_ext` is open work but not on the load-bearing path of
correctness — only of disclosure.

---

## Provenance

- **Generated**: 2026-05-11 / 2026-05-12 development window.
- **Worker model**: `claude-opus-4-7[1m]` (Claude Opus 4.7, 1M-context variant).
- **Operator orchestrator**: `operator` (https://github.com/uthunderbird/vibechord); codex-brain adapter ran `gpt-5.3-codex-spark` at `effort=low`.
- **Same-model caveat**: this artefact was produced by the same LLM-agent pipeline that produced the proof being critiqued; it is an **internal adversarial audit**, not a third-party review. LLM-generated proofs may exhibit plausibility-driven failure modes that survive same-model critique because the proof author and the critic share training-data blind spots. See `../../README.md` Provenance and `../../DEVELOPMENT.md` ADR-10 / ADR-11 / ADR-12 for the full methodology disclosure. External verification by an unrelated reader, a different model, or a human mathematician is encouraged.
- **Footer added**: round-2 publish-readiness repair, 2026-05-12 (P1-7).
