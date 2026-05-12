# Erdős Problem 625 — Lean 4 Formalization

A Lean 4 machine-checked proof that in the Erdős–Rényi random graph
$G(n,1/2)$, for every $\varepsilon \in (0, 0.001)$ and all sufficiently
large $n$,
$\Pr[\chi(G) - \zeta(G) \ge n^{1-2\varepsilon}] \ge 1 - 2\varepsilon$.

**Caveats at a glance:** this is an LLM-agent-generated formalization
(Anthropic Claude Opus 4.7, 1M-context); it admits **4 paper-backed
axioms** (2 literal HP-2023 citations + 1 HP-2023 hybrid + 1 Heckel-2024
extrapolation); it proves the **in-probability** form only (not
almost-sure); the five internal red-team passes were run by the same
LLM-agent pipeline and are not third-party reviews; this work does
**not** claim the Erdős \$100 prize. See [Caveats](#caveats) for the
full disclosures.

## Quick links

- [Flagship theorem](#flagship-theorem) — the per-ε bound
- [Four theorems (coverage hierarchy)](#four-theorems-coverage-hierarchy)
- [Axiom inventory](#axiom-inventory) — the 7 entries (4 paper + 3 kernel)
- [How to verify](#building-and-verifying) — `lake exe cache get` + `lake build`
- [Caveats](#caveats) — prize, LLM provenance, hybrid axioms, scope
- [References](#references)
- [Red-team audit trail](proof/red-team/README.md)

**Proof status**: complete on the in-probability form.
`#print axioms Problem625.Publishable.erdos_625_full_clean` returns
exactly **7 entries** (4 paper-backed + 3 Lean kernel) and **0
`sorryAx`** on the proof path of `erdos_625_full_clean`. Five internal
adversarial-audit passes (same LLM-agent pipeline; see
`proof/red-team/`); all concluded *no P0 found* in their respective
rounds.[^sorrynote]

[^sorrynote]: A grep of the Lean tree shows seven literal `sorry`
tokens in `private` helper lemmas: 5 in `PartBProfileBridge.lean`, 1 in
`ChromaticConnection.lean` (`decay_exponent_eventually_le_neg`,
documented in `ROADMAP.md` as off-path), and 1 in
`ZetaConcentration.lean` (the file's own header at line ~33 calls it
"architectural only, not load-bearing"). **None** is reachable from
`erdos_625_full_clean`; the seven-entry axiom inventory above is the
machine-checked statement of this. The legacy `erdos_625` (95%) and
`erdos_625_97` (97%) theorems are likewise unaffected.

---

## Flagship theorem

`Problem625.Publishable.erdos_625_full_clean` in
`Erdos625/PublishableProof.lean`:

For every real $\varepsilon$ with $0 < \varepsilon < 0.001$, there exists
$n_0$ such that for all $n \ge n_0$ (with **no** `InMainRange`
hypothesis),

$$
\mathbb{P}_{G \sim G(n,1/2)}\!\left[\,\chi(G) - \zeta(G) \ge n^{1-2\varepsilon}\,\right] \ge 1 - 2\varepsilon.
$$

The Lean theorem is the **per-$\varepsilon$ quantitative bound**
above. As a corollary (in $\varepsilon$, by letting $\varepsilon \to 0$;
**not itself formalized** in Lean),
$\chi(G) - \zeta(G) \to \infty$ in probability — positively answering
the **in-probability** form of the Erdős–Gimbel question
([erdosproblems.com/625](https://www.erdosproblems.com/625)). The
Erdős–Gimbel question literally asks for almost-sure convergence; that
upgrade requires a Borel–Cantelli / diagonal-subsequence argument that
is **not** a one-line application of Borel–Cantelli 1 (with
$\varepsilon_n = 1/\log n$ the series $\sum 2/\log n$ diverges, so a
subsequence-plus-monotonicity or coupling argument is needed) and is
**not yet** in the Lean chain. See `proof/proof.md` and `ROADMAP.md`
§N1 for the full scope discussion.

---

## Four theorems (coverage hierarchy)

| Theorem | Hypothesis | Bound | Coverage |
|---|---|---|---|
| `erdos_625` | `InMainRange ε n` | $\chi-\zeta \ge n^{1-\varepsilon}$ | $\sim 95\%$ of $n$ |
| `erdos_625_97` | `InMainRangeMod ε n` | $\chi-\zeta \ge n^{1-\varepsilon}$ | $\sim 97\%$ of $n$ |
| `erdos_625_full` | (none) | $\chi-\zeta \ge n^{1-\varepsilon} - 2n^{0.99}$ | $100\%$ |
| **`erdos_625_full_clean`** ⭐ | **(none)** | $\boldsymbol{\chi-\zeta \ge n^{1-2\varepsilon}}$ | $\boldsymbol{100\%}$ |

The flagship is `erdos_625_full_clean`; the other three are stepping
stones with their own clean Lean theorems for documentation and audit.

---

## Axiom inventory

```lean
import Erdos625.PublishableProof
#print axioms Problem625.Publishable.erdos_625_full_clean
```

returns exactly **7 entries**:

| Axiom | File | Source |
|---|---|---|
| `lemma_7_20_modified` | `PublishableProof.lean` | **hybrid:** HP-2023 Lemma 7.20 (modified) + our numerical certificate `lemma_7_10_ext` |
| `partB_alphaMinusTwo_firstMomentBelowOne_source` | `PartBAlphaMinusTwoFirstMomentAxiom.lean` | HP-2023 Lemma 8.1 first-moment input at level $\alpha-2$ |
| `chi_alphaMinusTwo_lower_bound_whp` | `CrossingPartB.lean` | HP-2023 Lemma 8.1 + Markov, at $\alpha-2$ |
| `zeta_alphaMinusTwo_upper_bound_whp` | `CrossingPartB.lean` | **extrapolation:** Heckel 2024 Prop 5(b) + Azuma, adapted $\alpha-1 \to \alpha-2$ |
| `propext`, `Classical.choice`, `Quot.sound` | Lean kernel | classical logic |

For a flat plain-text rendering see `proof/AXIOM_SNAPSHOT.txt`; for the
per-axiom paper citations see `paper/SOURCES.md`.

*Note on ordering.* Lean's `#print axioms` emits the seven entries in
alphabetical order by full namespace path, which interleaves the kernel
axioms with the `Problem625.*` paper-backed axioms (specifically
`Classical.choice` precedes the `Problem625.*` block and `propext` /
`Quot.sound` flank it). The verbatim alphabetical output is preserved in
`proof/AXIOM_SNAPSHOT.txt`; the table above re-groups the four paper-backed
axioms first and the three kernel axioms last for human reading.

**0 `sorryAx` on the proof path of `erdos_625_full_clean`** (the
`#print axioms` output above is the machine-checked statement of
this). Seven literal `sorry` tokens remain in `private` helper
lemmas in non-reachable supporting modules — see the footnote above
the flagship table.

---

## High-level proof idea

`erdos_625_full_clean` follows from `erdos_625_full` via an elementary
rpow inequality `rpow_clean_bound_eventually` (real analysis, 0
axioms).

`erdos_625_full` case-splits on `InMainRangeMod ε n`:

- **Good case** ($\sim 97\%$ of $n$): invoke `erdos_625_97`, which
  uses the modified Heckel 2024 chain (axiom #1 above).
- **Crossing case** ($\sim 3\%$ of $n$, $\mu_\alpha < n^{x_0+\varepsilon}$,
  $x_0 \approx 0.02905$): three new paper-backed axioms (#2, #3, #4)
  at level $\alpha-2$, where the structural margin
  $\mu_{\alpha-2}/\mu_\alpha = \Theta(n^2/\log^2 n)$ keeps every
  crossing $n$ inside HP-2023's $[n^{1.1}, n^{2.9}]$ application
  range. The crossing argument:
  $$
  \chi - \zeta \ge (k_{\alpha-2} - n^{0.99}) - (k_{\alpha-1} + n^{0.99}) = (k_{\alpha-2} - k_{\alpha-1}) - 2n^{0.99} \ge n^{1-\varepsilon} - 2n^{0.99}\quad\text{whp}\ge 1-2\varepsilon.
  $$

Full proof outline in `proof/proof.md`; full arXiv-style writeup in
`paper/main.tex`.

---

## Building and verifying

**Prerequisites**: Lean 4 / Lake (install via
[elan](https://github.com/leanprover/elan)). Toolchain version is
pinned in `lean-toolchain` (`leanprover/lean4:v4.29.0-rc8`).

```bash
git clone https://github.com/uthunderbird/erdosreshala-625
cd erdosreshala-625
lake exe cache get      # download prebuilt Mathlib oleans (~5 min)
lake build              # ~5 min with cache; 2925 jobs, GREEN
```

Verify the axiom inventory:

```lean
import Erdos625.PublishableProof
#print axioms Problem625.Publishable.erdos_625_full_clean
```

Expected output: exactly the seven entries listed in the table above.

---

## Repository layout

| Path | Contents |
|---|---|
| `Erdos625.lean` | Library root; imports `PublishableProof.lean`. |
| `Erdos625/PublishableProof.lean` | **Start here.** Four theorems + helper `rpow_clean_bound_eventually`. |
| `Erdos625/CrossingPartB.lean` | $\alpha-2$ chain: 3 crossing axioms + deterministic threshold gap. |
| `Erdos625/CrossingWindowProof.lean` | `KThresholdGapSource` theorem. |
| `Erdos625/PartBAlphaMinusTwoFirstMomentAxiom.lean` | The narrow HP-2023 Lemma 8.1 first-moment axiom. |
| `Erdos625/PartBAlphaMinusTwoFirstMomentBridge.lean` | Bridge to `kThreshold_gap_alpha_minus_2`. |
| `Erdos625/CumulantAlphaMinusTwo.lean` | Supporting cumulant lemmas. |
| `Erdos625/RouteD2.lean`, `Defs.lean`, `FirstMomentThreshold.lean`, `GapArithmetic.lean`, `ColoringBasic.lean`, `BoundedDifferences.lean`, `IndepMoments.lean` | Shared infrastructure. |
| `Erdos625/ChromaticConnection.lean`, `ZetaConcentration.lean`, `PartBProfileBridge.lean` | Part B / Part C chains; `erdos_625` axioms live here. |
| `proof/proof.md` | Standalone proof writeup. |
| `paper/main.tex` | arXiv-style companion paper. |
| `paper/SOURCES.md` | Per-axiom paper citations. |
| `proof/red-team/README.md` | **Index** over the audit artefacts (chronological, with one-line summaries and the "five red-team passes" mapping); read first if exploring the audit trail. |
| `proof/red-team/` | Audit artefacts: Markdown notes plus two Python reproducibility scripts. Local harness dumps and paper-side scratch critiques are intentionally not shipped in this publication package. |
| `DEVELOPMENT.md` | Architectural decision records (ADRs). |
| `ROADMAP.md` | Publication roadmap and known scope limitations. |

---

## References

- **HP-2023**: Heckel, A. & Panagiotou, K. (2023). *Colouring random
  graphs: Tame colourings.* arXiv:[2306.07253](https://arxiv.org/abs/2306.07253).
  Key inputs: Lemmas 5, 7.20, 8.1; eq:wert, eq:wert2, eq:mualpha-2.
- **Heckel 2024**: Heckel, A. (2024). *The difference between the
  chromatic and the cochromatic number of a random graph.*
  arXiv:[2409.17614](https://arxiv.org/abs/2409.17614). Key input:
  Proposition 5(b).
- **Companion paper**: [`paper/main.tex`](paper/main.tex).
- **Erdős–Gimbel question**: [erdosproblems.com/625](https://www.erdosproblems.com/625).

---

## Caveats

This section consolidates every caveat a reader should weigh before
relying on this work. The Lean kernel acceptance (build GREEN,
`#print axioms` machine-checked) reduces — but does not eliminate —
these risks.

### Prize disclaimer

This work does **not** claim the Erdős \$100 prize for Problem 625.
The prize is for an affirmative proof of $\chi(G) - \zeta(G) \to \infty$
**almost surely** (the Erdős–Gimbel question literally requires this).
The flagship Lean theorem `erdos_625_full_clean` establishes only the
**in-probability** form (a strictly weaker statement). Promoting to
almost-sure convergence requires a Borel–Cantelli / diagonal-subsequence
argument (with $\varepsilon_n \to 0$) which is **not yet formalized** in
Lean and is **not** a one-line application of standard Borel–Cantelli
(see `ROADMAP.md` §N1 for the actual measure-theoretic gap).

### LLM-agent provenance

This formalization — the Lean source, the companion paper, the proof
writeup, and the five red-team audit passes in `proof/red-team/` — was
generated by an LLM-agent pipeline (Anthropic Claude Opus 4.7, model id
`claude-opus-4-7[1m]`, the 1M-context variant, driven by the
open-source `operator` agent orchestrator at
[https://github.com/uthunderbird/vibechord](https://github.com/uthunderbird/vibechord)
whose codex-brain adapter ran `gpt-5.3-codex-spark` at `effort=low` to
propose next agent actions) under human supervision. The 1M-context
variant was load-bearing: the supporting Lean module
`PartBProfileBridge.lean` is 29512 lines (~1.59 MB), exceeding what
the 200k-context variant can hold in a single prompt. The same
LLM-agent pipeline also conducted the five internal adversarial-audit
passes; these are **not** independent third-party reviews.
Human-in-the-loop curation directed the proof strategy, accepted or
rejected proposed steps, and ran the build. See `paper/main.tex`
Acknowledgments and `DEVELOPMENT.md` ADR-7, ADR-10, ADR-11, and ADR-12
for details.

### Shared-blind-spot limitation

LLM-generated proofs may exhibit plausibility-driven failure modes that
can survive same-model internal critique because the proof author and
the critic share training-data blind spots. Here the proof author and
all five internal red-team critics are the **same** model
(`claude-opus-4-7[1m]`); the internal audits are therefore structurally
incapable of detecting blind spots inherited from training. External
verification by an unrelated reader, a different model, or a human
mathematician is encouraged. The Lean kernel acceptance reduces but
does not eliminate this risk: the four paper-backed axioms remain
admitted, and the natural-language disclosures surrounding them —
axiom-to-paper correspondence, the hybrid disclosure for A1, and the
extrapolation disclosure for A4 — remain LLM-authored. Cross-model
auditing was technically available through the `operator` framework's
codex-acp adapter but was not used in this development (see
`DEVELOPMENT.md` ADR-12).

### Hybrid / extrapolation axioms

Two of the four paper-backed axioms are **not** literal one-citation
paper quotes:

- **Axiom #1 `lemma_7_20_modified` (HYBRID).** Combines HP-2023
  Lemma 7.20 (peer-reviewed) with an in-repository numerical
  certificate `lemma_7_10_ext` (**not peer-reviewed**): a 1086-cell
  $\varphi$-positivity grid with Lipschitz envelope and ~1.2 orders
  of magnitude positivity margin. The underlying weakening is
  explicitly conjectured by Heckel 2024 §Discussion. See
  `proof/red-team/lemma-7-10-ext-disclosure-2026-05-11.md`.
- **Axiom #4 `zeta_alphaMinusTwo_upper_bound_whp` (EXTRAPOLATION).**
  Heckel 2024 Proposition 5(b) is stated and proved for
  $(\alpha-1)$-bounded profiles; this work uses the symmetric
  $(\alpha-2)$-version, which is **not literally in print**. The
  transfer goes via HP-2023's general-$a$ second-moment lemmas
  (Lemmas 6.3–6.5). See
  `proof/red-team/heckel2024-alpha-minus-two-transfer-audit-2026-05-11.md`.

Axioms #2 and #3 are literal HP-2023 citations.

### Reject ratio (order of magnitude)

Exact counts were not tracked, but qualitatively the development
required on the order of **$10^{2}$–$10^{3}$ rejected or failed agent
turns**; the final proof represents a small fraction of total LLM
output. See `DEVELOPMENT.md` ADR-12.

### Human supervisor and non-endorsement

Daniyar Supiyev directed the proof strategy at the branch-point level.
Contact: GitHub issues at
[https://github.com/uthunderbird/erdosreshala-625](https://github.com/uthunderbird/erdosreshala-625).
No institutional affiliation is claimed. Anthropic is acknowledged as
the provider of the Claude model used. No endorsement of this work by
Anthropic, OpenAI, or any other organization is implied.

### In-probability vs almost-sure scope

The Lean theorem is a per-$\varepsilon$ quantitative tail bound;
$\chi - \zeta \to \infty$ in probability is its $\varepsilon \to 0$
corollary and is not itself in the Lean chain either. The almost-sure
upgrade (the literal Erdős–Gimbel question) is a strictly stronger
statement and is not in scope of this work. See `ROADMAP.md` §N1.

---

## License

Apache 2.0.
