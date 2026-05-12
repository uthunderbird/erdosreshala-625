# Publish-Readiness Round 4 — Mathematical Exposition Rigor

**Date**: 2026-05-12
**Target**: `publish/erdos-625/` package (all human-readable + Lean files listed under "Inputs")
**Focus**: cross-document consistency of math content (threshold conventions, bounds, slack exponents, quantifier order, conditional definitions, hypothesis→conclusion directions, gap arithmetic, bibliographic restatements, numerical certificates).
**Mode**: hostile mathematician-referee line-by-line pass.
**Rounds 1–3 (honesty, provenance, navigation)**: NOT re-litigated.
**Status**: critique only; no repairs performed.

Inputs read in full: `README.md`, `proof/proof.md`, `paper/main.tex`,
`paper/SOURCES.md`, `proof/red-team/axiom-paper-correspondence-audit-2026-05-12.md`,
`proof/red-team/heckel2024-alpha-minus-two-transfer-audit-2026-05-11.md`,
`proof/red-team/red-team-erdos-625-full-2026-05-11.md`,
`proof/red-team/red-team-strict-lemma-by-lemma-2026-05-12.md`,
`proof/red-team/lemma_7_10_ext.md`,
`proof/red-team/lemma-7-10-ext-disclosure-2026-05-11.md`,
`proof/red-team/r2b-step1-results-2026-05-11.md`,
`Erdos625/PublishableProof.lean` (statements + axiom blocks),
`Erdos625/CrossingPartB.lean` (axiom statements),
`Erdos625/PartBAlphaMinusTwoFirstMomentAxiom.lean` (full file),
`Erdos625/Defs.lean` (`InMainRange*`, `x₀`).

---

## Headline verdict

**P0 = 2, P1 = 4, P2 = 3.**

Both P0s are exact-quote contradictions between an audit note and the rest of the
package on a numerical / definitional fact. Neither breaks the Lean proof. Both
are visible to a careful referee and are exactly the kind of finding a hostile
mathematician will use to call the package's consistency into question.

This artifact does **not** invalidate the proof; the four Lean theorems remain
machine-checked. But the package promises "every mathematical statement and
constant is internally consistent and matches the Lean source plus the cited
papers", and two such statements drift from that promise.

---

## P0 findings

### P0-1. "6 orders of magnitude" vs "≈ 1.2 orders of magnitude" — numerical margin contradiction

`proof/red-team/lemma-7-10-ext-disclosure-2026-05-11.md:59` states:

> "Margin: `envelope_lb > 0` by **6 orders of magnitude** vs the
> `L · h / 2 ≈ 3.74×10⁻⁸` slack term."

And the same file at line 111 (inside the suggested honest-framing block intended
for any future preprint):

> "yielding `min ϕ ≥ 6.15×10⁻⁷` with **6 orders of magnitude** margin over the
> Lipschitz slack."

Every other source in the package says **≈ 1.2 orders of magnitude**:

- `README.md:188`: "~1.2 orders of magnitude positivity margin"
- `ROADMAP.md:76`: "`lemma_7_10_ext` (1086-cell grid, $\sim 1.2$ orders of magnitude"
- `proof/proof.md:156-157`: "positivity margin ≈ 1.2 orders of magnitude"
- `paper/main.tex:523`: "$\approx 1.2$ orders of magnitude"
- `proof/red-team/red-team-strict-lemma-by-lemma-2026-05-12.md:73`: "envelope 6.15×10⁻⁷"
  with positivity margin "≈ 1.2 orders of magnitude" (Strict-pass P1-1, second
  paragraph).
- `proof/red-team/red-team-proof-md-2026-05-12.md:103-117` explicitly **flags this
  exact bug** in another sibling document ("envelope_lb itself is 6.15 × 10⁻⁷,
  i.e. ~6 in units of 10⁻⁷, but [a ratio against the slack] is the wrong reading")
  and prescribes the repair "replace with `positivity margin of envelope_lb ≈
  6.15 × 10⁻⁷`".

Arithmetic check: `envelope_lb / (L·h/2) = 6.150197 × 10⁻⁷ / 3.744207 × 10⁻⁸ ≈
16.43`, i.e. `log₁₀(16.43) ≈ 1.22`, confirming **≈ 1.2 OOM**, **not 6 OOM**. The
"6 orders of magnitude" reading conflates the magnitude of `envelope_lb` itself
(which sits at the `10⁻⁷` scale, "6–7 orders of magnitude below 1") with the
ratio `envelope_lb / slack` (which is `≈ 16`, i.e. 1.2 OOM).

**Why P0**: this is a numerical claim on a load-bearing certificate, present in
the disclosure note that the package directs reviewers to consult, in contradiction
with five sibling documents. The fix that the *sibling* audit
(`red-team-proof-md-2026-05-12.md`) prescribed was applied to `proof.md` but
**not propagated back to the disclosure note itself**. A reader who follows the
README breadcrumbs into the disclosure note sees the wrong figure.

**Files affected (verbatim occurrences)**:
- `proof/red-team/lemma-7-10-ext-disclosure-2026-05-11.md:59`
- `proof/red-team/lemma-7-10-ext-disclosure-2026-05-11.md:111`

**Fix shape (do not apply in this round)**: replace both occurrences with
"≈ 1.2 orders of magnitude (ratio 6.15×10⁻⁷ / 3.74×10⁻⁸ ≈ 16.4)" so the figure
is internally explanatory.

---

### P0-2. Lean `x₀ := 0.02905` vs certificate `x₀ = 0.02905439` — boundary mismatch

`Erdos625/Defs.lean:173-176`:

```lean
/-- x₀ ≈ 0.02905 is the unique zero of ϕ(1,x,1) in HP-2023 eq. (7.19).
    Determines the exact threshold below which the sub-profile second-moment
    argument (condition (d) of Lemma 7.20) fails. See proof sketch 2026-05-10. -/
noncomputable def x₀ : ℝ := 0.02905
```

Note: `x₀ : ℝ := 0.02905` is the *exact* rational value Lean uses; the leading
`≈` is in the docstring only.

`Erdos625/Defs.lean:181-184` defines `InMainRangeMod ε n` ⇔
`(n : ℝ)^(x₀ + ε) ≤ μ ∧ μ ≤ (n : ℝ)^(1 - ε)`, i.e. the **Lean** lower-bound
exponent is `0.02905 + ε`.

`proof/red-team/lemma_7_10_ext.md:44` says:

> "x₀ = 0.02905439 (residual |ϕ(x₀)| = 4.5 × 10⁻¹⁷ ≈ machine zero)"

and lines 57, 170 reaffirm `x₀ = 0.02905439` with the certificate proving
`inf_{x ∈ [0.029154, 0.04)} ϕ(x) ≥ 6.150 × 10⁻⁷`.

`proof/red-team/lemma-7-10-ext-disclosure-2026-05-11.md:37`:

> "Let x₀ = 0.02905439, ε = 10⁻⁴, x_lo = x₀ + ε = 0.029154"

i.e. the certificate's `x_lo = 0.029154` is `0.02905439 + 10⁻⁴`. **It is not
`0.02905 + ε_Lean`** for `ε_Lean ∈ (0, 0.001)`.

For `ε_Lean ∈ (0, 0.00010561)`, the Lean condition `μ_α ≥ n^{0.02905 + ε_Lean}`
corresponds to a target ϕ-positivity at `x ∈ [0.02905 + ε_Lean, 0.04)`, whose
**lower endpoint lies strictly below** the certificate's `x_lo = 0.029154`. The
uncovered interval `[0.02905 + ε_Lean, 0.029154)` is non-empty whenever
`ε_Lean < 0.000104` — a non-negligible subset of the theorem's declared range
`ε ∈ (0, 0.001)`.

In other words: the analytic ϕ-positivity certificate proves ϕ > 0 on
`[0.029154, 0.04)`, but the Lean axiom `lemma_7_20_modified` requires ϕ-positivity
on `[0.02905 + ε, 0.04)` for **every** `ε ∈ (0, 0.001)`, including ε well below
`10⁻⁴`. The package nowhere reconciles these:

- Either `Defs.lean:176` should read `noncomputable def x₀ : ℝ := 0.02905439`
  (4 additional digits, no other change), pushing the Lean boundary inside the
  certified interval; or
- The disclosure must state that the relevant analytic interval is fixed at
  `[0.029154, 0.04)` regardless of the theorem's `ε`, and explain how that
  delivers ϕ-positivity for `x = 0.02905 + ε` when `ε < 10⁻⁴`.

`Erdos625/PublishableProof.lean:347, 391, 393, 411` all use the rounded
`x₀ ≈ 0.02905` text but cite the certificate. `paper/main.tex:251-255`,
`proof/proof.md:60`, `README.md:213-214`, `paper/SOURCES.md:27`, all use
"`x₀ ≈ 0.02905`". A referee who looks at the exact Lean definition will see
`0.02905` (not `0.02905439`) and then read the certificate framed in
`0.02905439`. There is no document that tells them which boundary is binding.

**Why P0**: this is a definitional/numerical alignment between the Lean source of
truth and the analytic certificate that is supposed to certify the gap in the
Lean axiom's hypothesis. The mismatch is small (≈ 4 × 10⁻⁶) but real: for
`ε_Lean < 0.000104`, the certificate does not cover the interval. Either fix is
trivial; the *absence* of either is a P0.

**Files affected**:
- `Erdos625/Defs.lean:176` (Lean source of truth)
- `proof/red-team/lemma_7_10_ext.md:44, 57, 78, 170, 209-211`
- `proof/red-team/lemma-7-10-ext-disclosure-2026-05-11.md:37` (`ε = 10⁻⁴` fixed
  treatment)
- Every doc using `x₀ ≈ 0.02905`:
  `README.md:214`, `paper/SOURCES.md:27`, `paper/main.tex:251`,
  `proof/proof.md:60`, `proof/red-team/r2b-step1-plan-2026-05-11.md:14, 39, 59`,
  `proof/red-team/r2b-step1-results-2026-05-11.md:7`,
  `proof/red-team/axiom-paper-correspondence-audit-2026-05-12.md:98`,
  `Erdos625/PublishableProof.lean:347, 391, 393, 411`.

---

## P1 findings

### P1-1. paper/main.tex Lemma 3 justification omits the X-class removal step

`paper/main.tex:350-379` (the proof-sketch for `\Cref{lem:chi_lower}` = axiom
`chi_alphaMinusTwo_lower_bound_whp`) says:

> "Heckel–Panagiotou~\cite{heckelpanagiotou2023}, Lemma~8.1 establishes
> $\chrom_{a}(G)\geq\mathbf{k}_{a}-1$ \whp\ for $a\in\{\alpha-1,\alpha-2\}$. The
> slack $n^{0.99}$ is a conservative budget covering both (i) the lossless $-1$
> in HP-2023 Lemma~8.1's conclusion and (ii) the Azuma–Hoeffding vertex-exposure
> martingale deviation of $\chrom_{a}$ around its mean."

It then computes the Azuma tail at scale `n^{0.96}` and notes
"`n^{0.99} ≫ n^{0.96}` slack absorbs the Azuma deviation". The justification
**stops there**.

But HP-2023 Lemma 8.1 bounds `χ_a`, not `χ`. The axiom's conclusion is
`χ(G) ≥ k_{α-2} − n^{0.99}` whp — i.e. on the chromatic number itself, not on
the a-bounded chromatic number. The missing step is the X-class removal
observation, which is stated explicitly only in:

- `paper/SOURCES.md:73-77`: "`χ(G) ≥ χ_{α-2}(G) - X_α - X_{α-1}`, with both
  correction terms negligible in the crossing regime"
- `proof/red-team/axiom-paper-correspondence-audit-2026-05-12.md:151-157`:
  the full derivation with `X_α = O(log n)` whp and `X_{α-1} = O(n / log n)` whp
  in the crossing case.

The flagship paper therefore presents the slack `n^{0.99}` as an Azuma-only
budget, when in fact a substantial part of it absorbs `X_α + X_{α-1} = O(n/log n)`
(the **dominant** term, much larger than the Azuma `n^{0.5}`-scale tail). A
mathematician-referee comparing paper/main.tex against the Lean axiom and the
Lean source's docstring (`CrossingPartB.lean:227-262`, which does mention the
X-class observation) will spot the omission.

**Why P1, not P0**: the math is correct (the slack is sufficient because
`O(n/log n) ≪ n^{0.99}`), and the X-class step is given in SOURCES.md and the
audit note. But the *paper itself* — the document an arXiv reader sees first —
hides the load-bearing argument behind a single line of Azuma analysis. This is
the strongest "where does the stronger reading fail?" finding in the package.

**Fix shape**: insert a single paragraph in `\Cref{lem:chi_lower}`'s
"Justification" block stating "HP-2023 Lemma 8.1 bounds `χ_a`, which is related
to χ by the X-class observation `χ ≥ χ_a − X_α − X_{α-1}` (Heckel 2024, eq. used
near line 433); in the crossing regime `μ_α < n^{x₀+ε}`, so `X_α = O(log n)`
whp and `X_{α-1} = O(n/log n)` whp; the slack `n^{0.99}` absorbs both this and
the Azuma deviation."

---

### P1-2. `μ_{α-2} ≥ n^{1.05}` vs HP-2023 application range `[n^{1.1}, n^{2.9}]`

Two different "application threshold" numbers float through the package without
disambiguation:

- `n^{1.1}` (HP-2023 §8 application range lower bound, for Lemma 8.1):
  `paper/main.tex:122` "$[n^{1.1},n^{2.9}]$ application range",
  `proof/proof.md:121` "HP-2023's [n^{1.1}, n^{2.9}] application range",
  `proof/red-team/red-team-erdos-625-full-2026-05-11.md:27` "application
  conditions for Lemma 8.1: μ_a ∈ [n^{1.1}, n^{2.9}]".
- `n^{1.05}` (the actual application threshold the package's α−2 transfer needs,
  from shifting `μ_α ≥ n^{0.05+ε}` up by a factor of n):
  `paper/main.tex:401-402` "translates at $a=\alpha-2$ to
  $\mu_{\alpha-2}\geq n^{1.05}$",
  `proof/red-team/heckel2024-alpha-minus-two-transfer-audit-2026-05-11.md:60`
  "the relevant inequality is `μ_{α−2} ≥ n^{1.05}`",
  `proof/red-team/r2b-step1-results-2026-05-11.md:7` "x_{α−2}(n) ≥ 1.05".

These are **two different conditions**: `n^{1.1}` is the HP-2023 lower bound
for general Lemma-8.1 application; `n^{1.05}` is the Heckel-2024 (α−1) lower
bound shifted to α−2. The package uses them interchangeably as "the application
condition", and a referee who knows HP-2023 will ask which is binding. The
numerical certificate (R2B Step 1) tests `≥ 1.05`, which is the weaker of the
two; the slope `[1.65, 1.80]` clears both.

**Why P1, not P0**: the math is sound at either threshold (the empirical floor
1.533 clears 1.1 and 1.05); but the exposition uses the two numbers in adjacent
paragraphs without saying they are different conditions on different lemmas.

**Files affected**: `paper/main.tex:122` vs `:401-402`;
`proof/red-team/heckel2024-alpha-minus-two-transfer-audit-2026-05-11.md:60-65`
vs `proof/red-team/red-team-erdos-625-full-2026-05-11.md:27-32`.

---

### P1-3. Asymptotic slope band: `[1.65, 1.80]` vs `[1.68, 1.80]`

The canonical numerical source is
`proof/red-team/r2b-step1-results-2026-05-11.md:55-60` (Pass C, mpmath dps=50,
n ∈ {10⁷, …, 10¹²}): the six measured slope values are `1.6783, 1.6858, 1.7586,
1.7536, 1.7486, 1.7950` (verified by recomputing `x_{α−2} − x_α` from columns 3
and 5 of the table). The minimum is `1.6783`, the maximum is `1.7950`.

Cited as:

- `proof/red-team/r2b-step1-results-2026-05-11.md:122` "slopes = ['1.678',
  '1.686', '1.759', '1.754', '1.749', '1.795']"
- `proof/red-team/red-team-erdos-625-full-2026-05-11.md:43` "slope
  `x_{α−2} − x_α ∈ [1.68, 1.80]`" — **rounded `1.6783 → 1.68`** (one decimal),
  consistent with the data.
- `paper/main.tex:336` "$x_{\alpha-2}\in[1.65,1.80]$" — **understates the
  lower bound by 0.03**. The data minimum is `1.6783`; rounding down to
  `1.65` is *more conservative* (i.e. paper claims a weaker margin than is
  actually achieved), which is mathematically harmless but a misquote.
- `proof/proof.md:120` "asymptotic in [1.65, 1.80] for n ∈ [10⁷, 10¹²]" —
  same understated lower bound.
- `README.md`: does not state the slope band directly.

**Why P1**: the band `[1.65, 1.80]` is not present in the canonical numerical
source (`r2b-step1-results-2026-05-11.md`'s data shows min slope 1.6783); two
different rounding conventions (one rounding to 0.01 floor → 1.65; the other
rounding to nearest 0.01 → 1.68) coexist. The conservative direction makes this
not a correctness issue, but it is a quotable inconsistency.

**Fix shape**: use `[1.68, 1.80]` consistently (matches the data), or
`[1.6, 1.8]` (one decimal, both true), in `paper/main.tex:336`,
`proof/proof.md:120`, and any other doc that picks up the band.

---

### P1-4. `axiom-paper-correspondence-audit-2026-05-12.md:191` uses `n^{0.9995}` with silent ε = 0.001

The α−2 transfer derivation reads:

> "ζ ≤ boldk_{α-2} - n^{1-ε/2} + 2n^{0.999} whp.
>  Using boldk_{α-2} = boldk_{α-1} + Θ(n/log²n):
>  ζ ≤ boldk_{α-1} + Θ(n/log²n) - **n^{0.9995}** + 2n^{0.999}"

The exponent `0.9995` is `1 − ε/2` with `ε` silently fixed to `0.001` (its upper
endpoint). Up to line 189 the derivation kept `ε` symbolic (`n^{1-ε/2}`); on
line 191 it switches to numeric without saying so. The remainder of the
derivation then equates `n^{0.999} > n^{0.9995}`, which is **false numerically**
(`0.999 < 0.9995`), but **becomes true** once you read `0.9995` as
`1 − ε/2` for `ε < 0.001` (`1 − ε/2 > 0.9995 > 0.999` — and indeed `n^{0.9995}`
is *larger*, so `-n^{0.9995} + 2n^{0.999}` is dominated by the negative term,
and the absorption is the other way around). The audit's conclusion
"`≈ n^{0.999}` dominates" depends on this confusion being unwound by the reader.

**Why P1**: this is an internal-derivation slip in an audit note that nobody is
expected to compute by hand. It does not propagate to the Lean source or to the
paper. But the audit note presents itself as a byte-by-byte sanity check; a
referee who reads it line-by-line will pause.

**Fix shape**: keep `n^{1-ε/2}` symbolic to the end, or insert "fix ε ≤ 0.001
so `1 − ε/2 ≥ 0.9995`" once before the numeric step.

---

## P2 findings

- **P2-1.** `red-team-erdos-625-full-2026-05-11.md:30` writes
  `μ_{α-2} ≥ Θ(n² / log²n) = n^{2 − 2 loglog n / log n}`, a continuous
  rewriting that loses the `Θ` constant. Harmless (the asymptotic form is
  correct), but the strict-pass and paper carry `≈ n^{1.65}` at `n = 10⁶`,
  whereas the rewriting suggests `≈ n^{1.49}` at `n = 10⁶` (since
  `2 − 2·log log 10⁶ / log 10⁶ = 2 − 2·log(13.8)/13.8 ≈ 1.62`, not 1.49 —
  recheck). Stylistic mixing of `Θ` and concrete exponents.

- **P2-2.** `paper/main.tex:80` writes "structural margin
  $\Theta(n^{2}/\log^{2}n\cdot\mu_{\alpha})$" — the `\cdot\mu_α` is *inside*
  the `Θ(·)`, which formally makes the margin scale with `μ_α`. The intended
  reading is `μ_{α-2}/μ_α = Θ(n²/log²n)`, i.e. the *ratio* is the margin.
  Easy to misparse on a first read. Notational polish.

- **P2-3.** `axiom-paper-correspondence-audit-2026-05-12.md:19` writes
  "X_{α-1} = O(n/log n) whp (HP-2023 expectationu eq with μ_α ≈ 1)". The
  word `expectationu` is a non-word (likely a typo for `expectation`,
  possibly preserving HP-2023's internal LaTeX label `\textsc{expectationu}`).
  Cosmetic.

---

## Grep tabulation: numerical certificate constants (item (i))

| Constant                | Canonical value (lemma_7_10_ext.md)      | proof/proof.md | paper/main.tex | paper/SOURCES.md | README.md | lemma-7-10-ext-disclosure | strict-lemma-by-lemma | red-team-proof-md | ROADMAP.md | PublishableProof.lean |
|-------------------------|------------------------------------------|----------------|----------------|------------------|-----------|---------------------------|-----------------------|-------------------|------------|-----------------------|
| Grid cells              | 1086 (line 109, 173)                     | 1086 (155)     | 1086 (519)     | 1086 (32)        | 1086 (186)| 1086 (54, 110)            | 1086 (71)             | 1086 (93)         | 1086 (76)  | 1086 (386)            |
| Grid spacing h          | 10⁻⁵ (line 109, 173)                     | —              | —              | —                | —         | 10⁻⁵ (53)                 | —                     | —                 | —          | —                     |
| Interval [x_lo, x_hi]   | [0.029154, 0.04) (line 57, 109)          | [x₀+ε, 0.04) (87) | (implicit) | [x₀+ε, 0.04) (33) | (implicit) | [x_lo, x_hi]              | —                     | —                 | —          | (implicit)            |
| min ϕ on grid           | 6.524618 × 10⁻⁷ (line 119, 179)          | 6.5 × 10⁻⁷ (155)| (implicit)    | (implicit)       | (implicit)| 6.524618 (55, 89)         | 6.5×10⁻⁷ (71)         | 6.5×10⁻⁷ (92)     | (implicit) | 6.5×10⁻⁷ (386)        |
| Lipschitz bound L       | 7.488414 × 10⁻³ (line 136, 178)          | —              | —              | —                | —         | 7.488414 (56)             | 7.49×10⁻³ (71)        | 7.49×10⁻³ (93)    | —          | 7.49 (386)            |
| Envelope lb             | 6.150197 × 10⁻⁷ (line 151, 180)          | —              | —              | —                | —         | 6.150197 (57)             | 6.15×10⁻⁷ (72)        | 6.15×10⁻⁷ (94)    | —          | 6.15×10⁻⁷ (388)       |
| Lipschitz slack L·h/2   | 3.744207 × 10⁻⁸ (line 150)               | —              | —              | —                | —         | (≈ 3.74×10⁻⁸)            | —                     | —                 | —          | —                     |
| **Margin (orders)**     | 1.2 OOM (from line 153 ratio)            | 1.2 OOM (157)  | 1.2 OOM (523)  | —                | 1.2 OOM (188)| **6 OOM** (59, 111) ✗  | 1.2 OOM (73)          | (implicit)        | 1.2 OOM (76)| 1.2 OOM (~388)        |
| Margin (ratio)          | (≈ 16)                                   | —              | —              | —                | —         | —                         | —                     | (≈ 16)            | —          | —                     |
| x₀                      | 0.02905439 (44, 57, 78, 170)             | 0.02905 (60)   | 0.02905 (251)  | 0.02905 (27)     | 0.02905 (214) | 0.02905439 (37)        | 0.02905 (74)          | 0.02905           | (impl)     | 0.02905 (Defs.lean:176) ✗ |
| ε (certificate)         | 10⁻⁴ (line 57, 171)                       | —              | —              | —                | —         | 10⁻⁴ (37)                 | —                     | —                 | —          | —                     |

✗ = inconsistent with majority. **P0-1** is the `6 OOM` row; **P0-2** is the
`x₀ = 0.02905 (Lean)` vs `0.02905439 (certificate)` row.

---

## Grep tabulation: α-2 margin numerics (item (j))

| Quantity                           | Canonical (r2b-step1-results) | red-team-erdos-625-full | strict-lemma-by-lemma | heckel2024-α-2-transfer | paper/main.tex   | proof/proof.md   | publish-readiness-r3 |
|-----------------------------------|-------------------------------|--------------------------|------------------------|--------------------------|------------------|------------------|----------------------|
| Scan range                        | n ∈ [100, 10⁶] (6)            | n ∈ [100, 10⁶] (41)      | (implicit)             | n ∈ [100, 10⁶] (66-67)   | n ∈ [100, 10⁶] (335)| n ∈ [100, 10⁶] (120)| —              |
| n scanned                         | 999,901 (13)                  | —                        | —                      | —                        | —                | —                | —                    |
| Bad n count                       | 34,636 (14)                   | —                        | —                      | —                        | —                | —                | —                    |
| Bad density                       | 3.464% (14)                   | (~3% implied)            | —                      | —                        | —                | (~3% implied 90) | —                    |
| Min bad margin                    | 0.483244 (15)                 | 0.483 (42)               | 0.4832 (92)            | 0.483 (68)               | (not stated)     | (not stated)     | —                    |
| Worst-margin n                    | 108 (38, 71)                  | 108 (42)                 | 108 (92)               | (implied)                | (not stated)     | (not stated)     | —                    |
| x_{α−2}(108)                      | 1.533244 (38, 71)             | (≥ n^{1.65} at n=10⁶, 30)| —                      | n^{1.6} for n≥100 (66)   | $\geq 1.533$ (333)| n^{1.65} (119)  | —                    |
| Required threshold                | 1.05 (7)                      | (not stated)             | —                      | 1.05 (60, 67)            | n^{1.05} (402)   | (not stated)     | —                    |
| Asymptotic slope band             | min 1.678, max 1.795 (60, 122)| **[1.68, 1.80]** (43)   | —                      | 1.65–1.80 (68)           | **[1.65, 1.80]** (336)| **[1.65, 1.80]** (120)| —              |

Discrepancies:
- Slope lower bound: data minimum is **1.678**; red-team-erdos-625-full and
  heckel2024-α-2-transfer round to **1.68**; paper/main.tex and proof/proof.md
  round to **1.65** (conservative but wrong — see **P1-3**).
- "n^{1.05}" (transfer-audit, paper) vs "n^{1.1}" (HP-2023 application range,
  red-team-erdos-625-full) — see **P1-2**.

---

## Items checked and CLOSED (verified consistent)

- **Threshold convention** (item a). `boldk_t(n) := min{k : E_{n,k,t} ≥ 1}`
  appears at `paper/main.tex:217-222` (Definition 1), `proof/proof.md:54-58`,
  `axiom-paper-correspondence-audit-2026-05-12.md:34-37` (P0-D1 fix landed).
  Direction `boldk_{α-2} > boldk_{α-1}` consistent at
  `paper/main.tex:238` ("$\partbthr(n)\le\athr(n)$" with explanation),
  `proof/proof.md:55-58`, and the Lean identifiers
  `kThresholdAlphaMinusOne` / `kThresholdAlphaMinus2`. Gap `Θ(n/log²n)` consistent
  at `paper/main.tex:242`, `proof/proof.md:56`,
  `axiom-paper-correspondence-audit-2026-05-12.md:18`. Post-rename header
  notes present on all four named audit files (per round-3 P0-4 fix):
  `axiom-paper-correspondence-audit-2026-05-12.md:3`,
  `red-team-strict-lemma-by-lemma-2026-05-12.md:3`,
  `paper/red-team-paper-2026-05-12.md:3`,
  `proof/red-team/erdos-625-full-axiom-check-2026-05-11.md:3`.

- **Bound consistency across four theorems** (item b). Tabulated grep shows
  all four bounds (`n^{1-ε}` × 2, `n^{1-ε} − 2·n^{0.99}`, `n^{1-2ε}`) appear
  uniformly. Coverage labels 95% / 97% / 100% / 100% consistent in
  `README.md:136-139`, `proof/proof.md:65-70`, `paper/main.tex:262-296`,
  `paper/SOURCES.md:113-136`, `ROADMAP.md:16`. Helper
  `rpow_clean_bound_eventually` statement consistent
  (`PublishableProof.lean:621`, `paper/main.tex:289-296`,
  `proof/proof.md:74-77`).

- **Slack constants** (item b). `n^{1-0.9ε}` (χ side, α−1):
  `Erdos625/PublishableProof.lean:46,50,53,88,98,111,246,249,286,288,292`,
  `proof/proof.md:86`, `paper/main.tex` (implicit via
  `lemma_7_20_modified`), `axiom-paper-correspondence-audit-2026-05-12.md:81,89,94`.
  `n^{1-ε/2}` (ζ side, α−1):
  `proof/proof.md:87`, `axiom-paper-correspondence-audit-2026-05-12.md:82,90,94,182,189,191`,
  `PublishableProof.lean:46,50,53,98,111,249,288,292`. `2·n^{0.999}` (good case):
  `proof/proof.md:87,107`, `paper/main.tex:369`,
  `axiom-paper-correspondence-audit-2026-05-12.md:82,90,94,182,188,189,191`,
  `PublishableProof.lean:46,50,53,98,111,249,288,292`. `n^{0.99}` (crossing
  case): see grep table above (16 hits). All four propagate with the correct
  exponents.

- **Quantifier order** (item c). Lean theorem statements
  `PublishableProof.lean:251, 417, 502, 702`, axioms `:400, :621`,
  `CrossingPartB.lean:263, 311`, and `PartBAlphaMinusTwoFirstMomentAxiom.lean:50`
  all bind `ε` outside `∃ n₀`, then `∀ n ≥ n₀`. Paper Theorem 1
  (`paper/main.tex:125-127`) uses "For every $\varepsilon\in(0,0.001)$, there
  exists $n_{0}=n_{0}(\varepsilon)$ such that for all $n\geq n_{0}$" — explicit
  ε-dependence in `n₀(ε)`. `proof/proof.md:16`, `README.md:108-114` likewise.
  No `∃ n₀ ∀ ε ∀ n` form found anywhere in the package.

- **InMainRange / InMainRangeMod** (item d). `Erdos625/Defs.lean:168-184`
  defines both: `InMainRange` ⇔ `n^{0.05+ε} ≤ μ ≤ n^{1-ε}`, `InMainRangeMod`
  ⇔ `n^{x₀+ε} ≤ μ ≤ n^{1-ε}`. Paper/main.tex:246-255 matches. Proof.md:59-61
  matches. (The Lean `x₀ := 0.02905` exact-rational issue is P0-2 above.)
  The two disjuncts of `¬ InMainRangeMod` are explicitly named at
  `paper/main.tex:302-310`, `proof/proof.md:122-125`, and the docstring of
  `chi_alphaMinusTwo_lower_bound_whp` (`CrossingPartB.lean:252-262`); the
  μ > n^{1-ε} disjunct is correctly identified as asymptotically vacuous via
  Stirling.

- **Heckel 2024 anchor `k* = boldk_{α-1} − n^{1-ε/2}`** (item f).
  `axiom-paper-correspondence-audit-2026-05-12.md:182` "ζ(G_{n,1/2}) ≤ k* +
  2n^{0.999}, where k* = boldk_{α-1} - n^{1-ε/2}". Consistent with
  `proof/proof.md:87`, `PublishableProof.lean:46`, paper/main.tex (implicit
  via lemma_7_20_modified statement). α−2 anchoring at boldk_{α-1} with slack
  n^{0.99}: `proof/proof.md:97`, `paper/main.tex:384`,
  `CrossingPartB.lean:311-312`, `axiom-paper-correspondence-audit-2026-05-12.md:20,179`,
  all consistent.

- **Gap arithmetic** (item g). `n^{1-ε/2} − n^{1-0.9ε} − 2·n^{0.999} ≥ n^{1-ε}`
  consistent: `PublishableProof.lean:53,111,249`,
  `axiom-paper-correspondence-audit-2026-05-12.md:94`. `n^{1-2ε} ≤ n^{1-ε} −
  2·n^{0.99}`: `PublishableProof.lean:621-676` (proof of
  `rpow_clean_bound_eventually`), `paper/main.tex:289-296`, `proof/proof.md:75`.
  `boldk_{α-2} − boldk_{α-1} ≥ n^{1-ε}`: stated at `paper/main.tex:412-413`
  (Lemma 4 = `kThreshold_gap_alpha_minus_2`), `proof/proof.md:93-94`,
  `CrossingPartB.lean` (`kThresholdGapSource`), `axiom-paper-correspondence-audit-2026-05-12.md:18`.

- **Bibliographic accuracy** (item h). HP-2023 Lemma 8.1 statement
  ("χ_a ≥ k_a − 1 whp for a ∈ {α−2, α−1}") quoted at `paper/main.tex:357`,
  `proof/proof.md:95-96`, `axiom-paper-correspondence-audit-2026-05-12.md:146-147`,
  `heckel2024-alpha-minus-two-transfer-audit-2026-05-11.md:72-74`. HP-2023
  eq:mualpha-2 (μ_{α-2}/μ_α = Θ(n²/log²n)) quoted at `paper/main.tex:325-327`,
  `proof/proof.md:118`, `README.md:216`. Heckel 2024 Prop 5(b) statement quoted
  at `axiom-paper-correspondence-audit-2026-05-12.md:182`, paper/main.tex
  (§A4), Heckel 2024 §Discussion conjecture re Lemma 7.20 quoted at
  `lemma-7-10-ext-disclosure-2026-05-11.md:27-29` (verbatim) and
  `paper/main.tex:514-517`. HP-2023 eq:ktdef definition quoted at
  `paper/main.tex:218-222`, `proof/proof.md:54`. **Notes (i) μ_{α-2} ≥ n^{1.05}
  vs HP-2023 [n^{1.1}, n^{2.9}] application range — see P1-2.**

---

## Mechanism audit (per `mechanism-audit.md`)

**Mechanism claim**: "Every mathematical statement and constant in the package
is internally consistent and matches the Lean source plus the cited papers."

1. **What does the target explicitly promise?** A self-consistent
   referee-ready package in which (i) every theorem statement, (ii) every
   slack-exponent, (iii) every threshold convention, (iv) every conditional
   definition, (v) every restated paper lemma, (vi) every numerical certificate
   constant agrees byte-for-byte across all human-readable docs and matches
   the Lean source of truth.

2. **What does the mechanism actually guarantee?** The Lean kernel certifies
   the proof modulo the four named axioms + three kernel axioms (verified by
   `#print axioms`). Cross-doc math consistency is *not* mechanically
   enforced — it depends on the same LLM-agent pipeline preserving the
   conventions across documents and audit rounds.

3. **Where does the stronger reading fail?**
   - **P0-1**: `lemma-7-10-ext-disclosure-2026-05-11.md:59,111` says "6 orders
     of magnitude" margin where every other doc says "1.2 orders of magnitude"
     (or "≈ 16" ratio). The fix prescribed by `red-team-proof-md-2026-05-12.md`
     for `proof.md` was not propagated back to the disclosure note itself.
   - **P0-2**: Lean `Defs.lean:176` uses `x₀ := 0.02905` exact; the certificate
     proves positivity from `x_lo = 0.02905439 + 10⁻⁴ = 0.029154`. For
     ε_Lean < 0.000104, the Lean InMainRangeMod boundary lies *below* the
     certified interval; the package nowhere reconciles the two boundaries.
   - **P1-1**: paper/main.tex Lemma 3 justification omits the X-class removal
     step that converts `χ_a ≥ k_a − 1` to `χ ≥ k_{α-2} − n^{0.99}`. The
     Azuma-only justification given is structurally insufficient.
   - **P1-2**: `n^{1.05}` (α−2 transfer threshold) vs `n^{1.1}` (HP-2023
     application range) used interchangeably as "the application condition"
     without disambiguation.
   - **P1-3**: slope band cited as `[1.65, 1.80]` in paper/proof.md and
     `[1.68, 1.80]` in red-team-erdos-625-full; canonical data minimum is
     1.6783.
   - **P1-4**: `axiom-paper-correspondence-audit-2026-05-12.md:191` slides
     from `n^{1-ε/2}` to `n^{0.9995}` mid-derivation without flagging the
     ε = 0.001 substitution.

4. **Minimal fix set** (do not apply in this round):
   - **P0-1 (priority 1)**: replace "6 orders of magnitude" with "≈ 1.2 orders
     of magnitude" or "≈ 16-fold" at
     `lemma-7-10-ext-disclosure-2026-05-11.md:59` and `:111`.
   - **P0-2 (priority 1)**: tighten `Defs.lean:176` to
     `noncomputable def x₀ : ℝ := 0.02905439` (4 extra digits) — and
     re-verify `lake build`. Alternatively, add a one-paragraph note to
     `lemma_7_10_ext.md` and `lemma-7-10-ext-disclosure-2026-05-11.md`
     explaining how the certificate's fixed `x_lo = 0.029154` covers the
     Lean axiom's `[0.02905 + ε, 0.04)` requirement for all ε ∈ (0, 0.001).
   - **P1-1**: insert a one-paragraph X-class removal step in
     `paper/main.tex:355-366` (Lemma 3 justification).
   - **P1-2**: in `paper/main.tex:399-403`, distinguish "HP-2023 §8 application
     range `[n^{1.1}, n^{2.9}]`" from "Heckel 2024 (α−1) application threshold
     `n^{0.05+ε}` shifted to α−2 gives `n^{1.05}`"; either drop one or label
     both.
   - **P1-3**: replace `[1.65, 1.80]` with `[1.68, 1.80]` in
     `paper/main.tex:336` and `proof/proof.md:120`.
   - **P1-4**: keep `n^{1-ε/2}` symbolic in
     `axiom-paper-correspondence-audit-2026-05-12.md:189-192`, or insert
     "fixing ε ≤ 0.001 ⇒ 1 − ε/2 ≥ 0.9995" once.
   - **P2-1, P2-2, P2-3**: notational polish only.

---

## Routing ledger

| Route | State  | Verdict                                         |
|-------|--------|-------------------------------------------------|
| R1 threshold convention            | CLOSED | PASS                              |
| R2 four-theorem bounds             | CLOSED | PASS                              |
| R3 slack constants                 | CLOSED | PASS                              |
| R4 quantifier order                | CLOSED | PASS                              |
| R5 InMainRange / InMainRangeMod    | CLOSED | **P0-2** (Lean x₀ vs cert x₀)     |
| R6 χ-vs-χ_a direction              | CLOSED | **P1-1** (X-class step omitted)   |
| R7 Heckel 2024 anchor k*           | CLOSED | PASS                              |
| R8 gap arithmetic                  | CLOSED | PASS                              |
| R9 bibliographic accuracy          | CLOSED | **P1-2** (1.05 vs 1.1)            |
| R10 numerical certificate          | CLOSED | **P0-1** (6 OOM vs 1.2 OOM)       |
| R11 α-2 margin numerics            | CLOSED | **P1-3** (1.65 vs 1.68)           |

---

## Compact ledger

- **Target document**: `publish/erdos-625/` package
- **Focus**: mathematical exposition rigor (cross-document math consistency)
- **Counts**: **P0 = 2 · P1 = 4 · P2 = 3**
- **Headline list**:
  1. P0-1 — `lemma-7-10-ext-disclosure-2026-05-11.md:59,111` "6 orders of
     magnitude" margin contradicts ≈ 1.2 OOM in five sibling docs.
  2. P0-2 — `Defs.lean:176` `x₀ := 0.02905` (exact) vs certificate
     `x₀ = 0.02905439`; for ε_Lean < 0.000104 the Lean InMainRangeMod
     lower-bound lies below the certified ϕ-positivity interval.
  3. P1-1 — `paper/main.tex` Lemma 3 justification omits the X-class removal
     step `χ ≥ χ_{α-2} − X_α − X_{α-1}`; only Azuma deviation is named.
  4. P1-2 — `μ_{α-2} ≥ n^{1.05}` (α−2 transfer) vs `[n^{1.1}, n^{2.9}]`
     (HP-2023 §8 application range) used interchangeably.
  5. P1-3 — slope band `[1.65, 1.80]` (paper/proof.md) vs `[1.68, 1.80]`
     (red-team-erdos-625-full); canonical data minimum is 1.6783.
  6. P1-4 — `axiom-paper-correspondence-audit-2026-05-12.md:191` slides
     from `n^{1-ε/2}` to `n^{0.9995}` mid-derivation without flagging the
     ε = 0.001 substitution.
  7. P2-1 — `red-team-erdos-625-full-2026-05-11.md:30` mixes `Θ(n²/log²n)`
     with concrete `n^{2 − 2 loglog n / log n}` form, dropping the Θ constant.
  8. P2-2 — `paper/main.tex:80` "structural margin
     $\Theta(n²/\log²n·\mu_α)$" — parens scope-ambiguous (the ratio, not the
     product, is what is Θ).
  9. P2-3 — `axiom-paper-correspondence-audit-2026-05-12.md:19`
     "expectationu eq" typo.

### Ordered fix list for the repair round

1. **P0-1**. Replace "6 orders of magnitude" with "≈ 1.2 orders of magnitude
   (ratio ≈ 16-fold)" at
   `proof/red-team/lemma-7-10-ext-disclosure-2026-05-11.md:59` **and** `:111`.
2. **P0-2**. Reconcile `x₀ = 0.02905` (Lean) with `x₀ = 0.02905439`
   (certificate). Preferred fix: tighten `Erdos625/Defs.lean:176` to
   `noncomputable def x₀ : ℝ := 0.02905439` and re-run `lake build`. If the
   tighter rational changes proof obligations elsewhere, add a
   reconciliation paragraph to `proof/red-team/lemma_7_10_ext.md` §3 and
   `proof/red-team/lemma-7-10-ext-disclosure-2026-05-11.md` §"certificate
   details" stating that the certificate's `x_lo = 0.029154` covers the Lean
   axiom's `[0.02905 + ε, 0.04)` requirement for all ε ∈ (0, 0.001) (which
   it does **only** for ε ≥ 0.000104; the sub-ε regime needs an explicit
   ϕ(x) > 0 argument on `[0.02905 + ε, 0.029154)`).
3. **P1-1**. Insert in `paper/main.tex:355-366` (Lemma 3 justification) a
   paragraph: "HP-2023 Lemma 8.1 bounds $\chrom_a$, not $\chrom$. We use the
   X-class observation $\chrom \geq \chrom_{\alpha-2} - X_\alpha - X_{\alpha-1}$
   (Heckel 2024 §3, near eq. 433); in the crossing regime $\mu_\alpha <
   n^{x_0+\varepsilon}$ gives $X_\alpha = O(\log n)$ whp and $X_{\alpha-1} =
   O(n/\log n)$ whp by Markov, both absorbed by $n^{0.99}$ alongside the
   Azuma tail." Mirror this in `proof/proof.md:95-101`.
4. **P1-2**. In `paper/main.tex:399-403`, replace the bare "translates to
   $\mu_{\alpha-2}\geq n^{1.05}$" with "translates to $\mu_{\alpha-2}\geq
   n^{1.05}$ (the level-shift of Heckel~2024's $n^{0.05+\varepsilon}$
   condition at $\alpha-1$); this is the binding lower bound, well inside
   HP-2023~§8's broader application range $[n^{1.1},n^{2.9}]$ for Lemma~8.1
   applicability." Same disambiguation in
   `heckel2024-alpha-minus-two-transfer-audit-2026-05-11.md:60-65`.
5. **P1-3**. Replace `[1.65, 1.80]` with `[1.68, 1.80]` (or `[1.6, 1.8]`
   with explicit data-rounded language) in `paper/main.tex:336` and
   `proof/proof.md:120`. Keep the canonical `r2b-step1-results-2026-05-11.md`
   table as the source of truth.
6. **P1-4**. Keep `n^{1-\varepsilon/2}` symbolic through
   `axiom-paper-correspondence-audit-2026-05-12.md:189-192`, or insert
   "fixing $\varepsilon \le 0.001$ so $1-\varepsilon/2 \ge 0.9995$" once at
   line 189.
7. **P2-1, P2-2, P2-3**. Notational/typographical cleanup; address in the
   same pass as P1-1.

---

## Provenance

- **Generated**: 2026-05-12 publish-readiness round 4.
- **Worker model**: `claude-opus-4-7[1m]` (Claude Opus 4.7, 1M-context variant).
- **Operator orchestrator**: `operator` (https://github.com/uthunderbird/vibechord);
  codex-brain adapter ran `gpt-5.3-codex-spark` at `effort=low`.
- **Same-model caveat**: this artefact was produced by the same LLM-agent
  pipeline that produced the proof being critiqued; it is an **internal
  adversarial audit**, not a third-party review. LLM-generated proofs may
  exhibit plausibility-driven failure modes that survive same-model critique
  because the proof author and the critic share training-data blind spots. See
  `../../README.md` Provenance and `../../DEVELOPMENT.md` ADR-10/11/12 for the
  full methodology disclosure. External verification by an unrelated reader, a
  different model, or a human mathematician is encouraged.
