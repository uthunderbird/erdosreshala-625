# R2B Step 1 — Numerical Results

> **Path-context note (2026-05-12).** This artefact was authored against the source repository where work artefacts live at `problems/625/work/...`. In the `publish/erdos-625/` package those paths do not exist; this file's publish-package location is `proof/red-team/r2b-step1-results-2026-05-11.md` and the script is at `proof/red-team/r2b_step1_scan.py`. Path references below preserve the original-context wording for historical fidelity.

**Date**: 2026-05-11
**Scan range (Pass A)**: n ∈ [100, 1000000], step 1, float64 (lgamma)
**Target**: x_{α−2}(n) ≥ 1.05; bad ⇔ x_α < x₀ + 0.001 ≈ 0.03005 (using rounded x₀ ≈ 0.02905; exact x₀ = 0.02905439 — scan used the rounded boundary, which is slightly more permissive than the tight Lean definition and so over-counts "bad" n by a vanishing amount)
**Source CSV**: `problems/625/work/notes/r2b-step1-mu-alpha-minus-2-2026-05-11.csv`

## Headline

- **Verdict**: **CAUTIOUS-GO (C2: min bad margin ∈ [0.10, 0.50))**
- n scanned (Pass A): 999,901
- bad n: 34,636 (3.464%)
- min margin over **bad** n: 0.483244
- min margin over **all** n: 0.483244
- max margin over all n: 1.427041

## Histogram of margins over bad n (10 buckets)

Range: [0.483244, 0.681051]

- [0.4832, 0.5030): 3
- [0.5030, 0.5228): 7
- [0.5228, 0.5426): 11
- [0.5426, 0.5624): 30
- [0.5624, 0.5821): 77
- [0.5821, 0.6019): 229
- [0.6019, 0.6217): 804
- [0.6217, 0.6415): 3242
- [0.6415, 0.6613): 15007
- [0.6613, 0.6811): 15226

## 10 worst-margin bad n (float64)

| n | α | x_α | x_{α−1} | x_{α−2} | margin |
|---|---|---|---|---|---|
| 108 | 10 | 0.020467 | 0.863200 | 1.533244 | 0.483244 |
| 163 | 11 | 0.011963 | 0.855925 | 1.543818 | 0.493818 |
| 245 | 12 | 0.001175 | 0.847201 | 1.550637 | 0.500637 |
| 164 | 11 | 0.025563 | 0.867235 | 1.553034 | 0.503034 |
| 246 | 12 | 0.010258 | 0.854883 | 1.557027 | 0.507027 |
| 247 | 12 | 0.019291 | 0.862523 | 1.563382 | 0.513382 |
| 369 | 13 | 0.001506 | 0.848258 | 1.563727 | 0.513727 |
| 370 | 13 | 0.007554 | 0.853445 | 1.568115 | 0.518115 |
| 248 | 12 | 0.028272 | 0.870119 | 1.569702 | 0.519702 |
| 371 | 13 | 0.013579 | 0.858614 | 1.572487 | 0.522487 |

## Pass C — mpmath dps=50 spot checks (n = 10^7 … 10^12)

Theoretical: x_{α−2} − x_α ≈ 2 − 2·log log n / log n (HP-2023 Lemma 6.2 ratio).

| n | α | x_α | x_{α−2} | x_{α−2}−x_α | predicted 2−2·loglog/log | margin |
|---|---|---|---|---|---|---|
| 10^7 | 39 | 0.518165 | 2.196465 | 1.6783 | 1.6551 | 1.1465 |
| 10^8 | 45 | 0.737811 | 2.423595 | 1.6858 | 1.6837 | 1.3736 |
| 10^9 | 52 | 0.103064 | 1.861687 | 1.7586 | 1.7075 | 0.8117 |
| 10^10 | 58 | 0.402625 | 2.156194 | 1.7536 | 1.7276 | 1.1062 |
| 10^11 | 64 | 0.729101 | 2.477671 | 1.7486 | 1.7448 | 1.4277 |
| 10^12 | 71 | 0.167566 | 1.962527 | 1.7950 | 1.7598 | 0.9125 |

## Pass D — mpmath dps=50, ±5 neighbourhoods of 10 worst-margin bad n

| n | α | x_α | x_{α−2} | bad | margin |
|---|---|---|---|---|---|
| 103 | 9 | 0.776289 | 1.974989 | 0 | 0.924989 |
| 104 | 9 | 0.794163 | 1.985883 | 0 | 0.935883 |
| 105 | 9 | 0.811785 | 1.996625 | 0 | 0.946625 |
| 106 | 9 | 0.829162 | 2.007216 | 0 | 0.957216 |
| 107 | 9 | 0.846298 | 2.017662 | 0 | 0.967662 |
| 108 | 10 | 0.020467 | 1.533244 | 1 | 0.483244 |
| 109 | 10 | 0.040938 | 1.546480 | 0 | 0.496480 |
| 110 | 10 | 0.061135 | 1.559539 | 0 | 0.509539 |
| 111 | 10 | 0.081064 | 1.572425 | 0 | 0.522425 |
| 112 | 10 | 0.100731 | 1.585142 | 0 | 0.535142 |
| 113 | 10 | 0.120142 | 1.597694 | 0 | 0.547694 |
| 158 | 10 | 0.797855 | 2.036100 | 0 | 0.986100 |
| 159 | 10 | 0.809677 | 2.043750 | 0 | 0.993750 |
| 160 | 10 | 0.821394 | 2.051332 | 0 | 1.001332 |
| 161 | 10 | 0.833006 | 2.058847 | 0 | 1.008847 |
| 162 | 10 | 0.844516 | 2.066295 | 0 | 1.016295 |
| 163 | 11 | 0.011963 | 1.543818 | 1 | 0.493818 |
| 164 | 11 | 0.025563 | 1.553034 | 1 | 0.503034 |
| 165 | 11 | 0.039045 | 1.562170 | 0 | 0.512170 |
| 166 | 11 | 0.052411 | 1.571228 | 0 | 0.521228 |
| 167 | 11 | 0.065663 | 1.580208 | 0 | 0.530208 |
| 168 | 11 | 0.078802 | 1.589113 | 0 | 0.539113 |
| 169 | 11 | 0.091831 | 1.597942 | 0 | 0.547942 |
| 240 | 11 | 0.808125 | 2.083484 | 0 | 1.033484 |
| 241 | 11 | 0.816030 | 2.088843 | 0 | 1.038843 |
| 242 | 11 | 0.823890 | 2.094172 | 0 | 1.044172 |
| 243 | 11 | 0.831704 | 2.099471 | 0 | 1.049471 |
| 244 | 11 | 0.839475 | 2.104739 | 0 | 1.054739 |
| 245 | 12 | 0.001175 | 1.550637 | 1 | 0.500637 |
| 246 | 12 | 0.010258 | 1.557027 | 1 | 0.507027 |
| 247 | 12 | 0.019291 | 1.563382 | 1 | 0.513382 |
| 248 | 12 | 0.028272 | 1.569702 | 1 | 0.519702 |
| 249 | 12 | 0.037204 | 1.575986 | 0 | 0.525986 |
| 250 | 12 | 0.046085 | 1.582235 | 0 | 0.532235 |
| 251 | 12 | 0.054918 | 1.588450 | 0 | 0.538450 |
| 252 | 12 | 0.063703 | 1.594631 | 0 | 0.544631 |
| 253 | 12 | 0.072439 | 1.600777 | 0 | 0.550777 |
| 364 | 12 | 0.822034 | 2.128279 | 0 | 1.078279 |
| 365 | 12 | 0.827318 | 2.131998 | 0 | 1.081998 |
| 366 | 12 | 0.832582 | 2.135703 | 0 | 1.085703 |
| 367 | 12 | 0.837827 | 2.139394 | 0 | 1.089394 |
| 368 | 12 | 0.843052 | 2.143072 | 0 | 1.093072 |
| 369 | 13 | 0.001506 | 1.563727 | 1 | 0.513727 |
| 370 | 13 | 0.007554 | 1.568115 | 1 | 0.518115 |
| 371 | 13 | 0.013579 | 1.572487 | 1 | 0.522487 |
| 372 | 13 | 0.019583 | 1.576843 | 1 | 0.526843 |
| 373 | 13 | 0.025565 | 1.581184 | 1 | 0.531184 |
| 374 | 13 | 0.031525 | 1.585508 | 0 | 0.535508 |
| 375 | 13 | 0.037464 | 1.589817 | 0 | 0.539817 |
| 376 | 13 | 0.043381 | 1.594110 | 0 | 0.544110 |

## Check criteria (from plan §6)

- **C1** (≥0.50 ⇒ GO): min bad margin = 0.4832 → FAIL
- **C2** ([0.10,0.50) ⇒ cautious GO): TRIGGERED
- **C3** (<0.10 ⇒ NO-GO): n/a
- **C4** (x_{α−2}−x_α ∈ [1.6, 2.05] for n ≥ 10^10): slopes = ['1.678', '1.686', '1.759', '1.754', '1.749', '1.795'] → PASS
- **C5** (bad density at 10^6 ≈ 3.5% ± 0.5%): observed 3.464% → PASS
- **C6** (mpmath agrees with float64 to 3 sig figs near worst-margin n): see Pass D table; agreement to ≥4 decimals across all rows expected (visual check).

## Verdict

**CAUTIOUS-GO (C2: min bad margin ∈ [0.10, 0.50))**

## Reproduction — commands executed (2026-05-11)

```bash
# Install mpmath into the homebrew python (required for Pass C/D dps=50)
/opt/homebrew/bin/python3 -m pip install --user --break-system-packages mpmath

# Smoke test on a small window
/opt/homebrew/bin/python3 problems/625/work/notes/scripts/r2b_step1_scan.py \
  --n-lo 100 --n-hi 5000 --skip-cd \
  --csv /tmp/r2b_smoke.csv --md /tmp/r2b_smoke.md

# Full Pass A (n∈[100,10^6]) + Pass C (n∈{10^7..10^12}) + Pass D (±5 around 10 worst-margin bad n)
/opt/homebrew/bin/python3 problems/625/work/notes/scripts/r2b_step1_scan.py
# elapsed: ~19 s (Pass A 16.3 s, Pass C/D ~2 s)
```

## Files produced

- Script: `problems/625/work/notes/scripts/r2b_step1_scan.py`
- Raw CSV (Pass A + C + D combined): `problems/625/work/notes/r2b-step1-mu-alpha-minus-2-2026-05-11.csv` (≈ 1M rows, ~70 MB)
- Summary (this file): `problems/625/work/notes/r2b-step1-results-2026-05-11.md`

## Roadmap update

`problems/625/work/notes/roadmap-full-proof-2026-05-10.md` §"Recommended nearest action"
updated 2026-05-11 to mark Step 1 DONE (CAUTIOUS-GO, treated as GO for the asymptotic
formalization target) and to queue **R2B Step 2** (formal HP-2023 Lemma 8.1 analogue
for (α−2)-bounded colourings) as the next live item.

---

## Provenance

- **Generated**: 2026-05-11 / 2026-05-12 development window.
- **Worker model**: `claude-opus-4-7[1m]` (Claude Opus 4.7, 1M-context variant).
- **Operator orchestrator**: `operator` (https://github.com/uthunderbird/vibechord); codex-brain adapter ran `gpt-5.3-codex-spark` at `effort=low`.
- **Same-model caveat**: this artefact was produced by the same LLM-agent pipeline that produced the proof being critiqued; it is an **internal adversarial audit**, not a third-party review. LLM-generated proofs may exhibit plausibility-driven failure modes that survive same-model critique because the proof author and the critic share training-data blind spots. See `../../README.md` Provenance and `../../DEVELOPMENT.md` ADR-10 / ADR-11 / ADR-12 for the full methodology disclosure. External verification by an unrelated reader, a different model, or a human mathematician is encouraged.
- **Footer added**: round-2 publish-readiness repair, 2026-05-12 (P1-7).
