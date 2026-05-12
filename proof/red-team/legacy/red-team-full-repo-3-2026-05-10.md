# Red-Team Critique — Full Repository (Round 3) — Publish Discipline Focus

**Target**: `publish/erdos-625/` (publish-package relative; originally cited as the absolute author-side path).
**Date**: 2026-05-10
**Context**: Third red-team pass. Focus: (1) mathematical accuracy of "High-level proof idea" in README.md, (2) publish discipline excellence — all claims, cross-references, terminology at publication standard.

**Files reviewed**:
- `README.md` (207 lines, full)
- `proof/proof.md` (161 lines, full)
- `DEVELOPMENT.md` (110 lines, full)
- `paper/SOURCES.md` (67 lines, full)
- `Erdos625/README.md` (72 lines, full)
- `Erdos625/PublishableProof.lean` (348 lines, full)
- `Erdos625/extras/README.md`
- `lakefile.toml`, `lean-toolchain`, `.github/workflows/build.yml`
- `Erdos625/ChromaticConnection.lean` (targeted: X_α definition)
- `.gitignore` / `git ls-files work/` (publish hygiene check)

---

## Summary Verdict

**0 CRITICAL, 2 MINOR, 1 BOUNDED CONCERN.** The repository is in excellent shape for public release. All proof-path claims are accurate. The two MINOR issues are copy-propagation misses — the same errors that were fixed in `proof/proof.md` in Round 2 were not simultaneously propagated to `README.md`. No new mathematical errors were found.

Publish discipline is strong: no TODOs in public docs, no internal artifacts in git, no monorepo leakage, CI workflow correctly verifies axiom count, build system is clean.

---

## CRITICAL Issues

None.

---

## MINOR Issues

### M1 — README.md: Azuma tail formula drops factor of 2 (not fixed from proof.md)

**Severity**: MINOR

**Location**: `README.md`, §Part C — Cochromatic upper bound, line 81.

**Evidence**: README.md says:
> Setting $s = n^{0.999}$ makes the tail probability $e^{-n^{0.998}} = o(\varepsilon)$.

The Lean theorem `zeta_azuma_tail_bound` gives the tail bound `exp(-(t^2)/(2*n))`. With `t = n^{0.999}`, this evaluates to `exp(-n^{1.998}/(2n)) = exp(-n^{0.998}/2)`.

This exact error was fixed in `proof/proof.md` (commit 6c57709) but not propagated to `README.md`.

**Impact**: Cosmetic — the conclusion $o(\varepsilon)$ is correct either way. But a reader who checks the Lean proof against the README will find a discrepancy.

**Resolution**: Change `$e^{-n^{0.998}}$` to `$e^{-n^{0.998}/2}$` in README.md line 81.

---

### M2 — README.md: t defined as exact floor, not approximation (not fixed from proof.md)

**Severity**: MINOR

**Location**: `README.md`, §The threshold k*, line 43.

**Evidence**: README.md says:
> Define $k^* = k^*(n)$ as the *first-moment threshold* for $t$-bounded proper colorings of $G(n,1/2)$, where $t = \lfloor 2\log_2 n \rfloor$.

The Lean definition uses `t = thresholdFloor n - 1` where `thresholdFloor n = ⌊threshold n⌋₊` and `threshold n = 2log₂(n) − 2log₂(log₂(n)) + 2log₂(e/2) + 1`. This is approximately (but not exactly) `⌊2log₂ n⌋`.

This exact issue was corrected in `proof/proof.md` (commit 6c57709) to read `t ≈ 2 log₂ n (precisely: thresholdFloor n − 1 in Lean...)` but was not propagated to `README.md`.

**Impact**: A reader using the README as a reference for the formalization will get the wrong definition of t if they try to replicate it.

**Resolution**: Change `$t = \lfloor 2\log_2 n \rfloor$` to `$t \approx 2\log_2 n$` (with an optional Lean parenthetical, as in proof.md, or a footnote). The surrounding context already uses `\lfloor\rfloor` elsewhere so a brief qualifier is sufficient.

---

## BOUNDED CONCERNS

### BC1 — GitHub URL not locally verifiable (no git remote configured)

**Severity**: BOUNDED CONCERN

**Location**: `README.md`, §Building and verifying, line 150.

**Evidence**: The README instructs:
```bash
git clone https://github.com/erdosreshala-625/erdos-625-formalization
```
The local git repository has no remote configured (`git remote` returns empty). The URL cannot be verified from local files. The URL pattern looks intentional (not a generic placeholder), but could be the intended final URL or a pre-publication placeholder.

**Impact**: If the URL is wrong, a user's first action (clone) fails. This would be the most prominent friction point for adoption.

**Resolution**: Verify that `https://github.com/erdosreshala-625/erdos-625-formalization` is the correct final URL before publishing, and add a git remote (`git remote add origin <URL>`) so future CI has the correct upstream.

---

## Verified Correct (publish discipline checks)

| Check | Result |
|-------|--------|
| TODOs/FIXMEs in public docs (README, DEVELOPMENT, proof.md, SOURCES.md) | None found ✓ |
| Internal monorepo paths/artifacts in public docs | None found ✓ |
| `work/notes/` in git index | Untracked — not in public repo ✓ |
| CI workflow (.github/workflows/build.yml) | Correct: runs `lake build` + `#print axioms` ✓ |
| lakefile.toml | Clean: correct lib name, pinned Mathlib rev ✓ |
| `lean-toolchain` matches `lakefile.toml` rev | Both `v4.29.0-rc8` ✓ |
| Mechanism audit: "3 paper-backed axioms, 0 sorry on proof path" | CI verifies via `#print axioms`; hedged correctly ✓ |
| X_α described as "maximum independent sets" | Confirmed accurate: `maxIndepSetCount = indepSetCount G (G.indepNum)` ✓ |
| ζ ≤ χ framing in Part C | Logic is correct (motivates why trivial bound is insufficient) ✓ |
| k* asymptotic: k* = Θ(n/log n), n/k* → 2log₂ n | Correct ✓ |
| DEVELOPMENT.md: 5 clean ADRs, no internal metadata | Clean ✓ |
| Paper citations (arXiv IDs, Prop/Lemma numbers) | Consistent across README, SOURCES.md, proof.md ✓ |

---

## Compact Ledger

| ID | Severity | Category | Description |
|----|----------|----------|-------------|
| M1 | MINOR | Copy-propagation miss | README.md Azuma: `e^{-n^{0.998}}` should be `e^{-n^{0.998}/2}` |
| M2 | MINOR | Copy-propagation miss | README.md: `t = ⌊2log₂n⌋` should be `t ≈ 2log₂n` |
| BC1 | BOUNDED CONCERN | Publish readiness | GitHub URL unverified locally; confirm before release |

**Publication-ready?** Yes, after fixing M1 and M2. Both are one-line changes. BC1 requires out-of-band verification (the correct URL must be known to the author).

---

## Ordered Fix List

1. **M1**: `README.md` line 81 — change `$e^{-n^{0.998}}$` to `$e^{-n^{0.998}/2}$`
2. **M2**: `README.md` line 43 — change `$t = \lfloor 2\log_2 n \rfloor$` to `$t \approx 2\log_2 n$`
3. **BC1**: Verify GitHub URL and configure git remote before publishing

---

## Provenance

- **Generated**: 2026-05-11 / 2026-05-12 development window.
- **Worker model**: `claude-opus-4-7[1m]` (Claude Opus 4.7, 1M-context variant).
- **Operator orchestrator**: `operator` (https://github.com/uthunderbird/vibechord); codex-brain adapter ran `gpt-5.3-codex-spark` at `effort=low`.
- **Same-model caveat**: this artefact was produced by the same LLM-agent pipeline that produced the proof being critiqued; it is an **internal adversarial audit**, not a third-party review. LLM-generated proofs may exhibit plausibility-driven failure modes that survive same-model critique because the proof author and the critic share training-data blind spots. See `../../README.md` Provenance and `../../DEVELOPMENT.md` ADR-10 / ADR-11 / ADR-12 for the full methodology disclosure. External verification by an unrelated reader, a different model, or a human mathematician is encouraged.
- **Footer added**: round-2 publish-readiness repair, 2026-05-12 (P1-7).
