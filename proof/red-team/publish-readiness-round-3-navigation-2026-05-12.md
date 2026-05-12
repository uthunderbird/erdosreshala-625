# Publish-readiness round 3 — Self-containment & navigation

**Target document**: the entire `publish/erdos-625/` package.
**Round**: 3 of 5 (focus: SELF-CONTAINMENT & NAVIGATION; first-time-visitor experience).
**Conducted by**: `/swarm-red-team` (internal adversarial-audit pipeline, same LLM-agent pipeline that produced the proof; not a third-party review — see `../../README.md` Provenance and `../../DEVELOPMENT.md` ADR-10).
**Date**: 2026-05-12.
**Walk order**: `README.md` → `ROADMAP.md` → `DEVELOPMENT.md` → `proof/proof.md` → `paper/main.tex` → `paper/SOURCES.md` → `Erdos625/README.md` → `Erdos625/extras/README.md` → `proof/AXIOM_SNAPSHOT.txt` → `proof/red-team/README.md` → `proof/red-team/` (14 audit artefacts) → `proof/red-team/legacy/` (3 archived) → `proof/methodology/README.md`. Filesystem reads, `grep` on internal-link targets, physical line-count against Lean files.

**Out of scope** (covered in rounds 1 and 2, not re-litigated): honesty of the prize disclaimer, framing of LLM-provenance, ADR-authorship of axioms, operator-framework citation, methodology directory existence.

**Mechanism claim under audit**: *first-time hostile-but-literate visitor can verify and audit the core claim within 5 minutes without thrashing across broken links, contradictory facts, or mislabeled identifiers.*

---

## Setup

Team: Aaron Swartz (Critic · Completer-Finisher), Sebastian Ullrich (Critic · Implementer), Karen McGrane (Critic · Reframer), Donald Knuth (Monitor-Evaluator). Evidence boundary: filesystem reads + grep against `publish/erdos-625/` only. No live web fetch; arXiv IDs verified syntactically. Lean line numbers physically counted against the live files (`PublishableProof.lean` 735 lines, `CrossingPartB.lean` 320 lines, `PartBAlphaMinusTwoFirstMomentAxiom.lean` 57 lines, `PartBProfileBridge.lean` 29512 lines, `ChromaticConnection.lean` 4158 lines, `ZetaConcentration.lean` 2162 lines).

---

## P0 findings (contradictions, broken links, wrong identifiers)

### P0-1. Lean file:line references in `paper/SOURCES.md` are stale

Per-axiom file:line citations in `paper/SOURCES.md` point at the wrong lines after the post-rename docstring expansions of 2026-05-12:

| Axiom | `SOURCES.md` claim | Actual `axiom` declaration line | Drift |
|---|---|---|---|
| A1 `lemma_7_20_modified` | `Erdos625/PublishableProof.lean:398` (line 22) | line **399** | off by 1 |
| A2 `partB_alphaMinusTwo_firstMomentBelowOne_source` | `PartBAlphaMinusTwoFirstMomentAxiom.lean:50` (line 49) | line **50** | OK |
| A3 `chi_alphaMinusTwo_lower_bound_whp` | `Erdos625/CrossingPartB.lean:251` (line 68) | line **263** | off by 12 |
| A4 `zeta_alphaMinusTwo_upper_bound_whp` | `Erdos625/CrossingPartB.lean:293` (line 88) | line **311** | off by 18 |

Evidence:
```
$ grep -n '^axiom lemma_7_20_modified\|^axiom chi_alphaMinusTwo_lower_bound_whp\|^axiom zeta_alphaMinusTwo_upper_bound_whp\|^axiom partB_alphaMinusTwo_firstMomentBelowOne_source' \
       Erdos625/PublishableProof.lean Erdos625/CrossingPartB.lean Erdos625/PartBAlphaMinusTwoFirstMomentAxiom.lean
Erdos625/PublishableProof.lean:399:axiom lemma_7_20_modified (...)
Erdos625/CrossingPartB.lean:263:axiom chi_alphaMinusTwo_lower_bound_whp (...)
Erdos625/CrossingPartB.lean:311:axiom zeta_alphaMinusTwo_upper_bound_whp (...)
Erdos625/PartBAlphaMinusTwoFirstMomentAxiom.lean:50:axiom partB_alphaMinusTwo_firstMomentBelowOne_source :
```

Impact: a referee or hostile reader who follows the SOURCES.md citation to "audit the axiom against the cited paper" lands in the middle of a docstring block instead of on the axiom signature. The mechanism claim that "every paper-backed axiom is one click away from its Lean source" fails by 1, 12, and 18 lines respectively. This is the classic post-rename + post-docstring-expansion file:line drift, and is screenshot-quotable.

Result type: **verified issue**.

---

### P0-2. Internal contradiction: how many audit artefacts are in `proof/red-team/`?

Three different numbers appear, in three documents, inside the same package:

- `README.md:245`: "**Index** over the **14 audit artefacts** (chronological, with one-line summaries...)".
- `README.md:246`: "Audit artefacts: **11 Markdown notes** (five internal red-team audit passes + per-axiom paper-correspondence audit + numerical-certificate disclosure + α-2 transfer audit + a `lemma_7_10_ext` summary + an axiom-check snapshot + **this round's publish-readiness audit**), 2 Python reproducibility scripts, and a `legacy/` subdirectory."
- `proof/red-team/README.md:3`: "All **14 artefacts** indexed below".
- `proof/red-team/README.md:24-25`: "The **14 artefacts** (**11 in this directory** including the **3-file `legacy/` subdirectory**; the 2 paper-targeted critiques live in `../../paper/` and are listed at the bottom of this index for discoverability)."
- `proof/red-team/README.md` chronological table: **18 rows** (verified via `awk '/^\| 2026/{c++} END{print c}'`).

Filesystem reality:
```
$ ls proof/red-team/ | wc -l           # 16 (13 .md including README + 2 .py + 1 legacy/ subdir)
$ ls proof/red-team/legacy/*.md | wc -l # 3 (incl. legacy/README.md)
$ ls paper/red-team-paper*.md | wc -l   # 2
```

The arithmetic does not close:
- "11 in this directory including the 3-file legacy/ subdirectory" → 11 ≠ (12 top-level .md non-README) + (3 legacy) = 15.
- "11 Markdown notes ... 2 Python ... + legacy/" → 11 .md + 2 .py = 13 ≠ 14 in the same README two lines earlier.
- The index table at `proof/red-team/README.md:31-48` enumerates 18 rows but the surrounding prose says "14 artefacts".

In addition, `README.md:246` says the 11-Markdown-notes set includes "**this round's publish-readiness audit**" — but at the time the README was last edited, this round-3 audit had not yet been written. The "this round's" phrase is a forward reference to an artefact that did not exist when the sentence was authored (and only exists after this document is committed).

Impact: a hostile reader counts entries with `ls`, sees 16, opens README, reads "14", opens the index, reads "All 14" plus "11 in this directory" plus a table with 18 rows, and screenshots the contradiction. The package's own meta-narrative cannot describe its own audit trail without contradicting itself.

Result type: **verified issue**.

---

### P0-3. Stale repo-internal paths bleed into the published package

Multiple audit artefacts and methodology files reference paths that exist only in the source repo `~/Projects/erdosreshala/problems/625/work/notes/...` and **do not exist** under `publish/erdos-625/`. A standalone-publish visitor following these instructions hits dead ends.

Concrete instances:

- `proof/red-team/r2b-step1-plan-2026-05-11.md:86,94,139–142`: "Single CSV `problems/625/work/computations/r2b-step1-mu-alpha-minus-2-2026-05-11.csv`", "Companion summary `problems/625/work/computations/r2b-step1-summary-2026-05-11.md`", "`problems/625/work/scripts/r2b_step1_scan.py`", etc. None of these paths exist in `publish/erdos-625/`. The script that does exist is at `proof/red-team/r2b_step1_scan.py`.

- `proof/red-team/r2b_step1_scan.py:5,22-23,26,347,349`: docstring header reads "Implements Passes A–D of `problems/625/work/notes/r2b-step1-plan-2026-05-11.md` §4." and the CLI default output paths are `Path("problems/625/work/notes/r2b-step1-mu-alpha-minus-2-2026-05-11.csv")`. A visitor running the script from a fresh checkout of the publish package will write into a non-existent directory.
  ```
  problems/625/work/notes/scripts/r2b_step1_scan.py    # the invocation example in the docstring
  ```

- `proof/red-team/lemma-7-10-ext-disclosure-2026-05-11.md:107`: cites `problems/625/work/notes/lemma_7_10_ext.md` (in publish/ the file is at `proof/red-team/lemma_7_10_ext.md`).

- `proof/red-team/lemma_7_10_ext.md:254`: "cd /path/to/problems/625/work/notes" — a reproduction instruction that points to a path that does not exist in the publish package.

- `proof/red-team/red-team-erdos-625-full-2026-05-11.md:39,169,171,173,175`: cites `problems/625/work/notes/r2b-step1-results-2026-05-11.md`, `problems/625/work/heckel2023/TameColourings.tex` (the local mirror of HP-2023 source, *not shipped* in publish/), `problems/625/work/notes/n6-literature-scan-2026-05-11.md`. The first of these has a publish-side equivalent at `proof/red-team/r2b-step1-results-2026-05-11.md` but the link does not update.

- `proof/red-team/r2b-step1-results-2026-05-11.md:6,135,140,146-147`: same pattern — `Source CSV: problems/625/work/notes/...` and reproduction instructions pointing to repo-internal paths.

- `proof/red-team/red-team-proof-md-2026-05-12.md:3`: "**Target document:** `/Users/thunderbird/Projects/erdosreshala/publish/erdos-625/proof/proof.md`" — a **local absolute path**. In a public repository this exposes the author's home directory layout and is non-portable.

- `proof/methodology/operator-profile.yaml:39,42-43`: "Active roadmap: `problems/625/work/notes/roadmap-full-proof-2026-05-10.md`", "`problems/625/work/notes/` — all swarm/red-team session artifacts (380+ files)", "`problems/625/work/notes/blockers/`". None of these paths are reachable from `publish/erdos-625/`. The profile file is shipped as-is from the source repo and was not adapted for publication.

- `proof/methodology/operator-harnesses/erdos-metadata-harness.txt:4,12`: "`/Users/thunderbird/Projects/erdosreshala/problems/<id>/`" and "`python3 /Users/thunderbird/Projects/erdosreshala/scripts/list_unmarked_problems.py`" — absolute home-directory paths and a script that is not in publish/.

- `Erdos625/PublishableProof.lean:308`: inside a documentation comment block (the axiom-closure verification section header): "See also \"Lean Formalization\" in `problems/625/solution/proof.md`". The publish-side file is at `proof/proof.md`, not `problems/625/solution/proof.md`.

Impact: every one of these is a navigation dead end for a fresh-clone visitor. Particularly damaging: `r2b_step1_scan.py` is one of the two reproducibility scripts the package advertises (ROADMAP §reproducibility, line 155-156); its own docstring sends the visitor to a non-existent location.

Result type: **verified issue**.

---

### P0-4. Pre-rename `partBThresholdWitness` identifier still appears in audit artefacts dated 2026-05-12

ADR-9 (DEVELOPMENT.md:226-251) records the rename of the Lean identifier `partBThresholdWitness` → `kThresholdAlphaMinusOne`, applied 2026-05-12, with the explicit rationale that "the recurring P0-risk in this project has been silent threshold-convention errors". The Lean source has been swept; the audit artefacts have not. Eight verbatim occurrences remain in five files dated 2026-05-12 (the same day as the rename):

- `proof/red-team/axiom-paper-correspondence-audit-2026-05-12.md:16,18,42,43,47,53,59,108,222,226,236` — 11 occurrences. The most damaging are lines 16 and 18, which appear in the headline summary table of the per-axiom audit: "Lean: `∀ k < partBThresholdWitness n + ⌈n/log²n⌉, E_{n,k,α-2} < 1`" and "Lean: `ζ(G) ≤ partBThresholdWitness n + n^{0.99} = boldk_{α-1} + n^{0.99}` whp in crossing case". A reader who has read the canonical README (where the name is `kThresholdAlphaMinusOne`) and clicks into this per-axiom audit is told the Lean identifier is `partBThresholdWitness`, with no explanatory note that the name has been changed.
- `proof/red-team/red-team-strict-lemma-by-lemma-2026-05-12.md:160,179` — uses `partBThresholdWitness` and `kThresholdAlphaMinus2` mixed in the same passage. This is the audit that surfaced the rename; retention is historically defensible but no header note flags "the pre-rename name was `partBThresholdWitness`; per ADR-9 it is now `kThresholdAlphaMinusOne`".
- `proof/red-team/erdos-625-full-axiom-check-2026-05-11.md:93,95` — pseudocode of the proof structure using the pre-rename name.
- `paper/red-team-paper-2026-05-12.md:21,107,202,227` — references to the F5 finding that surfaced the rename; the body text uses `partBThresholdWitness` verbatim. R4/F5 is marked **CLOSED** in the artefact's own ledger, but a reader who searches the paper bibliography for the Lean name on the strength of these audits will not find anything in the canonical source.

Impact: a visitor cross-checking the package's claim that `kThresholdAlphaMinusOne` is the canonical Lean name for $\mathbf{k}_{\alpha-1}(n)$ — by going to the audit artefacts the package advertises as evidence — encounters an identifier that no longer exists in the Lean source. The rename was per ADR-9 specifically motivated by "closing the recurring threshold-convention risk surface"; failing to sweep the audit trail re-opens that surface from the documentation side.

Result type: **verified issue**.

---

## P1 findings (rendering hazards, landing-flow drag, suboptimal discoverability)

### P1-1. Landing-flow disclosure-wall on README.md

The first 70 lines of `README.md` are dominated by disclaimers, before the visitor reaches actionable content:

- Lines 1-6: theorem statement (4 lines of LaTeX-in-markdown).
- Lines 8-58: **50-line "Provenance" blockquote** (LLM-agent disclosure + limitation framing + reject ratio + Anthropic non-endorsement). All necessary content per rounds 1 and 2, but rendered as a single block before the visitor sees the axiom inventory or the build command.
- Lines 60-69: **prize disclaimer blockquote** (10 lines).
- Lines 71-87: build status + sorry footnote (positive content begins).

Total: ~62 of the first 90 lines are blockquotes. On a 1080p laptop or a typical mobile viewport, the entire first screen is wall-of-blockquote. A hostile first-time visitor whose claim is "5 minutes to verify" must scroll past two large disclaimer blocks before reaching the canonical axiom inventory at line 143. No TOC, no quick-nav anchors ("Jump to: Theorem · Axioms · Build · Red-team trail · References") to mitigate.

This is not a P0 because all six landing-flow items (theorem, axiom count, build, scope, red-team entry, LLM-provenance) are reachable within 5 minutes if the visitor scrolls past the walls. But the mechanism claim "without thrashing" is fragile: the disclaimers compress the verification path against the bottom of the document and trade landing-flow ergonomics for disclosure prominence. Round 1 and 2 deliberately ranked prominence over ergonomics; round 3 surfaces the cost.

Result type: **bounded concern**.

---

### P1-2. `proof/red-team/README.md` (the audit-trail index) is not linked from `paper/main.tex` or by-name from `proof/proof.md`

The round-2 repair pass added `proof/red-team/README.md` as a chronological index of the 14 (or 11, or 18 — see P0-2) audit artefacts. Round 2 P1-6 was explicit: "Cross-link from the main README.md audit-trail bullet." The cross-link from `README.md:245` is in place. But:

- `paper/main.tex` (the companion paper) never mentions `proof/red-team/README.md` by name. It cites individual files via `\path{proof/red-team/heckel2024-...}` and `\path{proof/red-team/r2b-step1-results-...}` and `\path{proof/red-team/lemma-7-10-ext-disclosure-...}` and `\path{proof/red-team/num-gap-lemma710-extension-...}` (lines 326, 395, 511, 516, 552). The paper's Acknowledgments (lines 597-638) talks about "five internal red-team audit passes" but does not point to the index. A reader reading only the PDF cannot navigate to the index.
- `proof/proof.md:187`: "**Red-team artefacts**: see `red-team/` for the full audit trail". This is a directory pointer, not a file pointer to the index. On GitHub the directory listing will show README.md and the visitor will infer to click it; but a `proof.md` reader who is reading the file outside GitHub (e.g. via `cat`) does not get the cue.
- The index is also not linked from `DEVELOPMENT.md` ADR-10/ADR-11/ADR-12, which are the obvious cross-references when those ADRs talk about "the five red-team passes".

Impact: discoverability of the audit-trail index is uneven; paper readers and `proof.md`-only readers do not find it.

Result type: **bounded concern**.

---

### P1-3. `proof/methodology/README.md` is not linked from `paper/main.tex` Acknowledgments or `DEVELOPMENT.md` ADR-12

The methodology directory was added in round 2 specifically to address P1-2 of round 2 ("the publish package previously named only the Lean-side reproducibility inputs ... and was silent on the agent-side inputs"). It is linked from:

- `README.md:247` (repository layout table — generic mention).
- `ROADMAP.md:158-164` (reproducibility section — adequate).

It is **not** linked from:

- `paper/main.tex` Acknowledgments (lines 597-669), where the LLM-agent provenance is disclosed and where a reader scoring the methodology would expect a pointer to the agent-side reproducibility artefacts.
- `DEVELOPMENT.md` ADR-10, ADR-11, or ADR-12 — ADR-12 is the obvious anchor since it discusses HIL granularity and cross-model auditing, both of which the methodology directory documents.
- `proof/proof.md` — the proof writeup does not point at the methodology directory at all.

Impact: a visitor reading the paper Acknowledgments and wanting to find the operator-profile yaml or the harness instructions has to figure out that they live under `proof/methodology/` from the repo-layout table in README.md. Round 2 P1-2 fixed the existence of the directory; round 3 surfaces that it is hard to find from the documents most likely to send a reader there.

Result type: **bounded concern**.

---

### P1-4. `ZetaConcentration.lean:33` file header is stale

The header at line 33 of `Erdos625/ZetaConcentration.lean` reads:

> **CURRENT STATE (verified 2026-05-10)**: 1 sorry (architectural only, not load-bearing), 1 load-bearing axiom:
> - `heckel_cochromatic_second_moment` (load-bearing axiom, Heckel 2024 Proposition 5(b), used via `heckel_zeta_paley_zygmund`)

But `paper/SOURCES.md:119-122` (`erdos_625` legacy axiom section) says:

> `Problem625.heckel_offdiag_term_bound` — Heckel 2024 Prop 5(b) off-diagonal term (a 2026-05-11 narrowing of the original `heckel_cochromatic_second_moment`, which is now a proved theorem on top of `heckel_offdiag_term_bound`).

A reader who opens the supporting Lean module (advertised at `Erdos625/README.md:90`) sees a header announcing that `heckel_cochromatic_second_moment` is a load-bearing axiom; the canonical SOURCES.md says it is now a proved theorem. The reader cannot tell which is current. Also: `Erdos625/README.md:80` says "the file's own header at line ~33 calls it 'architectural only, not load-bearing'" — that part is fine (the sorry is described correctly); the staleness is about the *axiom* it lists, not the sorry.

Result type: **verified issue**, P1 because it lives in a supporting (non-flagship-path) module.

---

### P1-5. `n^{0.99}` vs `n^{0.999}` slack constants — different regimes, never disambiguated

Two slack constants appear in the package:

- **`n^{0.99}`** — used by the **crossing-case axioms** (A3 and A4) in their Lean statements (`CrossingPartB.lean:263, 311`), and propagated through `README.md:128, 197`, `ROADMAP.md:16`, `proof/proof.md:69, 75, 95, 97, 101`, `paper/main.tex:281, 289, 349, 354, 361, 372, 422-430`, `paper/SOURCES.md:75`.
- **`n^{0.999}`** — used by the **good-case (Heckel 2024 / InMainRange) chain**. Appears in `DEVELOPMENT.md:47, 63` (ADR-2 and ADR-3 questions) and `proof/proof.md:87` ("`ζ ≤ k_{α-1} − n^{1-ε/2} + 2·n^{0.999}` whp" — the good-case Heckel bound).

Both are correct; they refer to different regimes (crossing vs InMainRange). But the package never explicitly states "the good case uses `n^{0.999}`; the crossing case uses `n^{0.99}`". A reader scanning the proof outline and seeing both numbers within 30 lines of each other has no way to distinguish whether this is a typo or an intentional regime split.

Result type: **bounded concern**, P1 because both numbers are mathematically defensible and the contradiction is in clarity, not correctness.

---

### P1-6. `paper/main.tex` ε-range inconsistency between Layer 4 and Layer 4'a

- All four theorem statements are scoped to `ε ∈ (0, 0.001)` (`paper/main.tex:63, 125, 264, 347, 370, 400, 571`).
- `paper/main.tex:254` defines `InMainRangeMod` and notes "We have $\xnaught+\varepsilon < 0.04$ for $\varepsilon < 0.01$" — a wider range used in the definition.
- `paper/main.tex:291-292` (Layer-4 rpow comparison): "since `n^{-ε} + 2n^{ε-0.01} → 0` for `ε ∈ (0, 0.01)`". This is the helper lemma's natural range.

The helper-lemma range `ε ∈ (0, 0.01)` is wider than the flagship's `(0, 0.001)`, and the helper is invoked only at `ε ∈ (0, 0.001)`, so there is no logical problem. But a fast-scanning reader sees `ε < 0.01` and `ε < 0.001` within the same theorem chain and cannot immediately tell which is the binding range. A one-sentence "the helper is stated for ε < 0.01 to keep the statement clean; the flagship only invokes it at ε < 0.001" would close this.

Result type: **speculative concern**, P1.

---

### P1-7. LaTeX in markdown tables — mobile-rendering hazard

`README.md:124-129`, `ROADMAP.md:13-17`, and `proof/proof.md:65-70` all use markdown tables with `$...$`-delimited math in cells. GitHub's mobile renderer (and several non-GitHub renderers including some VS Code preview plugins) is known to render `$n^{1-\varepsilon}$` inside table cells as plaintext `$n^{1-\varepsilon}$` rather than as math. The flagship table at `README.md:124-129` is the **single most important reference table in the package** (the four-theorem coverage hierarchy) and the visual integrity of the bound column depends on GitHub correctly rendering `$\chi-\zeta \ge n^{1-\varepsilon}$` etc.

Additionally, the bolded flagship row uses `$\boldsymbol{\chi-\zeta \ge n^{1-2\varepsilon}}$` and `$\boldsymbol{100\%}$` — `\boldsymbol` inside a markdown-table `$...$` is on the edge of what GitHub's MathJax handles consistently across browsers.

Result type: **bounded concern**, P1.

---

### P1-8. Emoji in tables (⭐ and ✅) — non-uniform cross-browser rendering

- `README.md:129` and `proof/proof.md:70`: `**erdos_625_full_clean** ⭐` (flagship indicator).
- `ROADMAP.md:14-17`: `✅ proved` (status column, 4 rows).

Both render on GitHub, but ⭐ is part of a bolded label in a narrow column; on mobile the cell wraps with the star on a separate line, breaking the visual emphasis. ✅ is in a "Status" column where text "proved" would render identically without the cross-platform variation.

Result type: **speculative concern**, P1.

---

### P1-9. Table cells in `README.md:147-150` (the axiom-inventory table) hold long underscored identifiers + filenames

```
| `lemma_7_20_modified`                              | `PublishableProof.lean`                  | **hybrid:** ...    |
| `partB_alphaMinusTwo_firstMomentBelowOne_source`   | `PartBAlphaMinusTwoFirstMomentAxiom.lean`| HP-2023 Lemma 8.1  |
| `chi_alphaMinusTwo_lower_bound_whp`                | `CrossingPartB.lean`                     | HP-2023 Lemma 8.1  |
| `zeta_alphaMinusTwo_upper_bound_whp`               | `CrossingPartB.lean`                     | **extrapolation:** |
```

Row 2: 47-char axiom name + 41-char filename + a short third column. On a 1024px viewport GitHub renders this cleanly; on mobile or in a narrow split view the columns wrap mid-identifier, breaking the underscore-quoting visual cue.

Result type: **speculative concern**, P1.

---

## P2 findings (polish)

### P2-1. `proof/AXIOM_SNAPSHOT.txt` lists Lean kernel axioms in an order that differs from `README.md`'s prose

The snapshot output (lines 13-19) sorts the seven axioms alphabetically by full namespace path: `propext`, `Classical.choice`, then four `Problem625.*` axioms, then `Quot.sound`. `README.md:151` describes the kernel axioms as "`propext`, `Classical.choice`, `Quot.sound`" — listing them as if contiguous. They are not contiguous in the snapshot; `Quot.sound` is at index 6 because alphabetically `Problem625.*` precedes `Quot.sound`. A reader comparing snapshot vs README sees a "kernel axioms" group that the snapshot doesn't actually group. Pure presentation; same content.

Result type: **speculative concern**, P2.

---

### P2-2. `paper/main.tex:308` uses `(\mualpha)` cite key while the equation tag is `(eq:mualpha-2)` elsewhere

`paper/main.tex:302-304`: "Heckel~\cite{heckel2024} eq.~(\mualpha)" — but `\mualpha` is not defined anywhere in the document (`grep -n 'newcommand{\\\\mualpha' paper/main.tex` returns nothing). This is a LaTeX-side defect: the citation will compile but render the literal text `(\mualpha)` rather than an equation reference. (Verified: `\mualpha` is referenced once and never defined.)

Result type: **verified issue**, P2 because it is a LaTeX rendering polish item; the surrounding prose makes the citation interpretable.

---

### P2-3. `proof/red-team/README.md:54` says "the 14-artefact inventory" — but the table immediately above has 18 rows

Already accounted for in P0-2 above. Listed here as a P2 because the polish-level fix is "make the prose count match the table count" once P0-2's canonical definition is chosen.

Result type: **verified issue**, P2.

---

### P2-4. Forward reference in `README.md:246` to "this round's publish-readiness audit"

`README.md:246`: "11 Markdown notes (... + an axiom-check snapshot + **this round's publish-readiness audit**)". The phrasing "this round's" suggests the README was last edited mid-round-2, anticipating that the count would naturally include "this round's audit" — but the round-2 audit is already in `proof/red-team/`. Once round 3 (this audit) lands, the count needs updating again. The "this round's" idiom is rebound at each repair pass and is a count-update tripwire.

Result type: **bounded concern**, P2.

---

## Information redundancy / contradictions check (focus area d) — passing items

For completeness, the following round-3 cross-document checks **passed** (no contradiction found):

- **Theorem statement** (precise bound `χ - ζ ≥ n^{1-2ε}` for `ε ∈ (0, 0.001)`, probability `≥ 1 - 2ε`) appears in identical form in `README.md:4-6, 98-104`, `ROADMAP.md:46-50`, `DEVELOPMENT.md` (implicit via ADR-7/8), `proof/proof.md:16-18`, `paper/main.tex:63-65, 127-130`. No drift.
- **Axiom count "7 entries = 4 paper + 3 kernel"** appears in identical form in `README.md:73, 143, 153, 225`, `ROADMAP.md:14-19`, `DEVELOPMENT.md:20, 299, 315, 324, 328`, `proof/proof.md:122, 128, 140`, `paper/main.tex:137-148, 451, 466-563, 572, 651`, `paper/SOURCES.md:7`, `Erdos625/README.md:16, 29-42`. Uniform.
- **Coverage hierarchy 95% / 97% / 100% / 100%** appears uniformly across the four-theorem table in `README.md:124-129`, `ROADMAP.md:13-17`, `proof/proof.md:65-70`, `paper/SOURCES.md`, and is implied by `Erdos625/README.md:61`. No `~94%` or `~96%` drift in the coverage column. (Paper:115 uses "$\sim 94\text{–}96\%$" in the literature-comparison prose, which is a deliberate informal hedge about Heckel 2024's published density-1 claim, not a coverage statement about our theorems. No contradiction.)
- **`ε ∈ (0, 0.001)`** for all four publishable theorems is consistent (see P1-6 for the helper-lemma-range subtletly).
- **Bibliography**: HP-2023 = arXiv:2306.07253 (2023), Heckel 2024 = arXiv:2409.17614 (2024), HR-2023 = arXiv:2103.14014 (2021, v3 2023), erdosproblems.com/625. All consistent across `README.md:255-263`, `proof/proof.md:180-185`, `paper/main.tex:672-690`, `paper/SOURCES.md:24, 28, 51, 70, 90`. ✓
- **CI workflow exists**: `ROADMAP.md:167-169` claims `.github/workflows/build.yml` is committed. `test -f .github/workflows/build.yml` confirms.
- **Methodology directory exists**: `proof/methodology/README.md` (51 lines) and `proof/methodology/operator-profile.yaml` and `proof/methodology/operator-harnesses/*.txt` (3 files) all present.

---

## Mechanism audit

**Promise** (what the package sells to a first-time visitor):
1. Theorem is verifiable from README in 5 minutes.
2. Axiom inventory is one click from the front door, with an exact count and an explicit list.
3. Build is reproducible (toolchain pinned, `lake exe cache get` + `lake build`).
4. Scope limitations (prize disclaimer + in-prob vs a.s.) are prominently disclosed.
5. Audit trail is fully indexed and discoverable.
6. LLM-provenance is prominent and complete.

**Guarantee** (what the package actually delivers within 5 minutes):
1. ✓ Theorem statement at `README.md:4-6` and again at `:98-104`.
2. ✓ Axiom inventory at `README.md:136-176`, plus a verbatim snapshot at `proof/AXIOM_SNAPSHOT.txt`.
3. ✓ Build commands at `README.md:206-225`, toolchain pinned at `lean-toolchain` (`leanprover/lean4:v4.29.0-rc8`), CI workflow committed.
4. ✓ Prize and in-prob/a.s. distinction at `README.md:60-69` and again at `:107-118`, with measure-theoretic gap at `ROADMAP.md §N1`.
5. ⚠️ Red-team trail is discoverable via `proof/red-team/README.md` index, but the index itself contradicts itself on the number of artefacts (P0-2); paper readers cannot navigate to the index (P1-2).
6. ✓ LLM-provenance is on the first screen of `README.md` (50-line blockquote at lines 8-58).

**Where the stronger reading fails**:
- The "audit each axiom against the Lean source" promise breaks for 3 of 4 axioms because the file:line references are off by 1, 12, and 18 lines (P0-1).
- The "the package describes its own audit trail accurately" promise breaks because three numbers (14, 11, 18) appear for the same count (P0-2).
- The "reproducibility script can be run from a fresh checkout" promise breaks because `r2b_step1_scan.py`'s own docstring points at `problems/625/work/notes/...` (P0-3).
- The "post-ADR-9 the canonical Lean name is `kThresholdAlphaMinusOne`" promise is undercut by 14 verbatim `partBThresholdWitness` occurrences in audit files dated 2026-05-12, with no header disclaimer (P0-4).

**Minimal fix set** (for round 4; this round is critique only):

P0 fixes (a hostile reader will screenshot these):
1. Update Lean file:line refs in `paper/SOURCES.md`: A1 398→399, A3 251→263, A4 293→311. Consider linking by `axiom <name>` regex rather than line number to immunize against future drift.
2. Choose one canonical definition of "audit artefact count" (e.g. "13 markdown notes in `proof/red-team/` including the index + 3 legacy + 2 paper-side = 18 total artefacts", or some other partition), then sweep all four locations (`README.md:245-246`, `proof/red-team/README.md:3, 24, 54`) to match. Also remove the forward-reference "this round's publish-readiness audit" idiom.
3. Scrub `problems/625/work/...` and `/Users/thunderbird/...` paths from publish-side files. Two acceptable strategies: (a) rewrite the paths to publish-relative form (e.g. `proof/red-team/r2b-step1-results-2026-05-11.md`); (b) add a one-line header to each affected file: "Path references below are to the source repository; in the publish package the corresponding files are at `proof/red-team/*` and `proof/methodology/*` respectively."
4. Sweep `partBThresholdWitness` across the four audit files (`axiom-paper-correspondence-audit-2026-05-12.md`, `red-team-strict-lemma-by-lemma-2026-05-12.md`, `erdos-625-full-axiom-check-2026-05-11.md`, `paper/red-team-paper-2026-05-12.md`). Two strategies: replace with `kThresholdAlphaMinusOne`, or add a top-of-file note "(pre-rename Lean identifier; current canonical name is `kThresholdAlphaMinusOne`, see DEVELOPMENT.md ADR-9)".

P1 fixes:
5. Add a 1-line TOC under the title of `README.md`: "Jump to: [Theorem](#flagship-theorem) · [Axioms](#axiom-inventory) · [Build](#building-and-verifying) · [Red-team trail](#repository-layout) · [References](#references)". Or compress the provenance blockquote to a 5-line summary with "see Acknowledgments" pointer.
6. Add a paper-side link to the audit index: in `paper/main.tex` Acknowledgments add "See `proof/red-team/README.md` for the chronological audit-trail index."
7. Add a `proof/proof.md` pointer by name to the index: replace "see `red-team/` for the full audit trail" with "see `red-team/README.md` for the chronological index of audit artefacts."
8. Cross-link `proof/methodology/README.md` from `DEVELOPMENT.md` ADR-12 and `paper/main.tex` Acknowledgments.
9. Fix `ZetaConcentration.lean:33` stale header: replace `heckel_cochromatic_second_moment` with `heckel_offdiag_term_bound` and note the narrowing.
10. Add a one-line regime-disambiguation note to `proof.md` and `paper/main.tex` explaining `n^{0.99}` (crossing) vs `n^{0.999}` (good-case) slack constants.

P2 fixes:
11. Fix `\mualpha` undefined-macro in `paper/main.tex:303` (define it in the preamble or replace with `\eqref{eq:mualpha-2}`).
12. Tighten the README axiom-inventory table for mobile rendering (consider a 2-column variant with file + description merged).
13. Consider replacing ⭐ and ✅ emoji with bold-text equivalents in tables.
14. Add a sentence to `README.md` and `proof/proof.md` clarifying the kernel-axiom grouping in `AXIOM_SNAPSHOT.txt` (alphabetical sort places `Quot.sound` after `Problem625.*` entries).

---

## Compact ledger

- **Target document**: `publish/erdos-625/` package (8 main docs + `proof/red-team/` 14 audit artefacts incl. `legacy/` + `proof/methodology/` 5 files + Lean source).
- **Focus**: self-containment & navigation (first-time-visitor experience).
- **Main findings**: **4 × P0 / 9 × P1 / 4 × P2.**
  - **P0-1** Lean file:line drift in `paper/SOURCES.md` (A1 +1, A3 +12, A4 +18).
  - **P0-2** Contradictory artefact counts (14 vs 11 vs 18) across README and red-team/README.
  - **P0-3** Stale `problems/625/work/...` and absolute-home-dir paths in 9 publish-side files (incl. a reproducibility Python script's own docstring).
  - **P0-4** Pre-rename `partBThresholdWitness` identifier still present in 4 audit files dated 2026-05-12 (post-ADR-9).
  - **P1-1** to **P1-9**: README disclosure-wall, audit-index not linked from paper/proof.md, methodology not linked from paper Acknowledgments, `ZetaConcentration.lean:33` stale header, `n^{0.99}`/`n^{0.999}` regime split never disambiguated, `ε < 0.01` vs `< 0.001` ambiguity, LaTeX-in-tables mobile hazard, emoji wrap, narrow-table identifier wrap.
  - **P2-1** to **P2-4**: kernel-axiom ordering presentation, undefined `\mualpha` macro, "14-artefact inventory" vs 18-row table, forward-reference "this round's" idiom.
- **Mechanism verdict**: the "5-minute visitor verification" mechanism is **fragile but not broken**. All six landing-flow items are reachable; but P0-1 (line drift), P0-2 (count contradictions), P0-3 (broken reproducibility paths), and P0-4 (stale identifier) each give a hostile reader a screenshot-quotable inconsistency. None invalidates the mathematical content; all of them invalidate the package's self-presentation as "internally consistent and self-contained".

### Ordered fix list for round 4

1. (P0-1) Update Lean file:line refs in `paper/SOURCES.md`. Consider switching to `axiom <name>` regex references.
2. (P0-2) Pick one canonical count of audit artefacts and sweep `README.md:245-246`, `proof/red-team/README.md:3, 24-25, 54`. Remove the forward-reference "this round's publish-readiness audit" idiom.
3. (P0-3) Rewrite or annotate `problems/625/work/...` and `/Users/thunderbird/...` paths in: `r2b-step1-plan-2026-05-11.md`, `r2b_step1_scan.py`, `lemma-7-10-ext-disclosure-2026-05-11.md`, `lemma_7_10_ext.md`, `red-team-erdos-625-full-2026-05-11.md`, `r2b-step1-results-2026-05-11.md`, `red-team-proof-md-2026-05-12.md`, `proof/methodology/operator-profile.yaml`, `proof/methodology/operator-harnesses/erdos-metadata-harness.txt`, `Erdos625/PublishableProof.lean:308` (the docstring comment).
4. (P0-4) Sweep `partBThresholdWitness` across `axiom-paper-correspondence-audit-2026-05-12.md`, `red-team-strict-lemma-by-lemma-2026-05-12.md`, `erdos-625-full-axiom-check-2026-05-11.md`, `paper/red-team-paper-2026-05-12.md`. Replace with `kThresholdAlphaMinusOne` or add a top-of-file rename note.
5. (P1-1) Add a TOC or compress provenance blockquote on README.
6. (P1-2) Link `proof/red-team/README.md` from `paper/main.tex` Acknowledgments and from `proof/proof.md:187`.
7. (P1-3) Link `proof/methodology/README.md` from `paper/main.tex` Acknowledgments and `DEVELOPMENT.md` ADR-12.
8. (P1-4) Fix `ZetaConcentration.lean:33` stale axiom name.
9. (P1-5) Add a regime-disambiguation note for `n^{0.99}` vs `n^{0.999}`.
10. (P1-6) Clarify ε-range scoping in `paper/main.tex` Layer 4.
11. (P1-7, P1-9) Sanity-check table rendering on mobile (or accept the risk).
12. (P1-8) Consider replacing ⭐/✅ with text equivalents.
13. (P2-1, P2-3, P2-4) Polish kernel-axiom presentation, "14-artefact" prose vs table, and forward-reference idiom.
14. (P2-2) Fix `\mualpha` undefined macro in `paper/main.tex:303`.

---

## Provenance

- **Generated**: 2026-05-12 (round-3 publish-readiness pass).
- **Worker model**: `claude-opus-4-7[1m]` (Claude Opus 4.7, 1M-context variant).
- **Operator orchestrator**: `operator` (https://github.com/uthunderbird/vibechord); codex-brain adapter ran `gpt-5.3-codex-spark` at `effort=low`.
- **Conducted by**: `/swarm-red-team` (internal adversarial-audit pipeline; not a third-party review).
- **Same-model caveat**: this artefact was produced by the same LLM-agent pipeline that produced the proof being critiqued. LLM-generated proofs may exhibit plausibility-driven failure modes that survive same-model critique because the proof author and the critic share training-data blind spots. See `../../README.md` Provenance and `../../DEVELOPMENT.md` ADR-10 / ADR-11 / ADR-12 for the full methodology disclosure. External verification by an unrelated reader, a different model, or a human mathematician is encouraged.
- **Method**: filesystem walk + `grep` of all internal links + physical line-count against the live Lean files. No web fetch. No build re-run.
- **Inputs read**: `README.md`, `ROADMAP.md`, `DEVELOPMENT.md`, `proof/proof.md`, `paper/main.tex`, `paper/SOURCES.md`, `Erdos625/README.md`, `Erdos625/extras/README.md`, `proof/AXIOM_SNAPSHOT.txt`, `proof/red-team/README.md`, `proof/red-team/legacy/README.md`, `proof/methodology/README.md`, all 14 audit artefacts in `proof/red-team/`, all 3 in `proof/red-team/legacy/`, both paper-side red-team files in `paper/`, `Erdos625/PublishableProof.lean`, `Erdos625/CrossingPartB.lean`, `Erdos625/PartBAlphaMinusTwoFirstMomentAxiom.lean`, `Erdos625/ZetaConcentration.lean` header, `lean-toolchain`, `proof/methodology/operator-profile.yaml`, `proof/methodology/operator-harnesses/erdos-metadata-harness.txt`.
