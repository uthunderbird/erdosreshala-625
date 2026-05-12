# Publish-Readiness Red Team — Round 1: Honesty Surface

- **Date**: 2026-05-12
- **Target**: the entire `publish/erdos-625/` package (treated as one composite document).
- **Walk order**: `README.md` → `ROADMAP.md` → `DEVELOPMENT.md` → `proof/proof.md` → `paper/main.tex` → `paper/SOURCES.md` → `Erdos625/README.md` → `Erdos625/extras/README.md`.
- **Round**: 1 of 5.
- **Focus**: honesty surface only (overclaiming, hidden caveats, status/build accuracy, prize-claim framing, "solved" framing, LLM-agent attribution).
- **Conducted by**: `/swarm-red-team` (internal adversarial-audit pipeline; not an external review).
- **Repair-out-of-scope**: this round is critique-only; no edits made to the target.

## Method

Five-expert critique (Annika Heckel / Kevin Buzzard / Timothy Gowers / Lance Fortnow / Cynthia Rudin), three Phase 3 iterations, mandatory mechanism audit on the implicit guarantee *"honest, publication-ready submission of an LLM-generated proof"*. Evidence boundary: local files; `grep`/`cat` of the eight target documents plus the four source Lean files they describe. **Build status and `#print axioms` output were *not* re-run in this session** (no `lake build` executed); findings about those claims are flagged as such.

## Severity legend

- **P0**: must fix before publishing — overclaiming, mis-stated axiom inventory, false or unverifiable build/sorry status, missing prize/LLM disclosures that would be screenshot-quoted hostilely.
- **P1**: must fix before publishing — buried disclosures, terminology inconsistencies, framing ambiguities a careful reader will catch.
- **P2**: polish.

---

## P0 findings (6)

### P0-1. No explicit "this does not claim the Erdős prize" statement anywhere in the package

The prize is mentioned **once**, at `paper/main.tex:89-90`:

> "Erd\H{o}s offered \$100 for an affirmative answer and \$1000 for a counterexample."

No document — README, ROADMAP, proof/proof.md, paper abstract, Erdos625/README.md — contains a sentence stating that this submission does **not** claim that prize, or that the prize is for almost-sure convergence while the formalized result is in-probability. The Erdős–Gimbel question is literally for almost-sure convergence (paper:84-85 and 137-138 acknowledge this). With the LLM-agent provenance combined with prize visibility, the natural hostile headline is *"LLM agent solves \$100 Erdős problem"*.

**Evidence — exact quotes that screenshot-attack to the prize claim:**
- `README.md:31-32`: "**positively answering the in-probability form of the Erdős–Gimbel question** ([erdosproblems.com/625](https://www.erdosproblems.com/625))."
- `proof/proof.md:11-13`: "This repository establishes the following Lean-machine-checked theorem, which **positively answers** the question with a quantitative bound holding for **all** sufficiently large n."
- `paper/main.tex:56-58`: "In particular $\chrom(\Gnh) - \cochrom(\Gnh)\to\infty$ in probability, positively answering the in-probability form of the Erd\H{o}s--Gimbel question (Erd\H{o}s problem~625) which asks for almost-sure divergence."

The paper line 58 does acknowledge the gap ("asks for almost-sure"), but the README and proof.md headline sentences do not, and prize-eligibility is left to inference.

### P0-2. LLM-agent provenance not disclosed anywhere

`grep -in "LLM\|Claude\|operator\|generated\|AI\|machine generation\|agent" README.md ROADMAP.md DEVELOPMENT.md proof/proof.md paper/main.tex paper/SOURCES.md Erdos625/README.md Erdos625/extras/README.md` returns **zero hits**. The proof was produced by an LLM-agent pipeline (Claude + operator); no target document discloses this. The closest is `paper/main.tex:556-557`:

> "The development was adversarially audited via \texttt{/swarm-red-team} (sessions 2026-05-11 on the Lean theorem, 2026-05-12 on \texttt{proof.md} and on the present paper)"

This discloses *audit-by-LLM* but not *proof-generation-by-LLM*; a reader interprets it as a tool-assisted review of a human-authored proof. The acknowledgments at `paper/main.tex:548-552` thank Heckel and Panagiotou for foundational papers and the Lean community — a normal authorship gesture that **further** implies human authorship by omission. Combined with `paper/main.tex:41-43` ("Author list redacted for review"), the package presents as a conventional human submission. The user's brief raised this to P1; in the prize context P0 is justified.

### P0-3. "No `sorryAx`" claim repeated in five documents without the precise caveat

`grep -rn "^\s*sorry\b\|^  sorry$\|^    sorry$" Erdos625/*.lean` returns **7 literal `sorry` tokens** in the published Lean tree:

- `Erdos625/ChromaticConnection.lean:3753` (inside `private lemma decay_exponent_eventually_le_neg`; the file comment at line 3950 asserts it is no longer on the dependency path)
- `Erdos625/ZetaConcentration.lean:1986` (the file's own header at line 33 calls it "1 sorry (architectural only, not load-bearing)")
- `Erdos625/PartBProfileBridge.lean:13790, 13832, 13844, 13860, 13904` (five `private` helper lemmas in the legacy chain)

The narrow claim "0 `sorry` on the `erdos_625_full_clean` proof path" is defensible *if* `#print axioms` is clean (we did not re-verify in this session). The package-wide claim "No `sorryAx`" is internally true (`grep -n sorryAx` finds nothing). But the bare summary lines below are screenshot-quotable as false, because a hostile reviewer running `grep -rn sorry Erdos625/` lands on those 7 hits in five seconds:

- `README.md:8-10`: "**4 paper-backed axioms (2 literal HP-2023 citations, 2 hybrid with explicit disclosures), 0 `sorry` on the `erdos_625_full_clean` proof path.**" — defensible *only* with the proof-path qualifier, which the next line drops.
- `README.md:71`: "No `sorryAx`."
- `ROADMAP.md:19`: "`lake build` GREEN (2925 jobs). No `sorryAx`."
- `proof/proof.md:99`: "returns **7 entries**, 0 `sorryAx`:"
- `Erdos625/README.md:22`: bare "No `sorryAx`."

The **only** disclosure of unreachable sorrys lives in `paper/main.tex:424-426`:

> "Sorries elsewhere in the repository (in supporting modules not on the proof path) are warned by Lean during build but do not affect this dependency closure."

That single sentence is the entire disclosure of 7 literal `sorry` markers, in one of the eight documents.

### P0-4. "$\chi-\zeta \to \infty$ in probability" headlined as if it were the Lean theorem

The Lean theorem `erdos_625_full_clean` proves, for *fixed* $\varepsilon \in (0,0.001)$, $\Pr[\chi-\zeta \ge n^{1-2\varepsilon}] \ge 1-2\varepsilon$ for all large $n$. The in-probability limit ("$\chi-\zeta \to \infty$ in probability") is the **$\varepsilon \to 0$** corollary. `paper/main.tex:532-536` openly admits:

> "Also, Corollary 1 stated in §1 (in-probability divergence) is the $\varepsilon\to 0$ limit of Theorem 1, which itself is a straightforward exercise but is not in the Lean chain either; only the per-$\varepsilon$ quantitative form is machine-checked."

But the package headlines the unformalized corollary:

- `README.md:30-31`: "In particular $\chi(G) - \zeta(G) \to \infty$ **in probability**, positively answering the in-probability form of the Erdős–Gimbel question" — **bolded**.
- `proof/proof.md:20`: "**χ(G) − ζ(G) → ∞ in probability**." — **bolded**.
- `paper/main.tex:56-57`: "In particular $\chrom(\Gnh) - \cochrom(\Gnh)\to\infty$ in probability".
- `paper/main.tex:131-133`, Corollary `cor:in_prob`: "$\chrom(\Gnh)-\cochrom(\Gnh)\to\infty$ in probability as $n\to\infty$." — stated as a corollary without the "not in Lean" qualifier appearing in the same theorem-block.

A reader screenshot-quoting the bolded headline cites a statement that is **not** machine-checked; the Lean theorem checks a strictly different, ε-quantified statement.

### P0-5. "Routine follow-up" rhetorical compression of the Borel–Cantelli step

The "almost-sure" gap is described as "a routine follow-up not yet in the Lean chain" (`README.md:33-35`), "a routine measure-theoretic argument not yet in the Lean chain" (`paper/main.tex:139-141`), and "a routine follow-up not yet in Lean" (`proof/proof.md:21-23`).

The promotion from per-ε in-probability bounds to almost-sure convergence with $\varepsilon_n = 1/\log n$ is **not** trivial: $\sum 2/\log n$ diverges, so a direct application of Borel–Cantelli-1 to the events $\{\chi-\zeta < n^{1-2\varepsilon_n}\}$ does not work. The actual argument needs either (i) BC-2 plus an independence/coupling argument the events across different $n$ do not satisfy off-the-shelf, or (ii) a subsequence + monotonicity argument. Either way, "routine" is rhetorical compression. The package neither (a) sketches the argument nor (b) cites a textbook lemma; it relies on the adjective.

This is an honesty-surface P0 because it primes the reader to mentally promote the in-probability result to almost-sure ("one week away") when the step may be subtler.

### P0-6. `axiom heckel_cochromatic_second_moment` declaration vs. SOURCES.md "now a proved theorem" contradiction

`Erdos625/PublishableProof.lean:321` still contains the declaration:

```
axiom heckel_cochromatic_second_moment :
```

But `paper/SOURCES.md:99-102` describes the same axiom:

> "`Problem625.heckel_offdiag_term_bound` — Heckel 2024 Prop 5(b) off-diagonal term (a 2026-05-11 narrowing of the original `heckel_cochromatic_second_moment`, which is now a proved theorem on top of `heckel_offdiag_term_bound`)."

A hostile reader running `grep '^axiom' Erdos625/PublishableProof.lean` sees an axiom; the docs say "now a proved theorem". This is either (i) a stale `axiom` declaration that should be deleted, or (ii) a documentation overclaim. Either way, a screenshot-quotable inconsistency.

(Note: technically not in the reachable axiom set of `erdos_625_full_clean` per the verbatim `#print axioms` output at `paper/main.tex:417-423`, so the inconsistency is documentary, not load-bearing on the flagship. But it is on the honesty surface.)

---

## P1 findings (7)

### P1-1. Hybrid- and extrapolation-axiom disclosures unevenly distributed across documents

The two strongest disclosures (axiom A1 `lemma_7_20_modified` is *hybrid* with our non-peer-reviewed numerical certificate; axiom A4 `zeta_alphaMinusTwo_upper_bound_whp` is an *α−2 extrapolation* not literally in print) appear at full strength only in `paper/SOURCES.md` (§A1, §A4) and `paper/main.tex §7`. README/`ROADMAP`/`proof.md` mention them but in compressed forms ("hybrid", "extrapolation") that are easy to overlook. `Erdos625/README.md` mentions them only by pointer ("see `paper/SOURCES.md`"). A reader who reads only README + Erdos625/README.md (the two most likely GitHub first-touch documents) gets a softer picture than the SOURCES + paper combined.

Evidence:
- `README.md:54-73` table presents axiom #1 inline as "**hybrid:** HP-2023 Lemma 7.20 (modified) + our numerical certificate `lemma_7_10_ext`" and axiom #4 as "**extrapolation:** Heckel 2024 Prop 5(b) + Azuma, adapted α−1 → α−2". This is honest but compact; the 1086-cell grid, 1.2-orders-of-magnitude margin, and "not literally in print" framing arrive only in the paper §7.
- `Erdos625/README.md:14-22` simply says "with two literal HP-2023 citations and two hybrid axioms" and points elsewhere; no headline of *which* claims are not peer-reviewed.

### P1-2. "Hybrid" vs "extrapolation" terminology inconsistency for axiom A4 / Axiom 3 in paper

- `README.md:68` and `proof/proof.md:106` call axiom #4 **"extrapolation"**.
- `paper/SOURCES.md:72,85` labels it **"EXTRAPOLATION"** (uppercase) with "**adapted from $(\alpha-1)$-bounded to $(\alpha-2)$-bounded cocolorings**".
- `paper/main.tex:464-478` (paragraph "Axiom~3") uses the softer **"(*Hybrid:* literal HP-2023 second-moment machinery + symmetric $(\alpha-2)$-version of Heckel 2024 Proposition 5(b))"** and explains "We use the language ''hybrid'' for this axiom because while the underlying HP-2023 second-moment lemmas (Lemmas 6.3-6.5) are explicitly stated for general $a$-bounded profiles, the application step at $a=\alpha-2$ is not a verbatim quote of any published lemma."

"Hybrid" sounds incrementally less strong than "extrapolation" — the paper picks the softer word for the document that will face the most external scrutiny. Pick one term, use it everywhere.

(Bonus inconsistency: `paper/main.tex §7` numbers axioms 1–4 in the order Axiom 1 = `partB_alphaMinusTwo_firstMomentBelowOne_source`, Axiom 2 = `chi_alphaMinusTwo_lower_bound_whp`, Axiom 3 = `zeta_alphaMinusTwo_upper_bound_whp`, Axiom 4 = `lemma_7_20_modified`. README/SOURCES/proof.md all use the order 1 = `lemma_7_20_modified`, 4 = `zeta...`. The paper's "Axiom 4" is the README's "Axiom 1", and the paper's "Axiom 3" is the README's "Axiom 4". A careful reader will be confused; a hostile one will note the renumbering.)

### P1-3. "Five independent red-team passes" presented as a quality signal without disclosing they are self-administered

- `README.md:11`: "Five independent red-team passes (see `proof/red-team/`); all concluded *no P0 found*."
- `ROADMAP.md:19-22`: "Five independent red-team passes ... all 0 P0."
- `paper/main.tex:556-558`: "no critical (P0) issues were found that affect the proof correctness."

All five passes are runs of `/swarm-red-team` on the same agent-operator pipeline that produced the proof. "Independent" is doing a lot of work here. Reframe as "five internal adversarial audits (same LLM-agent pipeline)" or drop the implicit objectivity claim.

### P1-4. "[Author list redacted for review]" reads as evasion for a GitHub publication

`paper/main.tex:41-43`:

> "[Author list redacted for review; final version will name authors and affiliations]"

For a paper accompanying a public GitHub release with no stated venue under review, redacted authorship reads as evasion of provenance accountability. Combined with P0-2 (LLM provenance hidden), it compounds the trust gap. Either name the operator (and disclose LLM tooling) or state the venue and review status.

### P1-5. "We give the *first* Lean 4 machine-checked proof" — no documented prior-art check

`paper/main.tex:50`:

> "We give the first Lean~4 machine-checked proof of a quantitative chromatic--cochromatic gap in the Erd\H{o}s--R\'enyi random graph $\Gnh$ that is valid for *all* sufficiently large $n$."

"First" claims in adversarial settings are attacked unless a prior-art search is documented. The package contains no such documentation. Either drop "first" (e.g., "a Lean 4 machine-checked proof") or document the search.

### P1-6. Red-team artefact count: 5 vs 11 vs actually 13

- `README.md:11`: "Five independent red-team passes (see `proof/red-team/`)".
- `README.md:142`: "`proof/red-team/` | **Eleven** adversarial audit artefacts (red-team passes, axiom-paper correspondence, numerical certificate, transfer audits)."
- Actual `ls proof/red-team/`: 13 entries (including 2 Python scripts, 1 legacy subdir).

Pick a counting convention and use it consistently. As stands, a reader notices three different numbers in 130 lines of README.

### P1-7. Acknowledgments thank human authors of foundational papers, never disclose AI provenance

`paper/main.tex:550-552`:

> "The authors thank Annika Heckel and Konstantinos Panagiotou for the foundational papers \cite{heckel2024,heckelpanagiotou2023} that this formalization builds on, and the Lean community for the Mathlib library."

This is a normal human-authorship acknowledgments paragraph. With no LLM disclosure (P0-2), it reinforces the human-authored framing.

---

## P2 findings (4)

### P2-1. `Erdos625/extras/README.md` is a placeholder describing a file that does not exist

The entire content (lines 1-10) is "Currently empty. A candidate for future inclusion is `SharpProfileBound.lean`...". For a published artefact, an empty placeholder README is noise; either fill it or remove the directory.

### P2-2. `lake build` GREEN claim and `#print axioms` output are not pinned to a reproducible artefact

`ROADMAP.md:19`: "`lake build` GREEN (2925 jobs). No `sorryAx`." A fresh clone with a mismatched Mathlib pin or a different `elan` version could fail this. Recommend a CI badge, a `.github/workflows/build.yml` with a published green run, or a checksum of the `#print axioms` output committed under `proof/`.

### P2-3. DEVELOPMENT.md has duplicate ADR numbering

`DEVELOPMENT.md:9` introduces "ADR-1"; line 139 introduces a **second** "ADR-3"; line 176 introduces a **second** "ADR-4"; lines 13 and 137 are the original ADR-3 and ADR-4. ADR identifiers should be unique; the duplicates make the doc hard to cite.

### P2-4. Bound-strength framing in §scope: structural-bound $n^{1-\varepsilon}-2n^{0.99}$ vs clean $n^{1-2\varepsilon}$

The package consistently and correctly distinguishes `erdos_625_full` (structural bound) from `erdos_625_full_clean` (clean rate). No overclaim found here in the inline bound headline; this is noted as a *non-issue* relative to the brief's category (a) bound-strength worry.

---

## Mechanism Audit Summary

**Mechanism claim:** "The publish/erdos-625/ package is an honest, publication-ready submission of an LLM-generated proof."

| Promise made by package | Mechanism (8 documents as written) actually delivers? |
|---|---|
| Honest disclosure of 4 paper axioms | Yes, but unevenly distributed (P1-1, P1-2). |
| 0 sorry on proof path | Defensible only with the proof-path qualifier; bare "No sorryAx" is misleading (P0-3). |
| Machine-checked in-probability divergence | The *bolded* headline corollary is **not** in Lean (P0-4). |
| Quantitative Erdős–Gimbel answer | Yes, modulo P0-5 ("routine" BC step) and the headline gap (P0-4). |
| Internal consistency of axiom inventory | A1 vs A4 numbering and "hybrid/extrapolation" terminology shift between paper and README/SOURCES (P1-2). |
| Honest about LLM provenance | **No.** Zero disclosure (P0-2). |
| Honest about prize claim | **No.** No "we do not claim the prize" statement; prize mentioned, eligibility implicit (P0-1). |
| Verifiable build / axiom output | Claims stated but not pinned to a reproducible CI artefact (P2-2). |

Minimal P0 fix set is items 1–6 of the ledger below.

---

## Compact Ledger

- **Target document**: `publish/erdos-625/` package (8 documents, treated as one composite).
- **Focus**: honesty surface (rounds (a)–(f) of the brief).
- **Round**: 1 of 5 (honesty-only; later rounds out of scope for this artefact).
- **Findings**: **P0 × 6, P1 × 7, P2 × 4** (17 total).
- **Headline list (P0)**:
  1. No explicit "this does not claim the Erdős prize" statement.
  2. LLM-agent provenance not disclosed anywhere.
  3. "No `sorryAx`" repeated without the precise caveat; 7 literal `sorry` tokens exist in the tree.
  4. "$\chi-\zeta \to \infty$ in probability" headlined as the Lean theorem, but it is the unformalized $\varepsilon\to 0$ corollary.
  5. "Routine follow-up" rhetorical compression of the non-trivial Borel–Cantelli step.
  6. `axiom heckel_cochromatic_second_moment` still declared in `PublishableProof.lean:321` while SOURCES.md says "now a proved theorem".

### Ordered Fix List (for the repair round)

P0 fixes, in order:

1. **Prize disclaimer**. Add an explicit paragraph (suggested: "*This work does not claim the Erdős prize for Problem 625. The \$100 prize is for almost-sure convergence; the flagship Lean theorem establishes only the in-probability form. Promoting to almost-sure requires a Borel–Cantelli step (subsequence/diagonal argument) not yet formalized in Lean.*") visible in: `README.md` (immediately under the "Flagship theorem" section, before line 38), `ROADMAP.md` (top of "Honest scope limitations"), `proof/proof.md` (between lines 18 and 26), `paper/main.tex` (abstract or right after Theorem 1, before line 113).

2. **LLM-agent provenance**. Add a visible-level disclosure that the proof was generated by an LLM-agent pipeline (Claude + operator). Locations: `README.md` top (before "Flagship theorem"), `Erdos625/README.md` top, `paper/main.tex` Acknowledgments (lines 550-558), and `DEVELOPMENT.md` (a new ADR or a top-of-file note). The disclosure must say *proof generation*, not only *adversarial audit*.

3. **Sorry-status precision**. Replace every standalone "No `sorryAx`" with: "`#print axioms Problem625.Publishable.erdos_625_full_clean` returns seven entries and no `sorryAx`. Five `sorry` tokens remain in `private` helper lemmas in the legacy chain (`PartBProfileBridge.lean`) and two in supporting modules (`ChromaticConnection.lean`, `ZetaConcentration.lean`); none is reachable from the flagship theorem." Apply at: `README.md:8-11`, `README.md:71`, `ROADMAP.md:19`, `proof/proof.md:99`, `Erdos625/README.md:22`.

4. **Headline "in-probability"**. Reword every bolded "$\chi-\zeta \to \infty$ in probability" headline to make explicit that the **Lean theorem** is the per-ε quantitative form and the in-probability *limit* is the (un-formalized) $\varepsilon\to 0$ corollary. Locations: `README.md:27-31`, `proof/proof.md:18-20`, `paper/main.tex:56-57` (and Corollary 1 statement at line 131-133 should carry a "(not in Lean)" parenthetical).

5. **Borel–Cantelli framing**. Replace "routine follow-up" / "routine measure-theoretic argument" with either (i) a 3–5 line outline of the actual subsequence + BC argument, or (ii) a precise citation, or (iii) drop the adjective ("a follow-up not yet in Lean"). Locations: `README.md:33-35`, `proof/proof.md:21-23`, `paper/main.tex:139-141`.

6. **`heckel_cochromatic_second_moment` reconciliation**. Either delete `axiom heckel_cochromatic_second_moment` at `Erdos625/PublishableProof.lean:321` (if it really is now a proved theorem), or correct `paper/SOURCES.md:99-102` to say the original axiom remains and `heckel_offdiag_term_bound` is the narrower form alongside it. Build must remain green.

P1 fixes, in order:

7. Add an "Honest scope" / "Caveats" callout box at the top of `README.md` and `Erdos625/README.md` naming axioms A1 (hybrid, numerical certificate) and A4/A3 (α−2 extrapolation) explicitly with the strongest framing used elsewhere (P1-1).
8. Pick one term ("hybrid" or "extrapolation") and use it consistently for `zeta_alphaMinusTwo_upper_bound_whp` across `paper/main.tex §7`, `README.md`, `SOURCES.md`, `proof/proof.md`. Also: unify the axiom numbering (paper §7 1–4 vs. README/SOURCES 1–4) — same indexing in all documents (P1-2).
9. Reframe "five independent red-team passes" → "five internal adversarial audits (same LLM-agent pipeline)" or equivalent. Locations: `README.md:11`, `ROADMAP.md:19-22`, `paper/main.tex:556-558` (P1-3).
10. Either replace `[Author list redacted for review]` with concrete authorship (operator-of-record + LLM-tooling disclosure) or state the venue under review. `paper/main.tex:41-43` (P1-4).
11. Drop "first Lean 4 machine-checked proof" → "a Lean 4 machine-checked proof", or document the prior-art search in a footnote. `paper/main.tex:50` (P1-5).
12. Reconcile counts (5 passes / 11 artefacts / 13 actual files) into one consistent convention. `README.md:11, 142` (P1-6).
13. Add LLM provenance acknowledgment to `paper/main.tex` Acknowledgments and optionally a top-level `NOTICE` file. (P1-7, R-γ.)

P2 fixes, in order:

14. Fill or delete `Erdos625/extras/README.md` (P2-1).
15. Add CI badge + committed `#print axioms` output snapshot so build/axiom claims are independently verifiable from the snapshot. (P2-2.)
16. Renumber the duplicate ADRs in `DEVELOPMENT.md` (P2-3).

---

## Status note for downstream rounds

This artefact is round 1 of 5; later rounds were explicitly out of scope per the brief. The repair round following round 1 should retire P0-1 through P0-6 before any further critique round opens. Round 2 ("technical-claim surface") should re-open only after the P0 ledger above is closed, since several P0 items intersect technical claims (P0-3 axiom count, P0-4 Lean-theorem-vs-corollary, P0-6 axiom declaration).

---

## Provenance

- **Generated**: 2026-05-11 / 2026-05-12 development window.
- **Worker model**: `claude-opus-4-7[1m]` (Claude Opus 4.7, 1M-context variant).
- **Operator orchestrator**: `operator` (https://github.com/uthunderbird/vibechord); codex-brain adapter ran `gpt-5.3-codex-spark` at `effort=low`.
- **Same-model caveat**: this artefact was produced by the same LLM-agent pipeline that produced the proof being critiqued; it is an **internal adversarial audit**, not a third-party review. LLM-generated proofs may exhibit plausibility-driven failure modes that survive same-model critique because the proof author and the critic share training-data blind spots. See `../../README.md` Provenance and `../../DEVELOPMENT.md` ADR-10 / ADR-11 / ADR-12 for the full methodology disclosure. External verification by an unrelated reader, a different model, or a human mathematician is encouraged.
- **Footer added**: round-2 publish-readiness repair, 2026-05-12 (P1-7).
