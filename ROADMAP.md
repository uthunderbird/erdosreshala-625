# Publication Roadmap

This document tracks what remains before the formalization of Erdős Problem 625
is a complete mathematical publication. Produced from a publishing-excellence review
on 2026-05-10.

---

## Tier 1 — Required before any public claim

These items must be addressed before the repository is announced or the prize claim is made.

### T1-A: Fix InMainRange prose claim in README

**Status**: Open

The README currently says:
> "For the Erdős–Rényi model, E[α(G(n,1/2))] ≈ 2 log₂ n, so this condition holds
> for all sufficiently large n when ε < 0.001."

This is a mathematical claim that is **not proved in Lean**. The theorem `erdos_625`
takes `InMainRange ε n` as a hypothesis — it does not establish when InMainRange holds.

**Fix**: Add a parenthetical making clear that this is a known asymptotic fact not
formalized in this repo, e.g. "(this is standard by the asymptotics of α(G(n,1/2)),
but is not formalized here)".

### T1-B: arXiv companion paper

**Status**: Open

A GitHub repository is not a mathematical publication. For the result to be recognized
by the mathematical community (and for any prize claim), a human-readable arXiv preprint
is required.

**The paper should include**:
- Precise statement of the theorem (including InMainRange and ε < 0.001 restriction)
- Mathematical content of each of the 3 axioms (not just their Lean names)
- Comparison to the original Erdős problem statement — what exactly was proved and what was assumed
- A "limitations" section: what is not formalized, what axioms could in principle be discharged, generalization to G(n,p)
- Precise citations with arXiv version numbers for HP-2023 and Heckel 2024
- Link to the GitHub repo and DOI (once deposited on Zenodo)

### T1-C: Show the actual Lean type of `erdos_625` verbatim in README

**Status**: Open

Currently the README describes the theorem in prose and math. Add a code block showing
the exact Lean statement so there is no ambiguity about what was proved:

```lean
theorem erdos_625 (ε : ℝ) (hε_pos : 0 < ε) (hε_small : ε < 0.001) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → InMainRange ε n →
      1 - ENNReal.ofReal (2 * ε) ≤
        gnHalf n {G : SimpleGraph (Fin n) |
          (n : ℝ) ^ (1 - ε) ≤ (chromaticNumber G : ℝ) - (cochromaticNumber G : ℝ)}
```

This is standard practice for published Lean formalizations.

---

## Tier 2 — Establishes excellence

These items significantly raise the quality of the publication and signal seriousness
to both communities (formal verification and mathematics).

### T2-A: Add a "Problem background" section to README

**Status**: Open

Add 3–4 sentences above the Theorem section explaining:
- Who offered the prize (Paul Erdős, $1000)
- What the problem asks (chromatic vs. cochromatic gap in random graphs)
- Why it is interesting (connection to graph coloring thresholds, probabilistic combinatorics)

External readers — especially non-specialists — need this context to understand the significance.

### T2-B: Add a `#check` snippet to README

**Status**: Open

Add a one-liner that a Lean user can paste after importing the library to verify
the statement type without a full build:

```lean
-- After `import Erdos625.PublishableProof`:
#check @Problem625.Publishable.erdos_625
```

### T2-C: Zenodo / DOI deposit

**Status**: Open (post-arXiv)

Archive the exact source on [Zenodo](https://zenodo.org) (free, integrates with GitHub
releases). This creates a permanent DOI that can be cited in the companion paper and
by others. GitHub URLs are not stable citation targets.

Do after the arXiv preprint is posted.

### T2-D: Eliminate `lake build` sorry warnings

**Status**: Open

Two architectural sorrys produce `warning: ... uses sorry` on `lake build`, requiring
explanation to first-time users. Consider:
- Deleting the off-path sorry'd theorems entirely, or
- Moving them to `Erdos625/extras/` with a note

A completely clean `lake build` (0 warnings) is a strong quality signal.

### T2-E: Lean Zulip announcement (before broader announcement)

**Status**: Open (timing)

Post on Lean Zulip (#general or #mathlib4) with:
- What was proved and what was axiomatized
- Link to the repo
- Invitation for community review

Do this *before* the broader announcement to catch issues early and build goodwill.

### T2-F: Notify co-authors of axiomatized results

**Status**: Open (timing)

Email Annika Heckel and Konstantinos Panagiotou (HP-2023) and Annika Heckel (Heckel 2024)
describing how their results are used as axioms. Include a link to `paper/SOURCES.md`.

Standard academic courtesy; avoids surprises when the paper is announced.

---

## Tier 3 — Nice to have

These items add narrative and long-term value but are not required for "excellence."

### T3-A: CHANGELOG / formalization timeline

A brief timeline: when the project started, key milestones, date of completion.
Builds narrative and trust; signals sustained effort.

### T3-B: Pin arXiv versions in SOURCES.md

Change `arXiv:2306.07253` → `arXiv:2306.07253v?` (with the specific version number
whose equations exactly match the axioms). Same for `arXiv:2409.17614`.

### T3-C: Note on Mathlib upstreaming candidates

Add a note (e.g., in `DEVELOPMENT.md` or `Erdos625/README.md`) about which infrastructure
— Azuma–Hoeffding concentration, the `gnHalf` probability space, `chromaticNumber`,
`cochromaticNumber` — is a candidate for future Mathlib contribution.

### T3-D: "Limitations" section in README

What was not formalized, what it would take to discharge the 3 axioms, generalization
to G(n,p) for p ≠ 1/2. Sets honest expectations and invites follow-up work.

---

## Summary table

| Item | Tier | Status |
|------|------|--------|
| T1-A: Fix InMainRange prose claim | 1 | Open |
| T1-B: arXiv companion paper | 1 | Open |
| T1-C: Lean type verbatim in README | 1 | Open |
| T2-A: Problem background section | 2 | Open |
| T2-B: `#check` snippet | 2 | Open |
| T2-C: Zenodo / DOI deposit | 2 | Open (post-arXiv) |
| T2-D: Eliminate `lake build` warnings | 2 | Open |
| T2-E: Lean Zulip announcement | 2 | Open (timing) |
| T2-F: Co-author notification | 2 | Open (timing) |
| T3-A: CHANGELOG / timeline | 3 | Open |
| T3-B: arXiv version pinning in SOURCES.md | 3 | Open |
| T3-C: Mathlib upstreaming note | 3 | Open |
| T3-D: Limitations section | 3 | Open |
| Axiom count and CI verification | — | ✅ Done |
| Document accuracy (3 red-team passes) | — | ✅ Done |
| No internal artifacts in git | — | ✅ Done |
| License (Apache 2.0) | — | ✅ Done |
