# Erdős Problem 625 — analytical proof package

This repository packages a complete analytical proof route for
Erdős Problem 625.  The main analytical claim is:

```text
There exists a deterministic function w(n)->infinity such that
P_{G~G(n,1/2)}[chi(G)-zeta(G) >= w(n)] -> 1.
```

The shipped route takes `w(n)=log log n` and proves the claim by splitting
on the fractional first-moment parameter `x=alpha_0-floor(alpha_0)`.

## How to read this package

- *For the analytical proof*: start with `proof/proof.md`.
- *For the Lean formalization*: start with `Erdos625/README.md`.
- *For provenance, methodology, and LLM-pipeline disclosure*: see `DEVELOPMENT.md` ADR-10 through ADR-12.
- *For axiom citation details and per-axiom source audit*: see `paper/SOURCES.md`.

## Current status

**Analytical proof status**: all three regimes covered with source theorem notes
included in this package (`proof/source-notes/`), each with a closed source
argument — see `proof/proof.md` §Dependency-status table.

**Lean status**: checked companion theorem plus a compiled analytical
dependency wrapper.  The Lean files prove a separate fixed-epsilon
in-probability theorem `Problem625.Publishable.erdos_625_full_clean` and now
also expose `Problem625.Analytical.erdos_625_full_analytical`, a Lean-facing
wrapper for the full analytical route.  The wrapper records the dependency
closure and formalizes the final assembly/probability infrastructure, but it
still depends on three bridge-input-shaped source-package WHP bridge obligations.

**Certification status**: Not Lean-certified: the analytical wrapper theorem `erdos_625_full_analytical` depends on three WHP bridge obligations not yet formalized in Lean.

**Self-containment**: This package is self-contained.  All source theorem notes
for all three proof regimes are included in `proof/source-notes/`.  The middle
and upper branch notes
(`proof/source-notes/good-branch-partial-away-from-one-theorem-2026-05-13.md`,
`proof/source-notes/upper-boundary-r2-integrated-theorem-2026-05-13.md`, and
9 supporting files) were developed in the parent Erdosreshala repository
(same GitHub remote, `problems/625/work/notes/`) and are copied here for
reader convenience.  This repository: `https://github.com/uthunderbird/erdosreshala-625`.

## Main files

| Path | Role |
|---|---|
| `proof/proof.md` | Canonical full analytical proof writeup. |
| `paper/main.tex` | Companion paper for the analytical proof route. |
| `proof/ANALYTICAL_WRAPPER_AXIOM_SNAPSHOT.txt` | Recorded `#print axioms` output for the analytical wrapper theorem. |
| `Erdos625/PublishableProof.lean` | Lean companion theorem for the separate fixed-epsilon in-probability result. |
| `Erdos625/AnalyticalWrapper.lean` | Lean-facing wrapper theorem and dependency closure for the full analytical route. |
| `Erdos625/LowBranch.lean` | Lean-facing numerical certificate and interval skeleton for the low-branch finite-room margins. |
| `Erdos625/MiddleBranch.lean` | Lean-facing numerical certificate and interval skeleton for the middle-branch modified Lemma 7.20 package. |
| `Erdos625/UpperR2.lean` | Lean-facing numerical certificate, interval skeleton, and named appendix endpoint quantities for the upper-boundary `r=2` branch. |

## Analytical theorem

Let

```text
alpha_0 = 2 log_2 n - 2 log_2 log_2 n + 2 log_2(e/2) + 1,
alpha = floor(alpha_0),
x = alpha_0-alpha.
```

The proof covers all `x in [0,1)` by three regimes:

| Regime | Range | Shipped source theorem | Bound |
|---|---|---|---|
| Low | `[0,0.029155]` | First-moment (Markov) method, 2026-05-15 (HP-2023 Le.7.4, Le.7.3=HRHowdoes Co.39; Heckel 2024 line 516) | `(c_*-o(1)) n/log^3 n` |
| Middle | `[0.029155,0.95]` | `proof/source-notes/good-branch-partial-away-from-one-theorem-2026-05-13.md` | polynomial positive gap |
| Upper | `[0.95,1)` | `proof/source-notes/upper-boundary-r2-integrated-theorem-2026-05-13.md` | `0.001 n/log^3 n-o(n/log^3 n)` |

Each regime bound eventually dominates `log log n`, so the deterministic
choice `w(n)=log log n` proves the analytical claim.

## Lean boundary

The fixed-epsilon Lean theorem remains useful, but it is not the theorem
above.

`Problem625.Publishable.erdos_625_full_clean` states that for every fixed
real `epsilon` with `0 < epsilon < 0.001`, eventually in `n`,

```text
P[chi(G)-zeta(G) >= n^(1-2epsilon)] >= 1-2epsilon.
```

That is a fixed-epsilon quantitative in-probability theorem.  It is not a
formalization of the full analytical proof route and should not be cited as
machine certification of `proof/proof.md`.

The module `Erdos625.AnalyticalWrapper` also compiles.  It provides the
Lean-facing theorem
`Problem625.Analytical.erdos_625_full_analytical` and records the current
dependency closure for the full analytical route.  Not Lean-certified: the analytical wrapper theorem `erdos_625_full_analytical` depends on three WHP bridge obligations not yet formalized in Lean.

To inspect the wrapper axiom inventory:

```lean
import Erdos625.AnalyticalWrapper
#print axioms Problem625.Analytical.erdos_625_full_analytical
```

The expected output is recorded in
`proof/ANALYTICAL_WRAPPER_AXIOM_SNAPSHOT.txt`.

The current package does not include reproducibility scripts for the analytical
wrapper.  To verify the axiom closure, inspect the recorded snapshot directly
and run `#print axioms` in a local Lean build.

The three bridge-input-shaped source-package WHP bridge obligations remain in
the axiom closure of the current package.  ("Bridge-input-shaped" means each
obligation requires as input a source-theorem-level analytical result — a
"bridge input" — not yet formalized in Lean; satisfying it would require
formalizing a substantial paper argument, not just filling a local proof gap.)  Two additional source-artifact
caveats remain open: the middle source artifact leaves the residual region
`x > 1-epsilon_0` open, and the upper source artifact still depends on
explicit directed interval tables replacing finite decimal certificate checks.

The analytical wrapper (`Erdos625/AnalyticalWrapper.lean`) directly imports
the low, middle, and upper branch modules.  Each module combines the numerical
certificate interface with the interval-skeleton consumer, proving
certificate-to-slack consequences for its branch and exposing handoff shapes
for the remaining WHP bridge obligations.  The three remaining WHP obligations
are recorded in `AnalyticalRemainingConcreteObligations` within the wrapper.

For detailed Lean internals (adapter names, constructor chains, component
contracts), see the source files directly: `Erdos625/AnalyticalWrapper.lean`,
`Erdos625/LowBranch.lean`, `Erdos625/MiddleBranch.lean`,
`Erdos625/UpperR2.lean`.

To inspect the Lean axiom inventory:

```lean
import Erdos625.PublishableProof
#print axioms Problem625.Publishable.erdos_625_full_clean
```

The axiom snapshot for the publishable companion theorem is not separately
recorded in this package.  Use `#print axioms` in a local Lean build to
inspect it.

## Lemma and axiom source audit

The analytical proof is a full analytical proof with bundled route notes and
an explicit interval appendix.  The formerly non-literal Lean companion
assumptions `lemma_7_20_modified` and `zeta_alphaMinusTwo_upper_bound_whp`
are discharged as package analytical lemmas.  Those two statements are still
not literal primary-source theorem quotes.

Do not describe A1/A4 as literal source theorems; cite them as package
lemmas.

## Building the Lean companion

Prerequisites: Lean 4 / Lake via `elan`.  The toolchain is pinned in
`lean-toolchain`.

```bash
lake exe cache get
lake build
```

These commands verify the Lean companion theorem and the analytical wrapper.
They do not yet verify the full analytical route without assumptions.

## Checking the interval appendix

The upper-boundary appendix interval table is included in this package at:

```text
proof/source-notes/upper-boundary-r2-explicit-interval-tables-2026-05-13.md
```

It supplies explicit finite interval bounds for the `R2-G1` certificate.
It is a reproducibility aid for the interval table, not a formal proof certificate.

## Repository layout

| Path | Contents |
|---|---|
| `Erdos625.lean` | Lean library root. |
| `Erdos625/` | Lean formalization of the fixed-epsilon companion theorem and supporting modules. |
| `proof/proof.md` | Main analytical proof. |
| `proof/source-notes/` | Source theorem notes for all three proof regimes (12 files). |
| `proof/ANALYTICAL_WRAPPER_AXIOM_SNAPSHOT.txt` | Lean axiom snapshot for the analytical wrapper theorem. |
| `paper/main.tex` | Companion paper. |
| `DEVELOPMENT.md` | Development notes and architectural decisions. |
| `ROADMAP.md` | Remaining limitations and follow-up work. |

## References

- Heckel, A. & Panagiotou, K. (2023). *Colouring random graphs: Tame colourings.* arXiv:2306.07253. (Cited as HP-2023.)
- Heckel, A. (2024). *The difference between the chromatic and the cochromatic number of a random graph.* arXiv:2409.17614. (Cited as Heckel 2024.)
- Heckel, A. & Riordan, O. (2023). *How does the chromatic number of a random graph vary?* Journal of the London Mathematical Society, 108(5):1769–1815. (Cited as HRHowdoes; this is the internal TeX key used in HP-2023's source for lemmas originating in this paper.)
- The Erdős Problems, Problem 625: https://www.erdosproblems.com/625

## License

Apache 2.0.
