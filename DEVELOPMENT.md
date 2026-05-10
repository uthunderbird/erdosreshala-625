# Post-Proof Public Repository Design — Erdős Problem 625

**Produced by**: Swarm session, 2026-05-10
**Status**: Design spec — ready for implementation

---

## 1. Repository Overview

**Name**: `erdos-625-formalization` (GitHub repo name)
**Lake library name**: `Erdos625`
**Purpose**: Standalone, self-contained public formalization of Erdős Problem 625.
**Not required**: The full `erdosreshala` monorepo.

**The theorem**: In G(n, 1/2), for every 0 < ε < 0.001, with probability ≥ 1 − 2ε
(for all large n in the main-range regime), χ(G) − ζ(G) ≥ n^{1−ε}.

**Proof status**: Complete. 3 paper-backed axioms, 0 sorry.

---

## 2. Directory Tree

```
erdos-625-formalization/
├── README.md                    ← primary entry point; see §4
├── DEVELOPMENT.md               ← architectural decision records; see §6
├── lean-toolchain               ← leanprover/lean4:v4.29.0-rc8
├── lakefile.toml                ← see §5
├── lake-manifest.json           ← generated fresh via `lake update`; committed
├── .github/
│   └── workflows/
│       └── build.yml            ← CI; see §7
├── Erdos625/                    ← all Lean source; see §3
│   ├── README.md                ← Lean file guide for non-Lean readers; see §4.3
│   ├── Defs.lean
│   ├── ColoringBasic.lean
│   ├── GapArithmetic.lean
│   ├── FirstMomentThreshold.lean
│   ├── BoundedDifferences.lean
│   ├── IndepMoments.lean
│   ├── PartBProfileBridge.lean
│   ├── ChromaticConnection.lean
│   ├── ZetaConcentration.lean
│   ├── RouteD2.lean
│   ├── PublishableProof.lean
│   └── extras/                  ← optional; see §3.3
│       └── SharpProfileBound.lean   ← include only if compiles cleanly
├── proof/
│   └── proof.md                 ← the 148-line standalone mathematical document
└── paper/
    └── SOURCES.md               ← citations for the 3 paper axioms; see §4.4
```

**Total top-level files**: 5 (`README.md`, `DEVELOPMENT.md`, `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`).

---

## 3. Lean Source Files

### 3.1 Load-Bearing Files (all 11 required for `erdos_625`)

All 11 files below are in the transitive import closure of
`Problem625.Publishable.erdos_625`. None may be omitted.

| File | Role | Dependency layer |
|------|------|-----------------|
| `Defs.lean` | Core definitions: `gnHalf`, `chromaticNumber`, `cochromaticNumber`, `InMainRange`, `kThresholdWitness` | Layer 0 (base) |
| `ColoringBasic.lean` | Coloring combinatorics (Proposition 6) | Layer 1 |
| `GapArithmetic.lean` | Gap arithmetic: n^{1−ε/2} − n^{1−0.9ε} − 2n^{0.999} ≥ n^{1−ε} for ε < 0.001 | Layer 1 |
| `FirstMomentThreshold.lean` | First-moment threshold `kThresholdWitness`; t-bounded coloring count | Layer 2 |
| `BoundedDifferences.lean` | Lipschitz-1 property of cochromaticNumber under vertex deletion | Layer 2 |
| `IndepMoments.lean` | Independence number moment estimates | Layer 2 |
| `PartBProfileBridge.lean` | Part B bridge; **2 paper axioms declared here** | Layer 3 |
| `ChromaticConnection.lean` | Part B chain: `heckel_chromatic_lower_bound_of_exactNoEmpty`; 0 sorry | Layer 3 |
| `ZetaConcentration.lean` | Part C chain: Azuma–Hoeffding + Paley–Zygmund; **1 paper axiom declared here**; 0 sorry | Layer 3 |
| `RouteD2.lean` | Upstream theorem `gnHalf_gap_ge_n_pow_one_minus_eps_of_exactNoEmpty` | Layer 4 |
| `PublishableProof.lean` | Entry point: `erdos_625`; human-readable proof skeleton | Layer 5 |

### 3.2 Excluded Files

These files exist in the monorepo but are **not** imported by `erdos_625` and
should be excluded from the public repo's main source tree:

- `Test625.lean` — test/scratch file; no load-bearing theorems
- `SharpProfileBound.lean` — alternative discharge route for Axiom 1 (see §3.3)

### 3.3 extras/ — Optional Inclusion

`SharpProfileBound.lean` contains a Cauchy-Schwarz approach to discharging
`paperPartBThresholdAverageClassAsymptoticLowerCriterionTarget_source` (Axiom 1 from HP-2023).
It was developed but not used in the final proof.

**Include in `Erdos625/extras/` if and only if it compiles cleanly after
namespace migration** (`import Erdos625.X` instead of `import Erdosreshala.Problem625.X`).
If it has `sorry`s or import failures in the public repo, exclude it entirely —
a broken file in `extras/` is worse than its absence.

If included, add to `Erdos625/extras/README.md`:
> This file contains an alternative partial proof of Axiom 1. It is not part of the
> main proof of `erdos_625` and does not affect the 3-axiom count. It is preserved
> as a proof-engineering artifact showing how Axiom 1 might be discharged in future work.

### 3.4 Namespace and Import Paths

**Library name**: `Erdos625` (matches source directory and lakefile)
**Internal namespace**: Keep `Problem625` as the Lean namespace within files — this is what
the Lean kernel sees and matches the current formalization. Do not rename internal namespaces.
**Import paths**: `import Erdos625.PublishableProof`, `import Erdos625.Defs`, etc.

This requires updating every `import Erdosreshala.Problem625.X` to `import Erdos625.X`
in all 11 Lean files. The internal `namespace Problem625` declarations do not change.

---

## 4. Documentation Files

### 4.1 README.md (root)

Audience: anyone who lands on the GitHub page.
Length: ≤ 60 lines; dense with links.

Outline:
```
# Erdős Problem 625 — Lean 4 Formalization

## Statement
[1 paragraph: state the theorem in plain language and LaTeX]
[Link to proof/proof.md for the full mathematical argument]

## Axiom Inventory
[Table: 3 paper axioms, their names, files, and paper sources]
[Note: #print axioms produces exactly 6 items: 3 paper axioms +
 propext + Classical.choice + Quot.sound]
[Note on non-reachable axioms in PartBProfileBridge.lean]

## Building and Verifying

### Prerequisites
- Lean 4 / Lake (leanprover/lean4:v4.29.0-rc8)
- Internet access for first build (downloads Mathlib ~4 GB olean cache)

### Build steps
    git clone https://github.com/[user]/erdos-625-formalization
    cd erdos-625-formalization
    lake exe cache get        # downloads prebuilt Mathlib oleans (fast)
    lake build                # builds the formalization (~5 min with cache)

### Verify axiom count
    # In a Lean file or via lake env:
    #print axioms Problem625.Publishable.erdos_625
    # Expected output: 6 lines (3 paper axioms + 3 standard Lean axioms)

## Repository Structure
[Brief description of proof/, Erdos625/, DEVELOPMENT.md]

## References
[HP-2023: arXiv:2306.07253]
[Heckel 2024: arXiv:2409.17614]

## License
[Choose: Apache 2.0 recommended for Lean/Mathlib ecosystem compatibility]
```

### 4.2 proof/proof.md

This is the existing 148-line `problems/625/solution/proof.md`. Copy verbatim.
No changes needed — it is already a clean standalone document.

Update one line: the "File roles" section mentions file names as relative paths
within the Lean repository. Adjust to match `Erdos625/` prefix if needed.

### 4.3 Erdos625/README.md

Audience: mathematician who has read `proof.md` and wants to understand how it
maps to Lean. Assumes **zero Lean knowledge**.

Outline:
```
# Lean Source Guide

This directory contains the Lean 4 formalization of Erdős Problem 625.
If you are new to Lean, this guide explains what each file does and how
the files relate to the mathematical argument in ../proof/proof.md.

## What "axiom" means in Lean 4
[2 sentences: an `axiom` in Lean 4 is an admitted statement — like a
 lemma cited from a paper that has not been formalized. It is not a
 logical axiom in the foundational sense.]

## What `#print axioms` tells you
[Explain: running `#print axioms Problem625.Publishable.erdos_625`
 lists every admitted term in the proof's dependency closure.
 This proof produces 6 entries: 3 paper-backed axioms (named below)
 + propext, Classical.choice, Quot.sound (standard Lean axioms used
 in all Lean 4 proofs that reason about equality and existence).]

## File roles (in proof order)

### Definitions and infrastructure
- `Defs.lean` — core definitions (gnHalf, chromaticNumber, cochromaticNumber,
  InMainRange, kThresholdWitness)
- `ColoringBasic.lean` — coloring combinatorics (Proposition 6 of HP-2023)
- `GapArithmetic.lean` — the gap arithmetic inequality (§"Gap Arithmetic" in proof.md)
- `FirstMomentThreshold.lean` — the first-moment threshold k* (§"Part B" in proof.md)
- `BoundedDifferences.lean` — Lipschitz property of ζ needed for Azuma concentration
- `IndepMoments.lean` — independence number moment estimates

### Part B — Chromatic lower bound (2 axioms)
- `PartBProfileBridge.lean` — declares the 2 paper axioms from HP-2023
- `ChromaticConnection.lean` — proves the chromatic lower bound from those axioms; 0 sorry

### Part C — Cochromatic upper bound (1 axiom)
- `ZetaConcentration.lean` — declares the 1 paper axiom from Heckel 2024;
  proves the cochromatic upper bound via Azuma–Hoeffding; 0 sorry

### Assembly
- `RouteD2.lean` — intermediate theorem combining Parts B and C
- `PublishableProof.lean` — the main theorem `erdos_625`; start here

## Reading order
PublishableProof.lean → RouteD2.lean → ChromaticConnection.lean + ZetaConcentration.lean
→ PartBProfileBridge.lean + GapArithmetic.lean + FirstMomentThreshold.lean
→ Defs.lean + ColoringBasic.lean
```

### 4.4 paper/SOURCES.md

Short document (≤ 30 lines) listing:
- The 3 paper axioms and their exact citations (paper, theorem/equation number, arXiv ID)
- A note on the non-reachable axioms
- Brief description of what each paper contributes

This separates citation bookkeeping from the README (which would get cluttered).

---

## 5. lakefile.toml

```toml
name = "Erdos625"
version = "1.0.0"
defaultTargets = ["Erdos625"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4"
rev = "v4.29.0-rc8"

[[lean_lib]]
name = "Erdos625"
```

**Notes**:
- `version = "1.0.0"` signals this is a finalized proof, not a work in progress
- The `lean_lib` name `Erdos625` matches the source directory
- The Mathlib rev must exactly match the monorepo's `v4.29.0-rc8`

---

## 6. DEVELOPMENT.md — Architectural Decision Records

Audience: formalization researchers, mathematicians curious about proof engineering.
Format: ADR (Architectural Decision Record) — each entry is self-contained.

**Decision on content**: 426 session notes from `problems/625/work/notes/` are NOT
included in the public repo. They are too numerous and context-dependent to be
useful without the surrounding development infrastructure. The ADRs below distill
the key architectural decisions into a durable, navigable form.

**Decision on git history**: Initialize the public repo with a curated commit history
(not a single squashed commit). Use milestone commits — one commit per major proof
component closed. Suggested milestone commits:
1. "Initial repo structure with Lean source and lakefile"
2. "Add core definitions and coloring infrastructure (Defs, ColoringBasic)"
3. "Prove gap arithmetic (GapArithmetic.lean)"
4. "Add Part C: Azuma–Hoeffding concentration and cochromatic upper bound"
5. "Add Part B: chromatic lower bound via exact-no-empty profile chain"
6. "Complete proof: PublishableProof.lean with 3 axioms, 0 sorry"

Outline:
```
# Development History — Architectural Decision Records

This document records the key architectural decisions made during the formalization
of Erdős Problem 625. It is written for readers who want to understand *why* the
proof is structured as it is, not just *what* it proves.

## ADR-1: Route selection — exact-no-empty profile chain vs. Theorem 1 route

**Date**: 2026-05-05
**Question**: HP-2023 proves a chromatic lower bound via two routes:
  (A) Theorem 1 (direct first-moment argument, axiomatizes Theorem 1 of HP-2023)
  (B) Lemma 5 + eq:wert + eq:wert2 (exact-no-empty profile reduction, axiomatizes
      two specific equations)
**Options considered**:
  - Route A: simpler to state, but axiomatizes a full theorem
  - Route B: more detailed, axiomatizes the two specific paper equations that do
    the real work; leaves the combinatorial reduction fully proved
**Decision**: Route B (exact-no-empty profile chain)
**Rationale**: Route B has a smaller axiom footprint per unit of mathematical content.
  Axiomatizing Lemma 5 + eq:wert (rather than the full Theorem 1) proves more
  in Lean and admits less. The exact-no-empty chain is fully proved (0 sorry above
  the two source lemmas).

## ADR-2: Cochromatic upper bound — Azuma–Hoeffding concentration strategy

**Date**: 2026-04-13 to 2026-04-15
**Question**: How to prove P[ζ(G) ≤ k* − n^{1−ε/2} + 2n^{0.999}] ≥ 1 − ε?
**Options considered**:
  - Direct second-moment method (Paley–Zygmund) applied to ζ
  - Azuma–Hoeffding via vertex-exposure martingale + Paley–Zygmund for existence
**Decision**: Two-stage approach: Paley–Zygmund for P[Z > 0] > 0, then Azuma for
  concentration to 1 − ε.
**Rationale**: The Azuma infrastructure (BoundedDifferences.lean, ZetaConcentration.lean)
  is fully proved with 0 sorry. The Paley–Zygmund step requires Proposition 5(b) of
  Heckel 2024 (the one remaining axiom in Part C), which provides the second-moment
  bound on Z. This clean separation means the concentration argument is fully verified
  and only the second-moment bound is admitted.

## ADR-3: Gap arithmetic — proved, not axiomatized

**Date**: 2026-04-30
**Question**: Should the inequality n^{1−ε/2} − n^{1−0.9ε} − 2n^{0.999} ≥ n^{1−ε}
  (for ε < 0.001) be axiomatized or proved?
**Decision**: Proved (GapArithmetic.lean, 0 sorry, 0 axioms).
**Rationale**: This is a purely analytic inequality involving `Real.rpow`. Lean's
  `norm_num` and `rpow` tactics can handle it. Axiomatizing a provable inequality
  inflates the axiom count without mathematical justification.

## ADR-4: Axiom naming and citation discipline

**Date**: 2026-05-05 to 2026-05-10
**Question**: How should paper axioms be named and cited in Lean?
**Decision**: Each axiom name encodes the mathematical content it captures
  (e.g., `paperPartBThresholdAverageClassAsymptoticLowerCriterionTarget_source`).
  Each axiom declaration includes a comment citing: paper title, arXiv ID, theorem/
  equation number, and a plain-language description.
**Rationale**: Verbose names make `#print axioms` output self-documenting. A reader
  who sees `heckel_cochromatic_second_moment` immediately knows which mathematical
  claim is admitted. Generic names like `axiom_hp_1` would require cross-referencing.

## ADR-5: Development history — ADRs vs. session notes

**Date**: 2026-05-10
**Question**: How much development history to preserve in the public repo?
**Decision**: 5 ADRs (this document) + curated milestone git history.
  The 426 session notes from the development monorepo are not included.
**Rationale**: Session notes are useful for active development but are too context-
  dependent and numerous to be navigable for an external reader. ADRs extract the
  durable architectural decisions; git history shows the development arc at a coarse
  level. The monorepo preserves the full session-level detail for internal use.
```

**ADR template** (for any future additions):
```
## ADR-N: [Short title]

**Date**: YYYY-MM-DD
**Question**: [What was the decision about?]
**Options considered**: [List at least 2]
**Decision**: [What was chosen?]
**Rationale**: [Why? What evidence or argument was decisive?]
```

---

## 7. CI Workflow (.github/workflows/build.yml)

```yaml
name: Build Lean Formalization

on:
  push:
    branches: [main]
  pull_request:
    branches: [main]

jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Install Lean 4
        uses: leanprover/lean4-action@v1
        with:
          lean-version: leanprover/lean4:v4.29.0-rc8

      - name: Get Mathlib cache
        run: lake exe cache get

      - name: Build
        run: lake build

      - name: Verify axiom count (informational)
        run: |
          lake env lean --run - << 'EOF'
          import Erdos625.PublishableProof
          #print axioms Problem625.Publishable.erdos_625
          EOF
```

**Notes**:
- The `leanprover/lean4-action` action handles toolchain installation
- `lake exe cache get` is essential — without it, building Mathlib from source
  takes 45-90 minutes and will time out on free GitHub Actions runners
- The axiom-count step is informational (it will print, not fail) — its output
  should list exactly 6 items

---

## 8. Implementation Steps (for the creator of the public repo)

In order:

1. Create new GitHub repo `erdos-625-formalization`
2. Create directory structure per §2
3. Copy the 11 load-bearing Lean files from `Erdosreshala/Problem625/`
4. Update all `import Erdosreshala.Problem625.X` to `import Erdos625.X` in all 11 files
5. Create `lakefile.toml` per §5; create `lean-toolchain` with `leanprover/lean4:v4.29.0-rc8`
6. Run `lake update` to generate fresh `lake-manifest.json`; commit it
7. Run `lake build` to verify clean compilation
8. Run `#print axioms Problem625.Publishable.erdos_625` — verify exactly 6 items
9. Copy `proof.md` to `proof/proof.md`; update file path references if needed
10. Write `README.md`, `Erdos625/README.md`, `paper/SOURCES.md`, `DEVELOPMENT.md` per §4/§6
11. Decide on `SharpProfileBound.lean` (test compile → include in `extras/` or exclude)
12. Add `.github/workflows/build.yml` per §7
13. Make milestone commits (see §6 git history section)
14. Verify CI passes on GitHub

---

## 9. Key Design Decisions Summary

| Decision | Choice | Rationale |
|----------|--------|-----------|
| Library/source dir name | `Erdos625/` | Mathlib convention: library name = source dir |
| Internal namespace | Keep `Problem625` | No rename needed; kernel-visible names unchanged |
| Import paths | `import Erdos625.X` | Matches library name |
| lake-manifest.json | Commit fresh copy | Pins transitive deps; generated in new isolated repo |
| Mathlib version | `v4.29.0-rc8` | Exact match to verified build |
| SharpProfileBound.lean | `extras/` if compiles | Valuable artifact; must not break build |
| Test625.lean | Excluded | Not load-bearing; clutters public repo |
| Development history | 5 ADRs + milestone git | Durable, navigable, avoids 426-item dump |
| Lean dir README audience | Zero Lean knowledge | Mathematicians need it; specialists skip it |
| Primary README length | ≤ 60 lines | First-60-seconds experience for GitHub visitors |
| CI | GitHub Actions + lean4-action + Mathlib cache | Verified reproducibility guarantee |

---

*Design artifact produced by Swarm session. All file structure decisions grounded against
actual file reads (Executor iteration). Decisions on lake-manifest.json, directory naming,
history format, and CI all arose from expert adjudication (A, A1, D rounds).*
