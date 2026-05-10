# Lean Source Guide

This directory contains the Lean 4 formalization of Erdős Problem 625.
If you are new to Lean, this guide explains what each file does and how
the files relate to the mathematical argument in [`../proof/proof.md`](../proof/proof.md).

## What "axiom" means in Lean 4

An `axiom` in Lean 4 is an admitted statement — like a lemma cited from a paper that has
not been formalized inside this repository. It is distinct from Lean's foundational axioms
(`propext`, `Classical.choice`, `Quot.sound`) which are part of the kernel. Paper-backed
axioms in this formalization are explicitly named and cited; see [`../paper/SOURCES.md`](../paper/SOURCES.md).

## What `#print axioms` tells you

Running `#print axioms Problem625.Publishable.erdos_625` lists every admitted term in the
proof's dependency closure. This proof produces **6 entries**:

- 3 paper-backed axioms (named and cited in `PartBProfileBridge.lean` and `ZetaConcentration.lean`)
- `propext`, `Classical.choice`, `Quot.sound` — standard Lean axioms used in all Lean 4
  proofs that reason about equality and existence

## File roles (in proof order)

### Definitions and infrastructure

| File | Contents |
|------|----------|
| `Defs.lean` | Core definitions: `gnHalf` (G(n,1/2) measure), `chromaticNumber`, `cochromaticNumber`, `InMainRange`, `kThresholdWitness` |
| `ColoringBasic.lean` | Coloring combinatorics (Proposition 6 of HP-2023) |
| `GapArithmetic.lean` | Gap arithmetic inequality: n^{1−ε/2} − n^{1−0.9ε} − 2n^{0.999} ≥ n^{1−ε} for ε < 0.001; **0 axioms, 0 sorry** |
| `FirstMomentThreshold.lean` | First-moment threshold k* (= `kThresholdWitness`); t-bounded coloring count |
| `BoundedDifferences.lean` | Lipschitz-1 property of ζ under vertex deletion (needed for Azuma concentration) |
| `IndepMoments.lean` | Independence number moment estimates |

### Part B — Chromatic lower bound (2 axioms from HP-2023)

| File | Contents |
|------|----------|
| `PartBProfileBridge.lean` | Declares the 2 paper axioms from HP-2023; proves the combinatorial bridge to `heckel_chromatic_lower_bound_of_exactNoEmpty` |
| `ChromaticConnection.lean` | Proves P[χ(G) ≥ k* − n^{1−0.9ε}] ≥ 1 − ε from those axioms; **0 sorry** |

### Part C — Cochromatic upper bound (1 axiom from Heckel 2024)

| File | Contents |
|------|----------|
| `ZetaConcentration.lean` | Declares 1 paper axiom (Proposition 5(b) of Heckel 2024); proves Azuma–Hoeffding concentration and P[ζ(G) ≤ k* − n^{1−ε/2} + 2n^{0.999}] ≥ 1 − ε; **0 sorry** |

### Assembly

| File | Contents |
|------|----------|
| `RouteD2.lean` | Intermediate theorem `gnHalf_gap_ge_n_pow_one_minus_eps_of_exactNoEmpty` combining Parts B and C |
| `PublishableProof.lean` | **Start here.** Main theorem `erdos_625` with named steps (`part_B`, `part_C`, `joint_bound`) and full inline citations |

## Suggested reading order

```
PublishableProof.lean
  → RouteD2.lean
    → ChromaticConnection.lean   → PartBProfileBridge.lean → FirstMomentThreshold.lean
    → ZetaConcentration.lean     → BoundedDifferences.lean
    → GapArithmetic.lean
  → Defs.lean, ColoringBasic.lean, IndepMoments.lean
```
