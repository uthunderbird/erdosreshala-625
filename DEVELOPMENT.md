# Development Notes — Architectural Decision Records

This document records the key architectural decisions made during the formalization
of Erdős Problem 625. It is written for readers who want to understand *why* the
proof is structured as it is, not just *what* it proves.

---

## ADR-1: Route selection — exact-no-empty profile chain vs. Theorem 1 route

**Date**: 2026-05-05

**Question**: HP-2023 proves a chromatic lower bound via two routes:
- Route A: Theorem 1 (direct first-moment argument; axiomatizes the full Theorem 1 of HP-2023)
- Route B: Lemma 5 + eq:wert + eq:wert2 (exact-no-empty profile reduction; axiomatizes two specific equations)

**Options considered**:
- Route A: simpler to state, but axiomatizes a full theorem — admitting more mathematical content as black-box
- Route B: more detailed; axiomatizes the two specific paper equations that do the real work; the combinatorial reduction connecting those equations to the chromatic lower bound is fully proved in Lean

**Decision**: Route B (exact-no-empty profile chain, implemented in `PartBProfileBridge.lean` and `ChromaticConnection.lean`)

**Rationale**: Route B has a smaller axiom footprint per unit of mathematical content. Axiomatizing Lemma 5 + eq:wert (rather than the full Theorem 1) means more of the proof is verified in Lean and less is admitted. The exact-no-empty chain is fully proved with 0 sorry above the two source lemmas.

---

## ADR-2: Cochromatic upper bound — Azuma–Hoeffding concentration strategy

**Date**: 2026-04-13 to 2026-04-15

**Question**: How to prove P[ζ(G) ≤ k* − n^{1−ε/2} + 2n^{0.999}] ≥ 1 − ε?

**Options considered**:
- Direct second-moment method (Paley–Zygmund) applied directly to ζ — would need the full second-moment distribution of ζ, which is not available from the paper
- Two-stage approach: Paley–Zygmund for existence (P[Z > 0] > 0 for a specific coloring count Z), then Azuma–Hoeffding for concentration (ζ is 1-Lipschitz under vertex exposure)

**Decision**: Two-stage approach (implemented in `ZetaConcentration.lean` and `BoundedDifferences.lean`)

**Rationale**: The Azuma–Hoeffding concentration infrastructure (BoundedDifferences.lean) is fully proved with 0 sorry — this is the part that produces the high-probability bound from a mere existence statement. The Paley–Zygmund step requires Proposition 5(b) of Heckel 2024, which provides the second-moment bound on Z; this is the single admitted axiom in Part C. The separation cleanly isolates what is verified (concentration) from what is admitted (the second-moment bound).

---

## ADR-3: Gap arithmetic — proved, not axiomatized

**Date**: 2026-04-30

**Question**: Should the inequality n^{1−ε/2} − n^{1−0.9ε} − 2n^{0.999} ≥ n^{1−ε} (for ε < 0.001 and all large n) be axiomatized or proved?

**Options considered**:
- Axiomatize: treat it as a cited analytic fact, like the paper-backed axioms
- Prove: formalize it directly using Lean's `Real.rpow` machinery

**Decision**: Proved (implemented in `GapArithmetic.lean`, 0 sorry, 0 axioms)

**Rationale**: This is a purely analytic inequality with no probabilistic content. Lean's `norm_num` and `rpow` tactics can handle it. Axiomatizing a provable inequality inflates the axiom count without mathematical justification and removes an opportunity for a fully verified component.

---

## ADR-4: Axiom naming and citation discipline

**Date**: 2026-05-05 to 2026-05-10

**Question**: How should paper-backed axioms be named and cited in Lean?

**Options considered**:
- Short generic names (e.g., `axiom_hp_1`, `axiom_hp_2`, `axiom_heckel_1`) — easy to read but require cross-referencing to understand what is admitted
- Descriptive content-encoding names (e.g., `paperPartBThresholdAverageClassAsymptoticLowerCriterionTarget_source`) — verbose but self-documenting

**Decision**: Descriptive content-encoding names, with each axiom declaration citing the paper, arXiv ID, theorem/equation number, and a plain-language description

**Rationale**: When a reader runs `#print axioms Problem625.Publishable.erdos_625`, the output is the primary record of what is admitted. Self-documenting names make this output interpretable without cross-referencing. A reader who sees `heckel_cochromatic_second_moment` immediately knows which mathematical claim is admitted; `axiom_hp_1` would require consulting a separate document.

---

## ADR-5: Development history — ADRs vs. session notes

**Date**: 2026-05-10

**Question**: How much development history to preserve in the public repository?

**Options considered**:
- Include full session notes — several hundred notes documenting each proof engineering decision, failed attempt, and diagnostic pass
- Include only ADRs — five records covering the durable architectural decisions, with a curated milestone git history

**Decision**: 5 ADRs (this document) + milestone git history. Session notes are not included.

**Rationale**: Session notes are indispensable during active development but are too context-dependent and voluminous to be navigable for an external reader. ADRs extract the durable decisions that affect how the proof is structured and why. The git history provides a coarse-grained development arc. Readers wanting finer-grained detail should consult the proof and source files directly.

---

## ADR Template

For any future additions, use:

```
## ADR-N: [Short title]

**Date**: YYYY-MM-DD

**Question**: [What was the decision about?]

**Options considered**:
- [Option 1: describe and assess]
- [Option 2: describe and assess]

**Decision**: [What was chosen?]

**Rationale**: [Why? What evidence or argument was decisive?]
```
