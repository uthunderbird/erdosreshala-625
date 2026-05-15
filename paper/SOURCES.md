# Paper Sources for the Paper-Backed Axioms

This file records the precise paper citations for the paper-backed axioms in
the formalization of Erdős Problem 625, separated by which theorem they
appear in.

## Flagship `erdos_625_full_clean` — 4 paper axioms

Running `#print axioms Problem625.Publishable.erdos_625_full_clean` returns:

1. `Problem625.Publishable.lemma_7_20_modified` — see Axiom A1 below.
2. `Problem625.partB_alphaMinusTwo_firstMomentBelowOne_source` — see A2.
3. `Problem625.chi_alphaMinusTwo_lower_bound_whp` — see A3.
4. `Problem625.zeta_alphaMinusTwo_upper_bound_whp` — see A4.

Plus the three Lean kernel axioms: `propext`, `Classical.choice`, `Quot.sound`.

### A1. `lemma_7_20_modified` (hybrid)

**Lean name**: `Problem625.Publishable.lemma_7_20_modified`
**File**: `Erdos625/PublishableProof.lean:399` (line numbers as of 2026-05-12; may drift with future edits — locate by `grep -n '^axiom lemma_7_20_modified'`)

**Sources**:
- Heckel, A. & Panagiotou, K. (2023). *Colouring random graphs: Tame
  colourings*. arXiv:2306.07253. §7, Lemma 7.20, with condition (d)
  weakened from $\mu_\alpha \ge n^{1.05}$ to $\mu_\alpha \ge n^{x_0+\varepsilon}$
  where $x_0 \approx 0.02905$.
- Heckel, A. (2024). *The difference between the chromatic and the
  cochromatic number of a random graph*. arXiv:2409.17614. §Discussion
  explicitly conjectures the weakening above.
- Numerical certificate `lemma_7_10_ext`: in-repository Lipschitz envelope
  on a 1086-cell grid filling the $\varphi$-positivity gap
  $[x_0+\varepsilon, 0.04)$ outside HP-2023 Lemma 7.10's coverage.
  (Audit details are in the parent Erdosreshala repository work notes (https://github.com/uthunderbird/erdosreshala-625, subdirectory problems/625/work/notes/).)

**Status**: HYBRID. Combines a peer-reviewed paper claim with our own
(not peer-reviewed) numerical certificate. Disclosed in the Lean
docstring and in the dedicated audit note.

**Proposal authorship**: LLM agent (structurally proposed from
Heckel 2024 §Discussion's explicit conjecture); numerical
certificate script also LLM-authored. Human supervisor approved the
citation boundary. See `../DEVELOPMENT.md` ADR-11.

### A2. `partB_alphaMinusTwo_firstMomentBelowOne_source`

**Lean name**: `Problem625.partB_alphaMinusTwo_firstMomentBelowOne_source`
**File**: `Erdos625/PartBAlphaMinusTwoFirstMomentAxiom.lean:50` (line numbers as of 2026-05-12; may drift — locate by `grep -n '^axiom partB_alphaMinusTwo_firstMomentBelowOne_source'`)

**Source**: Heckel & Panagiotou (2023), arXiv:2306.07253, proof of
Lemma 8.1, first-moment input paragraph ("by the definition of the first
moment threshold, $E_{n, k_a-1, a} < 1$"), instantiated at level
$\alpha-2$ over a window of width $\lceil n / \log^2 n \rceil$ above
`kThresholdAlphaMinusOne n` (i.e. $\mathbf{k}_{\alpha-1}(n)$).

**Status**: literal paper citation, narrower than the original threshold-gap
conclusion (cites only the first-moment computation paragraph, not the
full Lemma 8.1 application).

**Proposal authorship**: LLM agent (narrowing of a prior wider axiom
`KThresholdGapSource`). Human supervisor approved the narrower
citation boundary. See `../DEVELOPMENT.md` ADR-11.

### A3. `chi_alphaMinusTwo_lower_bound_whp`

**Lean name**: `Problem625.chi_alphaMinusTwo_lower_bound_whp`
**File**: `Erdos625/CrossingPartB.lean:263` (line numbers as of 2026-05-12; may drift — locate by `grep -n '^axiom chi_alphaMinusTwo_lower_bound_whp'`)

**Source**: Heckel & Panagiotou (2023), arXiv:2306.07253, Lemma 8.1
($\chi_a \ge \mathbf{k}_a - 1$ whp for $a \in \{\alpha-1, \alpha-2\}$),
applied at $a = \alpha-2$, plus the standard Markov-style X-class
removal argument
($\chi(G) \ge \chi_{\alpha-2}(G) - X_\alpha - X_{\alpha-1}$, with both
correction terms negligible in the crossing regime). Slack $n^{0.99}$
absorbs both the constant-$1$ slack of Lemma 8.1 and the Azuma-Hoeffding
deviation of $\chi_a$.

**Status**: literal paper citation + standard derivation.

**Proposal authorship**: LLM agent, after a human-supervisor-flagged
sign-error correction on an initial attempt. Final statement is
LLM-authored. See `../DEVELOPMENT.md` ADR-11.

### A4. `zeta_alphaMinusTwo_upper_bound_whp` (extrapolation)

**Lean name**: `Problem625.zeta_alphaMinusTwo_upper_bound_whp`
**File**: `Erdos625/CrossingPartB.lean:311` (line numbers as of 2026-05-12; may drift — locate by `grep -n '^axiom zeta_alphaMinusTwo_upper_bound_whp'`)

**Source**: Heckel (2024), arXiv:2409.17614, Proposition 5(b) +
Azuma–Hoeffding, **adapted from $(\alpha-1)$-bounded to
$(\alpha-2)$-bounded cocolorings**. Heckel 2024 explicitly restricts
its tame-profile and second-moment construction to $\alpha-1$ (§3
line 341, §5.1 line 529); the $\alpha-2$ version is the natural
symmetric move via HP-2023's second-moment lemmas (stated for general
$a$-bounded profiles in HP-2023 §6.3–6.5).

**Status**: $\alpha-2$ EXTRAPOLATION of a published $\alpha-1$ result;
not a literal one-citation paper axiom. Detailed transfer audit is in
the parent Erdosreshala repository work notes (https://github.com/uthunderbird/erdosreshala-625, subdirectory problems/625/work/notes/).

**Proposal authorship**: LLM agent. The $\alpha-1 \to \alpha-2$
extrapolation framing emerged from an internal swarm session
moderated by the human supervisor and was then refined by the LLM
agent. Decision to admit the extrapolation as an axiom (rather
than block on a literal $\alpha-2$ peer-reviewed citation) was
approved by the human supervisor. See `../DEVELOPMENT.md` ADR-11.

## Legacy `erdos_625` and `erdos_625_97`

These supporting theorems use a different subset of axioms.

### `erdos_625` (95% n) — 3 paper axioms

`#print axioms Problem625.Publishable.erdos_625` returns:

1. `Problem625.paperPartBThresholdAverageClassAsymptoticLowerCriterionTarget_source` — HP-2023 Lemma 5 (`lemma:averagecolourclass`) + eq:wert.
2. `Problem625.paperPartBExactNoEmptyDenomBinaryLowerControlledLhsDecayTarget_source` — HP-2023 eq:wert2.
3. `Problem625.heckel_offdiag_term_bound` — Heckel 2024 Prop 5(b)
   off-diagonal term (a 2026-05-11 narrowing of the original
   `heckel_cochromatic_second_moment`, which is now a proved theorem on
   top of `heckel_offdiag_term_bound`).

Plus `propext`, `Classical.choice`, `Quot.sound`.

These three are **not** in the closure of `erdos_625_full_clean` because
the flagship's good case goes through `erdos_625_97` (which uses axiom A1
instead).

### `erdos_625_97` (97% n) — 1 paper axiom

`#print axioms Problem625.Publishable.erdos_625_97` returns:

1. `Problem625.Publishable.lemma_7_20_modified` (= A1 above).

Plus the three kernel axioms.

## Non-reachable axioms (do not affect any `#print axioms` count)

`grep "^axiom" Erdos625/*.lean` shows additional `axiom` declarations
that exist in the repository but are **not** in the dependency closure
of `erdos_625_full_clean`, `erdos_625`, or `erdos_625_97`. They belong
to alternative proof routes explored during development:

**In `PartBProfileBridge.lean`**:
- `profileLogCoreBridgeTarget_source` — used only by the legacy
  Theorem 1 chain (`gnHalf_gap_ge_n_pow_one_minus_eps`); not by any
  publishable theorem.
- `paperPartBEndpointClosedVectorTailMomentQBoundedProductProfilePDenomAffineHalfLogSlackSmallClosedUniformAsymptoticNegOneStirlingFactorialUpperSplitAtBotTarget_source`
  — alternative Stirling-endpoint discharge route for Part B; not on
  the publishable path.

**In `ChromaticConnection.lean`**:
- `threshold_tBoundedColoringError_le_with_error` — direct axiom form
  of the coloring-error bound; used by alternative chromatic chains.
- `kThresholdWitness_le_n_div_threshold` — alternative threshold
  comparison.
- `threshold_decay_axiom` — proved as a theorem
  (`threshold_decay_axiom_discharge`) and the proved version is what
  the publishable chain uses.

**In `ZetaConcentration.lean`**:
- `heckel_zeta_upper_tail`, `heckel_zeta_lower_tail` — alternative
  $\zeta$ tail bound derivations; not used.

## Analytical proof certificate disclosure

The Regime III (upper-boundary x ∈ [0.95,1)) proof depends on the R2-G1
numerical certificate:

```
Room_2(x) >= 0.07  and  Prefix_2(x) >= 0.006  uniformly on [0.95,1]
```

This certificate, including the mean-solver enclosures (μ₀ ∈ [1.99,2.00],
μ₂ ∈ [1.68,1.69]), the partition-function truncation at I=40, and the
prefix guard evaluation at x=0.95, consists of **original computations in
these source notes** (`proof/source-notes/upper-boundary-r2-directed-certificate-proof-2026-05-13.md`
and `proof/source-notes/upper-boundary-r2-explicit-interval-tables-2026-05-13.md`).
These specific numerical values do not appear in HP-2023, HRHowdoes, or
Heckel 2024. The computation was generated by the same LLM pipeline that
produced the rest of this package and has **not been independently verified
by a third party**.

The proof *framework* for Room/Prefix (the objective function, the
monotonicity reductions, the Paley-Zygmund and Azuma amplification chain)
is paper-backed (HP-2023 + Heckel 2024). The specific certificate values
are not.

## Lean axiom disclosure summary

- 2 of the 4 paper axioms in the flagship are HYBRID (A1) or
  EXTRAPOLATION (A4) of published results, not literal one-citation
  facts. Both are explicitly disclosed.
- The other 2 paper axioms (A2, A3) are literal HP-2023 citations.
- Five internal red-team passes verifying the disclosure framing are documented
  in the parent Erdosreshala repository work notes
  (https://github.com/uthunderbird/erdosreshala-625, subdirectory problems/625/work/notes/;
  conducted by the same LLM pipeline; see `../DEVELOPMENT.md` ADR-10 and ADR-12).
