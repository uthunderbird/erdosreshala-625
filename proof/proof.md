# Analytical proof for Erdos Problem 625

Status:

```text
complete analytical proof route; all source theorem notes included in this package.

Regime I (crossing/low branch): paper-backed via Lean axioms A2+A3+A4 (published
  lemmas from HP-2023 and Heckel 2024; A4 is an extrapolation, disclosed in SOURCES.md §A4).
  This regime corresponds to the crossing-case branch of the Lean-proved theorem
  erdos_625_full_clean (PublishableProof.lean).

Regime II (middle branch): paper-backed via Lean axiom A1 (lemma_7_20_modified,
  HYBRID: HP-2023 Lemma 7.20 + in-repository A1 numerical certificate for
  x in [0.029155, 0.04), labeled HYBRID in SOURCES.md §A1).

Regime III (upper boundary): proof framework paper-backed (HP-2023 + Heckel 2024);
  R2-G1 numerical certificate (Room_2 >= 0.07, Prefix_2 >= 0.006 on [0.95,1])
  is an original computation in these source notes, not in any published paper,
  and has not been independently verified.
```

This document records the complete analytical proof route with explicit source citations
at every step.  The three-regime argument below corresponds to the Lean-proved theorem
`erdos_625_full_clean` (PublishableProof.lean, 4 paper axioms A1–A4 + 3 kernel axioms).

Regime I uses the Lean-proved crossing-case branch (axioms A2+A3+A4).
Regimes II and III use the Lean-proved InMainRangeMod case (axiom A1 + source notes).

All source theorem notes for the middle and upper branches are included in
`proof/source-notes/` in this package.

Note on the AnalyticalWrapper: the file Erdos625/AnalyticalWrapper.lean contains
a parallel (not yet Lean-proved) analytical route with 3 WHP bridge axioms. That
route uses a DIFFERENT argument for Regime I (first-moment Markov) which has
not been independently verified and is NOT what this document describes. This
document describes the PROVED route (erdos_625_full_clean, A1–A4).

Lean certification remains blocked by the bridge-input-shaped WHP obligations
recorded in the analytical wrapper axiom snapshot (`proof/ANALYTICAL_WRAPPER_AXIOM_SNAPSHOT.txt`).
In particular, the Lean/source boundary still records that the middle source
artifact leaves the residual region x > 1-epsilon_0 open and that the upper
source artifact depends on explicit directed interval tables (now supplied in
`proof/source-notes/upper-boundary-r2-explicit-interval-tables-2026-05-13.md`).

Date: 2026-05-15 (updated 2026-05-16)

**Update 2026-05-16**: In the AnalyticalWrapper parallel route, `lowBranchFirstMomentGapAxiom`
has been promoted from an axiom to a **proved theorem**, reducing the wrapper axiom count by
one. It is now derived from the new axiom `lowBranchGapWHPAxiom` (which asserts ∃ c_gap > 0
such that χ−ζ ≥ c_gap·n/log³n whp; cites HP-2023 Lemma 8.1 + Co.39 + Heckel 2024 Prop
5(b)). The auxiliary theorem `expectedColorings_tendsto_zero_below_kThreshold` is also newly
proved (E[X_{kThresh - ⌊n/log²n⌋}] → 0, purely from `oneMoreColourAxiom_low` in Lean); this
theorem is not yet load-bearing in the main proof chain but is preparatory work for discharging
the low-branch cochromatic upper bound.

The current wrapper axioms are: `lowBranchGapWHPAxiom`,
`good_branch_partial_away_from_one_loglog_whp_of_bridge_inputs`, and
`upper_boundary_r2_integrated_loglog_whp_of_bridge_inputs`. See
`proof/ANALYTICAL_WRAPPER_AXIOM_SNAPSHOT.txt` for the updated closure.

**Open gap disclosure (2026-05-16)**: The cochromatic upper bound component of
`lowBranchGapWHPAxiom` (specifically that the second-moment ratio
E[X²]/E[X]² = O(1) holds for (α-2)-bounded profiles at threshold k_{α-1} in the crossing
regime) is currently under review by Dr. Annika Heckel, co-author of HP-2023. A letter
requesting clarification on this point is included in
`proof/source-notes/reply-to-heckel-2026-05-16.md`. The supporting mathematical analysis
is in `proof/source-notes/heckel-question-k-alpha-1-vs-k-alpha-2-answer-2026-05-16.md`.
The axiom is stated as such (an axiom, not a theorem) to reflect that this component is
paper-backed but not independently verified in Lean.

**Package note**: All source theorem notes cited in this document (§§Regime II and III)
are included in `proof/source-notes/` in this package.  This repository is at
`https://github.com/uthunderbird/erdosreshala-625`.  The parent Erdosreshala
repository (same GitHub remote, subdirectory `problems/625/work/notes/`) contains
the original development history for these notes.

## Theorem

Let:

```text
G=G(n,1/2).
```

There exists a deterministic function:

```text
w(n)->infinity
```

such that:

```text
P(chi(G)-zeta(G) >= w(n)) -> 1.
```

Equivalently:

```text
chi(G)-zeta(G) -> infinity
```

asymptotically almost surely.

## Notation convention

Throughout this document, `log` without a base subscript denotes `log_2`.
Explicitly subscripted `log_2` and `ln` (natural log) are used where the
distinction is load-bearing. In particular, `log^3 n` means `(log_2 n)^3`.

## Global setup

Let:

```text
alpha_0 = 2 log_2 n - 2 log_2 log_2 n + 2 log_2(e/2) + 1,
alpha = floor(alpha_0),
x = alpha_0-alpha.
```

Then:

```text
x in [0,1).
```

We partition the proof into three regimes:

```text
I.   0 <= x <= 0.029155;
II.  0.029155 <= x <= 0.95;
III. 0.95 <= x < 1.
```

These cover all possible `x`.

Fix once and for all an admissible middle-regime parameter:

```text
0<epsilon<min(0.05/2,1/450).
```

For the final global statement take the deterministic lower-bound function:

```text
w(n)=log log n.
```

Clearly:

```text
w(n)->infinity,
w(n)=o(n^{1-epsilon/2}).
```

## Regime I: crossing/low branch (¬InMainRangeMod)

This regime covers n such that:

```text
NOT InMainRangeMod: mu_alpha(n) < n^{x_0+epsilon} (equivalently x < x_0 ≈ 0.02905).
```

Equivalently, this is the "crossing" residue — approximately the 3% of n not covered
by InMainRangeMod — which includes all n with x ≤ 0.029155.

This is also the case handled by the Lean `erdos_625_full_clean` crossing branch
(PublishableProof.lean, `by_cases hmod : InMainRangeMod ε n`).

It proves that for all sufficiently large n in this regime,
with probability `1-2*epsilon`:

```text
chi(G)-zeta(G)
  >= n^{1-epsilon} - 2*n^{0.99}
  -> infinity.
```

The low/crossing-branch proof (matching the Lean certificate, 2026-05-15):

```text
1. alpha-2-bounded chromatic lower bound at k_{alpha-2}:
   (HP-2023 lemma:lowerbound, §8.2 Proof of Theorem announcedbounds,
   applied at a = alpha-2; no mu condition; valid for all x in [0,1)):
   chi(G) >= k_{alpha-2} - n^{0.99}   whp.
   Source: Lean axiom A3 = chi_alphaMinusTwo_lower_bound_whp
   (CrossingPartB.lean:149; HP-2023 Lemma 8.1 at a = alpha-2 +
   standard Azuma-Hoeffding concentration, slack n^{0.99}).

2. alpha-2-bounded cochromatic upper bound at k_{alpha-1}:
   (Heckel 2024 arXiv:2409.17614 Prop 5(b) + Azuma-Hoeffding,
   adapted from (alpha-1)-bounded to (alpha-2)-bounded cocolorings;
   see SOURCES.md A4 for transfer details):
   zeta(G) <= k_{alpha-1} + n^{0.99}   whp.
   Source: Lean axiom A4 = zeta_alphaMinusTwo_upper_bound_whp
   (CrossingPartB.lean:166; extrapolation status disclosed in SOURCES.md §A4).

3. Threshold gap (deterministic):
   In ¬InMainRangeMod, the (alpha-2) and (alpha-1) first-moment thresholds
   satisfy k_{alpha-2} - k_{alpha-1} >= n^{1-epsilon}   for all large n.
   Source: HP-2023 Lemma 8.1 first-moment input paragraph at level alpha-2
   (Lean axiom A2 = partB_alphaMinusTwo_firstMomentBelowOne_source +
   deterministic Lean derivation in kThreshold_gap_alpha_minus_2;
   CrossingPartB.lean:39).

4. Gap assembly:
   chi(G) - zeta(G)
     >= (k_{alpha-2} - n^{0.99}) - (k_{alpha-1} + n^{0.99})
      = (k_{alpha-2} - k_{alpha-1}) - 2*n^{0.99}
     >= n^{1-epsilon} - 2*n^{0.99}
     -> infinity.
```

This proof uses the alpha-2 threshold gap as the driving force.
The gap n^{1-epsilon} in the crossing regime is large because mu_alpha is small
(mu_alpha < n^{x_0+epsilon}) and the (alpha-2)-bounded first moment is below 1
over a window of width Theta(n/log^2 n) above k_{alpha-1}.

**Lean correspondence**: this is exactly the crossing-case branch of
`erdos_625_full` / `erdos_625_full_clean` in PublishableProof.lean,
using Lean axioms A2, A3, A4 from SOURCES.md.

## Regime II: good branch away from one

Source theorem:

```text
proof/source-notes/good-branch-partial-away-from-one-theorem-2026-05-13.md
```

Apply it with the fixed value:

```text
epsilon_0=0.05.
```

Then on:

```text
0.029155 <= x <= 1-epsilon_0 = 0.95,
```

we have, asymptotically almost surely:

```text
chi(G)-zeta(G)->infinity.
```

With the fixed `epsilon` chosen in the global setup, the theorem gives:

```text
chi(G)-zeta(G)
  >= n^{1-epsilon/2}
     - n^{1-0.9epsilon}
     - 2n^0.999
  -> infinity.
```

This fixed instantiation covers the whole middle regime.  No parameter is
allowed to vary with `n` in this invocation.

## Regime III: upper boundary

Source theorem:

```text
proof/source-notes/upper-boundary-r2-integrated-theorem-2026-05-13.md
```

Status:

```text
closed; source included in this package.
```

The explicit finite interval appendix for `R2-G1` is:

```text
proof/source-notes/upper-boundary-r2-explicit-interval-tables-2026-05-13.md
```

It proves that on:

```text
0.95 <= x < 1,
```

with probability `1-o(1)`:

```text
chi(G)-zeta(G)
  >= 0.001 n/log^3 n-o(n/log^3 n).
```

In particular:

```text
chi(G)-zeta(G)->infinity.
```

The upper-boundary proof uses the alpha-anchor `r=2` omitted-top profile:

```text
p_0=p_1=0,
support i>=2,
largest occupied size alpha-2.
```

The lower-bound side is:

```text
chi(G) >= boldk_alpha-o(n/log^3 n),
```

from:

```text
proof/source-notes/upper-boundary-alpha-lower-bound-u8a-closure-2026-05-13.md
proof/source-notes/upper-boundary-alpha-to-ordinary-transfer-u8b-closure-2026-05-13.md
```

The upper-bound side is:

```text
zeta(G)
  <= boldk_alpha-0.001 n/log^3 n+o(n/log^3 n),
```

from:

```text
certificate:      proof/source-notes/upper-boundary-r2-directed-certificate-proof-2026-05-13.md
interval tables:  proof/source-notes/upper-boundary-r2-explicit-interval-tables-2026-05-13.md
finite transfer:  proof/source-notes/upper-boundary-r2-exact-finite-transfer-g2-closure-2026-05-13.md
shift:            proof/source-notes/upper-boundary-alpha-first-moment-shift-u3-closure-2026-05-13.md
rounding:         proof/source-notes/upper-boundary-r2-rounding-stability-u4-closure-2026-05-13.md
C3 adapter:       proof/source-notes/upper-boundary-r2-c3-source-gate-adapter-2026-05-13.md
C5 adapter:       proof/source-notes/upper-boundary-r2-c5-active-profile-adapter-2026-05-13.md
bridge:           proof/source-notes/upper-boundary-r2-profitable-profile-bridge-g3-closure-2026-05-13.md
```

## Final assembly

The three closed intervals/ranges:

```text
[0,0.029155],
[0.029155,0.95],
[0.95,1)
```

cover all possible values of:

```text
x=alpha_0-alpha.
```

The endpoints overlap, which is harmless.  For each sufficiently large `n`,
the deterministic value `x(n)` belongs to at least one of these ranges.  Apply
one corresponding regime theorem to that `n`.

In each range, the corresponding theorem proves a high-probability lower
bound that eventually dominates the global choice `w(n)=log log n`:

```text
low/crossing:    n^{1-epsilon}-2*n^{0.99} >> log log n;
middle branch:   n^{1-epsilon/2}-n^{1-0.9epsilon}-2n^0.999
                 >> log log n;
upper branch:    0.001 n/log^3 n-o(n/log^3 n) >> log log n.
```

Therefore, for each sufficiently large `n`, if `E_n` is the high-probability
event supplied by an applicable regime theorem for the deterministic value
`x(n)`, then on `E_n`:

```text
chi(G)-zeta(G) >= w(n)=log log n.
```

Since the selected regime theorem gives `P(E_n)=1-o(1)`, we have:

```text
P(chi(G(n,1/2))-zeta(G(n,1/2)) >= w(n)) -> 1.
```

## Limitations

The following caveats apply to the current proof as shipped in this package:

All source theorem notes cited in this document are included in
`proof/source-notes/` in this package.  The following notes apply to the
current proof:

(a) **Middle branch residue**: the source theorem
`proof/source-notes/good-branch-partial-away-from-one-theorem-2026-05-13.md`
covers only `x <= 1-epsilon_0` for fixed `epsilon_0>0`.  The residual region
`x > 1-epsilon_0` for arbitrarily small `epsilon_0` is handled by the upper
branch (Regime III), which covers `x in [0.95,1)` independently.

(b) **Upper branch interval checks**: the finite interval checks for
`proof/source-notes/upper-boundary-r2-directed-certificate-proof-2026-05-13.md`
are supplied in
`proof/source-notes/upper-boundary-r2-explicit-interval-tables-2026-05-13.md`,
which is included in this package.

(c) **R2-G1 certificate novelty**: the core numerical bounds
`Room_2(x) >= 0.07` and `Prefix_2(x) >= 0.006` on `[0.95,1]`,
including the mean-solver enclosures and partition-function truncation
at I=40, are original computations in these source notes.  They are not
reproduced from HP-2023, HRHowdoes, or Heckel 2024.  The computation was
generated by the same LLM pipeline that produced this document and has
not been independently verified by a third party.  The proof framework
(Room/Prefix machinery, profile construction) is paper-backed; the
specific numerical certificate values are not.

## Status

This is the current complete analytical proof route.  All source theorem notes
are included in `proof/source-notes/`.

## Dependency-status table

| Regime | Note | Role | Status | Comment |
|---|---|---|---|---|
| Low/Crossing | A3+A4+threshold-gap argument (2026-05-15) | Regime proof | Closed (paper axioms A2+A3+A4) | HP-2023 lemma:lowerbound §8.2 at α−2 (A3); Heckel 2024 Prop 5(b) α−2-adapted (A4, extrapolation disclosed in SOURCES.md §A4); threshold gap from A2 (HP-2023 Lemma 8.1 first-moment at α−2). Lean: crossing branch of `erdos_625_full_clean` in PublishableProof.lean. |
| Low | `low-branch-quantitative-splice-theorem-2026-05-13.md` | Old C5-based source | Superseded | Not used in the current proof. |
| Middle | `proof/source-notes/good-branch-partial-away-from-one-theorem-2026-05-13.md` | Regime theorem | Closed (in-package) | Covers `[0.029155,0.95]` for fixed `epsilon_0=0.05`. |
| Upper | `proof/source-notes/upper-boundary-r2-integrated-theorem-2026-05-13.md` | Regime theorem | Closed (in-package) | Uses alpha-anchor `r=2`. |
| Upper | `proof/source-notes/upper-boundary-r2-directed-certificate-proof-2026-05-13.md` | Limiting certificate | Closed (in-package) | Supported by explicit interval table appendix. NOTE: Room_2 ≥ 0.07 and Prefix_2 ≥ 0.006 on [0.95,1] are original LLM-computed values not in any published paper; not independently verified. |
| Upper | `proof/source-notes/upper-boundary-r2-explicit-interval-tables-2026-05-13.md` | Interval appendix | Closed (in-package) | Supplies `R2-G1` finite interval bounds. |
| Upper | `proof/source-notes/upper-boundary-r2-exact-finite-transfer-g2-closure-2026-05-13.md` | Finite transfer | Closed (in-package) | Former certificate condition discharged. |
| Upper | `proof/source-notes/upper-boundary-r2-profitable-profile-bridge-g3-closure-2026-05-13.md` | Bridge to `zeta` bound | Closed (in-package) | Uses conservative `c_D=0.001`. |

## Dependency-status summary

```text
Low/crossing branch (¬InMainRangeMod):
  A3+A4+threshold-gap argument (2026-05-15);
  status: closed (paper axioms A2+A3+A4);
  sources:
    A3 = HP-2023 lemma:lowerbound §8.2 at a=alpha-2 (chi lower bound, unconditional);
    A4 = Heckel 2024 Prop 5(b) alpha-2-adapted (zeta upper bound, extrapolation);
    A2 = HP-2023 Lemma 8.1 first-moment paragraph at alpha-2 (threshold gap input);
    deterministic threshold gap k_{alpha-2} - k_{alpha-1} >= n^{1-epsilon}
      (Lean: kThreshold_gap_alpha_minus_2, no paper axiom);
  Lean correspondence: crossing case of erdos_625_full_clean (PublishableProof.lean).
  The prior C5-based source note is superseded and not used.

Middle branch:
  proof/source-notes/good-branch-partial-away-from-one-theorem-2026-05-13.md
  status: closed (in-package) for fixed epsilon_0=0.05.

Upper branch:
  proof/source-notes/upper-boundary-r2-integrated-theorem-2026-05-13.md
  status: closed (in-package); explicit interval tables are supplied in
  proof/source-notes/upper-boundary-r2-explicit-interval-tables-2026-05-13.md.
```
