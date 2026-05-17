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

### Note on the AnalyticalWrapper (parallel route)

Note on the AnalyticalWrapper: the file Erdos625/AnalyticalWrapper.lean contains
a parallel analytical route using a DIFFERENT argument for Regime I
(first-moment/Markov cochromatic upper bound, not A2+A3+A4), which is NOT what
this document describes. This document describes the PROVED route
(erdos_625_full_clean, A1–A4). The AnalyticalWrapper exposes two theorems:

- `erdos_625_full_analytical_of_source_obligations`: NOT Lean-certified (three
  bridge-shaped WHP obligations remain in its dependency chain). Axiom snapshot:
  `proof/ANALYTICAL_WRAPPER_AXIOM_SNAPSHOT.txt`.
- `erdos625_low_discharged` (added 2026-05-17): Lean-certified modulo four
  paper-cited axioms (all three bridge obligations replaced). The Lean/source
  boundary notes that the middle source artifact covers only x <= 1-epsilon_0
  for fixed epsilon_0 > 0 (residual region x > 1-epsilon_0 handled by the upper
  branch), and that the upper source artifact uses explicit directed interval
  tables supplied in
  `proof/source-notes/upper-boundary-r2-explicit-interval-tables-2026-05-13.md`.

Date: 2026-05-15 (updated 2026-05-16, updated 2026-05-17)

**Update 2026-05-16**: In the AnalyticalWrapper parallel route, `lowBranchFirstMomentGapAxiom`
was promoted from an axiom to a proved theorem, derived from the new axiom
`lowBranchGapWHPAxiom`. The auxiliary theorem `expectedColorings_tendsto_zero_below_kThreshold`
was also proved (E[X_{kThresh - ⌊n/log²n⌋}] → 0, from `oneMoreColourAxiom_low` in Lean).

**Update 2026-05-17** (supersedes 2026-05-16 wrapper state): The new theorem
`erdos625_low_discharged` was added to `Erdos625/AnalyticalWrapper.lean`. It proves the
same top-level statement as `erdos_625_full_analytical_of_source_obligations` but with
a strictly better axiom chain: all three bridge-shaped WHP obligations are replaced by
paper-cited axioms.

The four paper-cited axiom leaves of `erdos625_low_discharged` are (non-kernel
leaves only; the theorem also inherits the three standard Lean kernel axioms
`propext`, `Classical.choice`, `Quot.sound`, plus any non-kernel axioms present
in the dependency chains of `ChromaticConnection.lean` and `ZetaConcentration.lean`
— see `proof/ANALYTICAL_WRAPPER_AXIOM_SNAPSHOT.txt` for the complete `#print axioms`
list, including the `<+ existing axioms>` residual):
- `paperLowBranchChiLower_source`: HP-2023 Lemma 8.1 (chromatic lower bound, unconditional)
- `paperLowBranchZetaUpper_source`: HP-2023 Co. 39 + Le. 7.4 + Heckel 2024 lines 514–516
  + Markov (first-moment/Markov cochromatic upper bound; does NOT use C5 second-moment,
  which is inapplicable for x < x₀ ≈ 0.029155; regime-unconditional)
- `middleBranchCrossingComplementWHPAxiom`: HP-2023 §7+§8, Heckel 2024 §3–7
- `upperBranchPaperWHPAxiom`: HP-2023 Theorem 1 + §4 Lemma 4.1 + §7 + Appendix;
  Heckel–Riordan 2023 Lemma 44

The wiring theorem `lowBranchWHP_of_paper_axioms` (proved, ~60 lines) derives
`LowBranchConcreteSourceObligation` from the two low-branch paper axioms via
`gnHalf_whp_inter` and a subset argument using `lowBranchConservativeGapLowerPub`
(proved by `ring`). `lowBranchGapWHPAxiom` remains declared in AnalyticalWrapper.lean
but is no longer a leaf of `erdos625_low_discharged`.

**Note on the C5/Heckel review**: The 2026-05-16 disclosure about a C5 second-moment
concern (E[X²]/E[X]² = O(1)) under review by Dr. Heckel applied to `lowBranchGapWHPAxiom`.
That concern is irrelevant to `erdos625_low_discharged`, whose cochromatic upper bound
uses the first-moment/Markov route (not C5). The letter and analysis in
`proof/source-notes/reply-to-heckel-2026-05-16.md` and
`proof/source-notes/heckel-question-k-alpha-1-vs-k-alpha-2-answer-2026-05-16.md`
remain in the package as context; they do not represent an open gap in the current proof.
C5 (second-moment) continues to be used in Regime III (upper branch, x in [0.95,1));
the resolved concern applied only to the former low-branch C5 application (x < 0.029155),
which is now replaced by the first-moment/Markov route.

See `proof/ANALYTICAL_WRAPPER_AXIOM_SNAPSHOT.txt` for the full axiom snapshot
of both theorems.

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
Iterated logarithm: `log log n` means `log_2(log_2(n))` throughout this document.

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

The threshold x_0 is defined by HP-2023 equation (7.19) as the unique solution
to phi(1, x_0, 1) = 0 in (0,1); numerically x_0 ≈ 0.029155.
InMainRangeMod holds when mu_alpha(n) >= n^{x_0+epsilon}.
The complement ¬InMainRangeMod (Regime I) is the set of n with
mu_alpha(n) < n^{x_0+epsilon}, equivalently x < x_0 ≈ 0.029155.

The first-moment thresholds are:

```text
k_j = min{k : E[X^{(j)}_k] <= 1},
```

where X^{(j)}_k counts j-bounded k-colorings of G(n,1/2).
In particular k_{alpha-2} and k_{alpha-1} are the thresholds at levels alpha-2
and alpha-1 respectively. The quantity boldk_alpha used in Regime III equals
k_{alpha-1} in the notation of HP-2023 §7.
See CrossingPartB.lean (A2) and HP-2023 §8 for definitions.

InMainRangeMod is the Lean predicate (Erdos625/Defs.lean) corresponding to the
condition mu_alpha(n) >= n^{x_0+epsilon} from HP-2023 §7.
mu_alpha(n) denotes the expected number of proper alpha-colorings of G(n,1/2).
See HP-2023 §7 and the Lean definition in Erdos625/Defs.lean.

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
NOT InMainRangeMod: mu_alpha(n) < n^{x_0+epsilon} (equivalently x < x_0 ≈ 0.029155).
```

Equivalently, this is the "crossing" residue — approximately the 3% of n not covered
by InMainRangeMod — which includes all n with x ≤ 0.029155.

This is also the case handled by the Lean `erdos_625_full_clean` crossing branch
(PublishableProof.lean, `by_cases hmod : InMainRangeMod ε n`).

It proves that for all sufficiently large n in this regime,
with probability `1-2*epsilon`:

```text
chi(G)-zeta(G)
  >= n^{1-2*epsilon}
  -> infinity.
```

(The parent theorem `erdos_625_full` produces the intermediate bound
`n^{1-epsilon} - 2*n^{0.99}`; `erdos_625_full_clean` wraps this via
the asymptotic inequality `n^{1-2*epsilon} <= n^{1-epsilon} - 2*n^{0.99}`
(eventually in n) to yield the cleaner `n^{1-2*epsilon}` form.)

The low/crossing-branch proof (matching the Lean certificate, 2026-05-15):

```text
1. alpha-2-bounded chromatic lower bound at k_{alpha-2}:
   (HP-2023 Lemma 8.1, applied at a = alpha-2;
   no mu condition; valid for all x in [0,1)):
   chi(G) >= k_{alpha-2} - n^{0.99}   whp.
   Source: Lean axiom A3 = chi_alphaMinusTwo_lower_bound_whp
   (CrossingPartB.lean:251; HP-2023 Lemma 8.1 at a = alpha-2 +
   standard Azuma-Hoeffding concentration, slack n^{0.99}).

2. alpha-2-bounded cochromatic upper bound at k_{alpha-1}:
   (Heckel 2024 arXiv:2409.17614 Prop 5(b) + Azuma-Hoeffding,
   adapted from (alpha-1)-bounded to (alpha-2)-bounded cocolorings;
   see SOURCES.md A4 for transfer details):
   zeta(G) <= k_{alpha-1} + n^{0.99}   whp.
   Source: Lean axiom A4 = zeta_alphaMinusTwo_upper_bound_whp
   (CrossingPartB.lean:293; extrapolation status disclosed in SOURCES.md §A4).

3. Threshold gap (two-step):
   Step 3a (paper axiom A2): In the regime mu_alpha(n) < n^{x_0+epsilon} (¬InMainRangeMod), Lean axiom A2
   (partB_alphaMinusTwo_firstMomentBelowOne_source, CrossingPartB.lean:39,
   sourced from HP-2023 Lemma 8.1 first-moment paragraph at level alpha-2)
   gives the gap k_{alpha-2} - k_{alpha-1} >= n/log²n.
   A2 contributes ONLY the n/log²n bound; the paper does not claim n^{1-epsilon}.
   Step 3b (real-analytic promotion, no paper axiom): The Lean-proved lemma
   kThreshold_gap_alpha_minus_2 (CrossingWindowProof.lean:68) uses the
   real-analytic comparison n/log²n >= n^{1-epsilon} (equivalently,
   log²n = o(n^epsilon) for any epsilon > 0), which holds for all large n.
   This promotion step is a pure real-analysis fact, proved entirely within Lean;
   it does not rely on HP-2023 or any other paper.
   Combined: k_{alpha-2} - k_{alpha-1} >= n^{1-epsilon}   for all large n.

4. Gap assembly:
   Let E_A3 be the event that chi(G) >= k_{alpha-2} - n^{0.99} (from A3, holds
   with probability >= 1-epsilon) and E_A4 be the event that
   zeta(G) <= k_{alpha-1} + n^{0.99} (from A4, holds with probability >= 1-epsilon).
   By the union bound, P(E_A3 ∩ E_A4) >= 1-2epsilon.  On the event E_A3 ∩ E_A4:
   chi(G) - zeta(G)
     >= (k_{alpha-2} - n^{0.99}) - (k_{alpha-1} + n^{0.99})
      = (k_{alpha-2} - k_{alpha-1}) - 2*n^{0.99}
     >= n^{1-epsilon} - 2*n^{0.99}
     -> infinity.
   This event E_n = E_A3 ∩ E_A4 satisfies P(E_n) >= 1-2epsilon; the
   intermediate bound `n^{1-epsilon} - 2*n^{0.99}` is proved by `erdos_625_full`,
   and `erdos_625_full_clean` further tightens this to `n^{1-2*epsilon}` using
   the asymptotic inequality `n^{1-2*epsilon} <= n^{1-epsilon} - 2*n^{0.99}`.
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

**Disclosure**: The original HP-2023 Lemma 7.20 requires mu_alpha >= n^{1.05}.
Since mu_alpha = n^{x+o(1)} and x < 1 throughout this regime, the original condition
is NEVER satisfied for any n in Regime II.  This regime therefore does not invoke
HP-2023 Lemma 7.20 directly; instead it invokes the HYBRID weakening
`lemma_7_20_modified` (Lean axiom A1), which is conjectured in Heckel 2024 §Discussion
and supported by an in-repository A1 numerical certificate for x in [0.029155, 0.04),
but is NOT a proved theorem in any published paper.  See SOURCES.md §A1 and the
top-level status block for the HYBRID label and certificate details.

Apply it with the fixed value:

```text
epsilon_0=0.05.
```

Here epsilon_0 = 0.05 is the middle-regime parameter from the source theorem;
epsilon < 1/450 is the global fixed parameter from §Global setup.
These are independent. In particular, epsilon < 1/450 < epsilon_0/2 = 0.025,
confirming the global epsilon satisfies both the Lean constraint (epsilon < 1/450)
and the source theorem constraint (epsilon < epsilon_0/2).

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

> **CAUTION — unverified numerical certificate**: The gap bound in this regime
> (chi(G) - zeta(G) >= 0.001 n/log^3 n) depends on the R2-G1 numerical certificate
> Room_2(x) >= 0.07 and Prefix_2(x) >= 0.006 on [0.95,1].  These values were
> generated by the same LLM pipeline that produced this document and have NOT been
> independently verified by a third party or by certified interval arithmetic.  The
> proof framework (Room/Prefix machinery, profile construction) is paper-backed;
> the specific certificate values are not.  Regime III is therefore contingent on
> this unverified certificate.  Closure in the standard mathematical sense requires
> independent recomputation or peer review of the interval tables (see §Limitations
> (c) and §Dependency-status table).

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

**Event intersection (union bound)**: Let E_chi be the event that
chi(G) >= boldk_alpha - o(n/log^3 n), and E_zeta be the event that
zeta(G) <= boldk_alpha - 0.001 n/log^3 n + o(n/log^3 n).  Each event holds with
probability 1-o(1) (from the respective source notes above).  Therefore
P(E_chi^c) = o(1) and P(E_zeta^c) = o(1), so by the union bound:

```text
P(E_chi ∩ E_zeta)
  = 1 - P(E_chi^c ∪ E_zeta^c)
  >= 1 - P(E_chi^c) - P(E_zeta^c)
  = 1 - o(1).
```

On the event E_chi ∩ E_zeta, which holds with probability 1-o(1):

```text
chi(G) - zeta(G)
  >= (boldk_alpha - o(n/log^3 n)) - (boldk_alpha - 0.001 n/log^3 n + o(n/log^3 n))
   = 0.001 n/log^3 n - o(n/log^3 n).
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
low/crossing:    n^{1-2*epsilon} >> log log n
                   (proved form; intermediate n^{1-epsilon}-2*n^{0.99} >> log log n
                    also holds and implies the clean form);
middle branch:   n^{1-epsilon/2}-n^{1-0.9epsilon}-2n^0.999
                 >> log log n;
upper branch:    0.001 n/log^3 n-o(n/log^3 n) >> log log n.
```

Asymptotic justification:
- Regime I: For epsilon < 0.01, n^{1-epsilon} - 2n^{0.99} = n^{0.99}(n^{0.01-epsilon}-2)
  → ∞, since n^{0.01-epsilon} → ∞ when epsilon < 0.01.  As n^{0.99} >> log log n,
  the full expression dominates log log n.
- Regime III: 0.001 n/log^3 n / log log n = 0.001 n / (log^3 n · log log n) → ∞
  because n grows faster than any power of log n.

Therefore, for each sufficiently large `n`, if `E_n` is the high-probability
event supplied by an applicable regime theorem for the deterministic value
`x(n)`, then on `E_n`:

```text
chi(G)-zeta(G) >= w(n)=log log n.
```

The probability bound type differs by regime: for Regime I, the Lean theorem
`erdos_625_full_clean` provides a quantitative finite-n bound P(E_n) >= 1-2epsilon
(for every fixed epsilon > 0 and all sufficiently large n); for Regimes II and III,
the source theorems give the asymptotic bound P(E_n) = 1-o(1) (no finite-n
quantitative constant).  In all three cases P(E_n) → 1.

Since in each case P(E_n) → 1, we have:

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

## Overall proof status

This is the current complete analytical proof route.  All source theorem notes
are included in `proof/source-notes/`.  (See also the top-level status block
in the preamble above for regime-level disclosure labels.)

## Dependency-status table

| Regime | Note | Role | Status | Comment |
|---|---|---|---|---|
| Low/Crossing | A3+A4+threshold-gap argument (2026-05-15) | Regime proof | Closed (paper axioms A2+A3+A4) | HP-2023 lemma:lowerbound §8.2 at alpha-2 (A3); Heckel 2024 Prop 5(b) alpha-2-adapted (A4): A4 is supported by an in-package analytical transfer argument (`proof/source-notes/alpha-minus-two-cochromatic-transfer-proof-2026-05-13.md`) but remains a Lean `axiom` (not a Lean-proved theorem); the paper axiom count is 4. See SOURCES.md §A4 for full transfer audit; threshold gap from A2 (HP-2023 Lemma 8.1 first-moment at alpha-2). Lean: crossing branch of `erdos_625_full_clean` in PublishableProof.lean. |
| Low | `low-branch-quantitative-splice-theorem-2026-05-13.md` | Old C5-based source | Superseded | Not used in the current proof. |
| Middle | `proof/source-notes/good-branch-partial-away-from-one-theorem-2026-05-13.md` | Regime theorem | Closed (in-package) | Covers `[0.029155,0.95]` for fixed `epsilon_0=0.05`. |
| Upper | `proof/source-notes/upper-boundary-r2-integrated-theorem-2026-05-13.md` | Regime theorem | Closed (in-package) | Uses alpha-anchor `r=2`. |
| Upper | `proof/source-notes/upper-boundary-r2-directed-certificate-proof-2026-05-13.md` | Limiting certificate | Closed (in-package) | Supported by explicit interval table appendix. NOTE: Room_2 >= 0.07 and Prefix_2 >= 0.006 on [0.95,1] are original LLM-computed values not in any published paper; not independently verified. |
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
      A4 has an in-package analytical transfer argument supporting it but remains a
      Lean axiom (not Lean-proved); the paper axiom count is 4 (unchanged);
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
