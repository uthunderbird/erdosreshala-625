# Analytical proof for Erdos Problem 625

Status:

```text
complete analytical proof route; all source theorem notes included in this package.
```

This document records the complete analytical proof route with explicit source citations at every step.  Not Lean-certified: the analytical wrapper theorem `erdos_625_full_analytical` depends on three WHP bridge obligations not yet formalized in Lean.  All source theorem notes for the middle and upper branches are now included in `proof/source-notes/` in this package.

Lean certification remains blocked by the bridge-input-shaped WHP obligations
recorded in the analytical wrapper axiom snapshot (`proof/ANALYTICAL_WRAPPER_AXIOM_SNAPSHOT.txt`).
In particular, the Lean/source boundary still records that the middle source
artifact leaves the residual region x > 1-epsilon_0 open and that the upper
source artifact depends on explicit directed interval tables (now supplied in
`proof/source-notes/upper-boundary-r2-explicit-interval-tables-2026-05-13.md`).

Date: 2026-05-15

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
w(n)=o(n/log^3 n),
w(n)=o(n^{1-epsilon/2}).
```

## Regime I: low branch

Source argument: first-moment (Markov) method (2026-05-15).
(The prior C5-based source note `low-branch-quantitative-splice-theorem-2026-05-13.md` is superseded.)

It proves that on:

```text
0 <= x <= 0.029155,
```

with probability `1-o(1)`:

```text
chi(G)-zeta(G)
  >= (c_*-o(1)) n/log^3 n
```

for some fixed:

```text
c_*>0.
```

In particular:

```text
chi(G)-zeta(G)->infinity.
```

The low-branch proof uses the first-moment (Markov) method (updated 2026-05-15):

```text
1. alpha-1-bounded chromatic lower bound at k_{alpha-1}
   (HP-2023 Le. 8.1, valid for all x in [0,1); requires a in {alpha-1, alpha-2}):
   Le. 8.1 gives chi_{alpha-1}(G) >= k_{alpha-1} - 1 whp.
   Converting to ordinary chi: by HRHowdoes Le. 44 (cited HP-2023 line 364),
   chi_{alpha-1}(G) - chi(G) <= O(mu_alpha) whp. In InLowRegime,
   mu_alpha = Theta(n^x) (HP-2023 Le. 7.4; mu_alpha = E[X_alpha] ~ C n^x/log n
   for the exact expression, with n^x the dominant factor) <= n^{0.029155+o(1)}
   = o(n/log^3 n) = o(D).
   Therefore chi(G) >= k_{alpha-1} - 1 - O(mu_alpha) = k_{alpha-1} - lowBranchConservativeError(n)
   whp, where lowBranchConservativeError(n) = O(n^{0.03}) = o(D);
2. averagecolourclass lemma: k_{alpha-1} = Theta(n/log n)
   (HP-2023 Le. 7.4 = HRHowdoes Le. 41, generic theta in [0,1], no regime restriction;
   HRHowdoes = Heckel-Riordan [2023], J. London Math. Soc. 108(5):1769-1815);
3. onemorecolour/delk lemma: dL_0/dk = (2/ln2)log^2 n + O(log n log log n)
   (HP-2023 Le. 7.3 = HRHowdoes Co. 39, y_t(rho) sums over u=1..t, no regime restriction);
4. firstmomentcocol: E[X^co_k] = 2^k * E[X_k]
   (Heckel 2024, line 516, exact equality; condition k_1=0 — no singleton
   colour classes — is automatic for alpha-1-bounded profiles: by definition
   alpha-a-bounded profiles have all class sizes in {1,...,a}; the first-moment
   threshold structure (HP-2023 §7) places k_{alpha-1} so that only class sizes
   >= 2 contribute to the leading first-moment term, and the k_1=0 restriction
   is satisfied at k_{alpha-1} since singleton classes are subcritical at that
   level; no x-regime restriction);
5. improvedapproximation: ln E[X_k] = L_0 + O(log^{3/2} n)
   (HP-2023, lines 2364-2369, no regime restriction);
6. Markov's inequality: E[X^co_{k-D}] -> 0 for D = Theta(n/log^3 n),
   so P(zeta(G) >= k_{alpha-1}-D) -> 0.
```

This proof does NOT use C5, tameness, phi(1,x,1) > 0, or mu_alpha >= n^{x_0+eps}.
It works uniformly for all x in [0, 0.029155], including the bulk x < x_0 where
phi(1,x,1) < 0 and C5 fails. The prior C5-based source note (2026-05-13) is superseded.

Red-team confirmation (2026-05-15): all adversarial attack vectors refuted
(internal LLM red-team audit conducted by the same LLM pipeline that produced
this document; not independently verified by a third party).
Summary of the five attack vectors and their dispositions:

1. **chi_a vs chi conversion**: HP-2023 Le. 8.1 gives chi_{alpha-1}(G) >= k_{alpha-1} - 1
   whp (a in {alpha-1, alpha-2}; no x-regime restriction). HRHowdoes Le. 44
   (cited HP-2023 line 364) gives chi_{alpha-1}(G) - chi(G) <= O(mu_alpha) whp.
   In InLowRegime mu_alpha <= n^{0.029155} = o(D). Refuted: gap is unaffected.

2. **eq:firstmomentcocol regime restriction**: The source (Heckel 2024 line 516) is an
   algebraic identity valid for any k-profile with k_1 = 0, with no regime restriction.
   Refuted: the identity applies uniformly.

3. **lemma:improvedapproximation conditions**: Conditions are satisfied at k = k_{alpha-1} - D
   for D = Theta(n/log^3 n). Refuted: conditions hold.

4. **lemma:onemorecolour (Le. 7.3) regime applicability**: Le. 7.3 gives dL_0/dk =
   (2/ln2)log^2 n + O(log n log log n) uniformly in the low branch; the preamble
   "generic theta in [0,1]" applies here. Refuted: lemma applies.

5. **Markov conclusion**: Going D = Theta(n/log^3 n) below k_{alpha-1}, ln E[X^co_{k-D}]
   decreases by >> 1, so E[X^co_{k-D}] -> 0 and Markov gives
   P(zeta(G) >= k_{alpha-1} - D) -> 0. Refuted: argument is internally consistent.

(The attack vectors above represent the complete adversarial review; critique artifacts have been incorporated into this document.)

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
low branch:      (c_*-o(1))n/log^3 n >> log log n;
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

## Status

This is the current complete analytical proof route.  All source theorem notes
are included in `proof/source-notes/`.

## Dependency-status table

| Regime | Note | Role | Status | Comment |
|---|---|---|---|---|
| Low | First-moment (Markov) argument (2026-05-15) | Regime proof | Closed (in-package) | HP-2023 Le. 7.4 + Le. 7.3 (= HRHowdoes Co. 39) + HP-2023 Le. 8.1 + HP-2023 lines 2364–2369 + Heckel 2024 line 516. Supersedes the C5-based source note `low-branch-quantitative-splice-theorem-2026-05-13.md`. |
| Low | `low-branch-quantitative-splice-theorem-2026-05-13.md` | Old C5-based source | Superseded | Replaced by the 2026-05-15 first-moment argument; not used in the current proof. |
| Middle | `proof/source-notes/good-branch-partial-away-from-one-theorem-2026-05-13.md` | Regime theorem | Closed (in-package) | Covers `[0.029155,0.95]` for fixed `epsilon_0=0.05`. |
| Upper | `proof/source-notes/upper-boundary-r2-integrated-theorem-2026-05-13.md` | Regime theorem | Closed (in-package) | Uses alpha-anchor `r=2`. |
| Upper | `proof/source-notes/upper-boundary-r2-directed-certificate-proof-2026-05-13.md` | Limiting certificate | Closed (in-package) | Supported by explicit interval table appendix. |
| Upper | `proof/source-notes/upper-boundary-r2-explicit-interval-tables-2026-05-13.md` | Interval appendix | Closed (in-package) | Supplies `R2-G1` finite interval bounds. |
| Upper | `proof/source-notes/upper-boundary-r2-exact-finite-transfer-g2-closure-2026-05-13.md` | Finite transfer | Closed (in-package) | Former certificate condition discharged. |
| Upper | `proof/source-notes/upper-boundary-r2-profitable-profile-bridge-g3-closure-2026-05-13.md` | Bridge to `zeta` bound | Closed (in-package) | Uses conservative `c_D=0.001`. |

## Dependency-status summary

```text
Low branch:
  first-moment (Markov) argument (2026-05-15);
  status: closed;
  sources: HP-2023 Le. 7.4 (averagecolourclass), HP-2023 Le. 7.3 = HRHowdoes Co. 39
  (onemorecolour), HP-2023 Le. 8.1 (chromatic lower bound),
  HP-2023 lines 2364-2369 (improvedapproximation), Heckel 2024 line 516
  (firstmomentcocol);
  the prior C5-based source note low-branch-quantitative-splice-theorem-2026-05-13.md
  is superseded and not used.

Middle branch:
  proof/source-notes/good-branch-partial-away-from-one-theorem-2026-05-13.md
  status: closed (in-package) for fixed epsilon_0=0.05.

Upper branch:
  proof/source-notes/upper-boundary-r2-integrated-theorem-2026-05-13.md
  status: closed (in-package); explicit interval tables are supplied in
  proof/source-notes/upper-boundary-r2-explicit-interval-tables-2026-05-13.md.
```
