# Upper-boundary r=2 remaining gates checklist

Date: 2026-05-13

## Purpose

This note records the current reduced state of the upper-boundary `r=2`
route after closing the lower-bound side and the source/rounding/second-moment
adapters.

## Closed or conditionally closed nodes

### Lower-bound side

Closed:

```text
upper-boundary-alpha-lower-bound-u8a-closure-2026-05-13.md
upper-boundary-alpha-to-ordinary-transfer-u8b-closure-2026-05-13.md
```

Output:

```text
chi(G) >= boldk_alpha-o(n/log^3 n)
```

whp on the upper-boundary interval.

### First-moment shift

Closed:

```text
upper-boundary-alpha-first-moment-shift-u3-closure-2026-05-13.md
```

Output:

```text
L_0(n,K,alpha)-L_0(n,K-D,alpha)
  = (2/log 2+o(1))D log^2 n
```

for:

```text
K=boldk_alpha,
D=O(n/log^3 n).
```

### Rounding stability

Conditionally closed:

```text
upper-boundary-r2-rounding-stability-u4-closure-2026-05-13.md
```

Dependency:

```text
R2-U1/R2-U2 must supply an exact finite Gaussian-tail profile with positive
room and prefix margins.
```

### C3 source gate

Conditionally closed:

```text
upper-boundary-r2-c3-source-gate-adapter-2026-05-13.md
```

Dependency:

```text
R2-U1/R2-U2/R2-U4 must supply tail/relevance and lower-boundbeta/prefix.
```

### C5 active second moment

Conditionally closed:

```text
upper-boundary-r2-c5-active-profile-adapter-2026-05-13.md
```

The active scale is:

```text
mu_{alpha-2}=mu_alpha*Theta((n/log n)^2)>>n log^4 n
```

on:

```text
x in [0.95,1).
```

Thus there is no remaining scrambled-scale obstruction for `r=2`.

## Remaining critical gates

### R2-G1: proof-grade interval certificate

Prove the limiting alpha-anchor `r=2` certificate:

```text
Room_2(x) >= 0.07,
Prefix_2(x) >= 0.006
```

uniformly for:

```text
x in [0.95,1].
```

Current evidence is only floating-point exploratory scan:

```text
room ~= 0.07518,
prefix ~= 0.00670.
```

Needed proof-grade work:

```text
1. interval arithmetic or analytic monotonicity on [0.95,1];
2. rigorous tail truncation for the infinite Gibbs sums;
3. endpoint/subdivision control for the prefix functional.
```

Room monotonicity is reduced in:

```text
upper-boundary-r2-room-monotonicity-certificate-2026-05-13.md
```

so the room side now needs only the endpoint directed-interval check
`Room_2(1)>0.07`.  The prefix side remains the harder interval certificate.

Prefix guard reduction:

```text
upper-boundary-r2-prefix-guard-reduction-2026-05-13.md
```

This identifies the tight prefix endpoint as the explicit guard mass
`0.01 e_2`, with value about `0.006708` at `x=0.95`; the moving cumulative
endpoints have much larger exploratory slack.

Directed interval checker specification:

```text
upper-boundary-r2-directed-interval-certificate-spec-2026-05-13.md
```

This is the exact next artifact needed to turn `R2-G1` from a target into a
closed certificate.

Numeric checker result:

```text
upper-boundary-r2-numeric-certificate-check-result-2026-05-13.md
```

All numeric targets pass, but the result is explicitly not yet a
proof-grade directed interval certificate.

Analytical certificate closure:

```text
upper-boundary-r2-directed-certificate-proof-2026-05-13.md
```

This closes `R2-G1` at ordinary analytical-proof standard, with the finite
decimal interval checks isolated for a publication appendix.

### R2-G2: exact finite alpha-anchor transfer

Adapt the large-anchor exact finite transfer from the previous G4/P3
pipeline to:

```text
anchor alpha,
support i>=2.
```

It must export:

```text
1. exact finite normalization/identity package;
2. finite room margin after transfer;
3. finite prefix/lower-boundbeta margin after transfer;
4. Gaussian tail/relevance;
5. profile coordinate bound k_u=O(n/log n);
6. compatibility with rounding and C3/C5 adapters.
```

The expected source reuse is:

```text
exact-du-large-anchor-expansion-2026-05-12.md
exact-du-large-anchor-compactness-lemmas-2026-05-12.md
g4-finite-transfer-publication-closure-2026-05-12.md
p3-exact-finite-normalization-bridge-theorem-2026-05-13.md
```

New boundary checks:

```text
1. anchor shifted from alpha-1 to alpha;
2. support starts at i=2;
3. missing i=0 and i=1 masses create no hidden normalization term;
4. the finite mean target matches T_alpha(x).
```

Closure:

```text
upper-boundary-r2-exact-finite-transfer-g2-closure-2026-05-13.md
```

This closes `R2-G2` conditional on the limiting certificate `R2-G1`; the
large-anchor compactness and normalization identities are anchor-agnostic.

### R2-G3: profitable-profile bridge

Once R2-G1 and R2-G2 are proved, choose `c_D>0` small enough that:

```text
finite room - shift cost - rounding/transfer losses >= c_FM > 0,
finite prefix after rounding >= c_prefix > 0.
```

Then the rounded profile has:

```text
|bf{k}^{up,2}| <= boldk_alpha-c_D n/log^3 n+o(n/log^3 n),
E[Z^co] >= exp(c_FM n/log n).
```

This bridge should be mostly bookkeeping after R2-G1/R2-G2, because
`U3` is already closed.

Closure:

```text
upper-boundary-r2-profitable-profile-bridge-g3-closure-2026-05-13.md
```

This closes `R2-G3` conditional on `R2-G1`, with a conservative saving
constant `c_D=0.001`.

## Current reduced blocker

The route is now reduced to certificate and final bridge analysis:

```text
R2-G1.
```

There is no remaining known lower-bound, C3-source, C5-source, scrambled
scale, or rounding-stability blocker outside those gates.

## Status

The full prize-candidate proof is still not complete.

Do not run final `$swarm-iterate` yet.  The next proof-producing step should
be either:

```text
1. build the proof-grade interval certificate for R2-G1; or
2. prove the exact finite alpha-anchor transfer R2-G2.
```
