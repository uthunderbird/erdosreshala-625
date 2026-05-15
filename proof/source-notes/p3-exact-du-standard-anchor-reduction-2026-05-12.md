# P3 exact-`d_u` standard-anchor reduction

Date: 2026-05-12

## Purpose

This note narrows the exact-`d_u` certificate problem to the version needed
by the standard prize route.

Earlier certificate notes allowed a general shifted anchor interval.  After
the `alpha_0` floor asymptotic and endpoint split, the proof no longer
needs arbitrary recursive shifted anchors for the standard choice

```text
alpha=floor(alpha_0).
```

The active endpoint proof uses:

```text
anchor a = alpha-1,
truncation r in {2,3}.
```

## Reduction

At the residual endpoint, split by:

```text
N_scr=n log^4 n.
```

If:

```text
mu_{alpha-2} >> N_scr,
```

use the `r=2` omitted-top profile at anchor `a=alpha-1`.

Otherwise:

```text
mu_{alpha-2} <= N_scr.
```

The Stirling/ratio lemma gives:

```text
mu_{alpha-3} >> N_scr,
```

so use the `r=3` omitted-top profile at the same anchor `a=alpha-1`.

Thus no endpoint branch requires shifting the lower-bound anchor from
`alpha-1` to `alpha-2`.

## Certificate consequence

The proof-grade exact-`d_u` certificate only needs to certify:

```text
Room^{(2)}(x)>0 and Prefix^{(2)}(x)>0,
Room^{(3)}(x)>0 and Prefix^{(3)}(x)>0,
x in [0,x0].
```

The exact finite centered objective should be evaluated at the local
standard anchor corresponding to `alpha-1`.  Since the certificate is an
asymptotic deficit-coordinate certificate, the final proof may express it
as a uniform-in-large-anchor statement:

```text
For all A>=A0 and x in [0,x0], the exact centered objective has
positive room and prefix margins for r=2,3.
```

This is stronger and cleaner than certifying a finite interval such as
`A in [30,40]`.  The exploratory scans at `A=30,40` are evidence for the
large-anchor stability, but not proof.

## Preferred final certificate theorem

A final theorem should state:

There exist constants

```text
A0,
R2,R3>0,
c2_delta,c3_delta>0
```

such that for every real/integer anchor parameter `A>=A0`, every
`x in [0,x0]`, and `r in {2,3}`, the exact centered finite-`d_u` profile
`p_A^{(r)}(x)` satisfies:

```text
Room_A^{(r)}(x) >= R_r,
Phi_x(q) >= c_{r,delta}
```

for all certified prefix subprofiles with mass in `[delta,1-delta]`.

## Implementation consequence

The interval generator should support two stages:

```text
Stage 1: fixed large integer A rows, to reproduce the exploratory margins
         with directed arithmetic.
Stage 2: monotonic/stability envelope in A>=A0, or a finite-A tail bound
         proving the fixed-A certificate transfers to all larger anchors.
```

Stage 1 alone does not close G4.  Stage 2 is the remaining mathematical
content that turns finite scans into an asymptotic proof.

The large-anchor expansion needed for Stage 2 is recorded in:

```text
exact-du-large-anchor-expansion-2026-05-12.md
```

## Status

This reduction removes unnecessary recursive-anchor scope from the standard
route.  It exposes the real remaining exact-`d_u` burden:

```text
prove large-anchor stability of the r=2,3 exact centered objective
and prefix margins.
```
