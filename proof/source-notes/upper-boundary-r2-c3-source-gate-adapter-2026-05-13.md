# Upper-boundary r=2 C3 source-gate adapter

Date: 2026-05-13

## Purpose

This note adapts the standalone C3 first-moment preservation lemma to the
upper-boundary alpha-anchor `r=2` route.

It closes `R2-U5` conditionally on the rounded profile produced by
`R2-U1/R2-U2/R2-U4`.

## Existing C3 source package

The available C3 lemma is:

```text
r4-c3-first-moment-preservation-full-lemma-2026-05-12.md
```

The accepted active-profile source-gate instantiation is:

```text
p3-c3-source-gate-instantiation-2026-05-13.md
```

with evidence:

```text
c5-source-gate-closure-summary-2026-05-12.md
r4-c5-source-table-2026-05-12.md
```

The source table records the fixed-partition `B/C/D` bad-event bounds as:

```text
OK-C3.
```

## Interface required by C3

The C3 proof uses only the following profile interface:

```text
1. total number of parts Theta(n/log n);
2. all occupied sizes in the active window alpha-i with i=O(sqrt(log n));
3. Gaussian tail/relevance hypotheses;
4. lower-boundbeta or equivalent prefix positivity;
5. fixed-partition B/C/D estimates from the closed source gate;
6. complement symmetry for the clique side in G(n,1/2).
```

It does not depend on the historical P3 anchor after these fields are
available.

## Upper-boundary r=2 verification

For the alpha-anchor `r=2` rounded profile:

```text
p_0=p_1=0,
support i>=2,
largest occupied independent-set size alpha-2.
```

The profile has:

```text
k=boldk_alpha-D+O(1)=Theta(n/log n).
```

The rounding adapter:

```text
upper-boundary-r2-rounding-stability-u4-closure-2026-05-13.md
```

exports:

```text
tail/relevance hypotheses,
room >= R_2^{finite}/2,
prefix/lower-boundbeta >= P_2^{finite}/2,
k_u=O(n/log n),
active window i<=C sqrt(log n).
```

Thus every structural C3 hypothesis is satisfied once `R2-U1/R2-U2` provide
the exact finite positive margins.

## Adapter theorem

Let `bf{k}^{up,2}` be the rounded alpha-anchor `r=2` profile from `R2-U4`.
Then:

```text
E[Z_{bf{k}^{up,2}}^co]
  = (1-o(1)) E[X_{bf{k}^{up,2}}^co].
```

Consequently, if the first-moment bridge supplies:

```text
E[X_{bf{k}^{up,2}}^co] >= exp(c n/log n)
```

for some fixed `c>0`, then:

```text
E[Z_{bf{k}^{up,2}}^co] >= exp(c' n/log n)
```

for some fixed `c'>0`.

## Status

`R2-U5` is closed conditional on `R2-U1/R2-U2/R2-U4` and the first-moment
bridge supplying the large unrestricted/restricted cocolouring expectation.

There is no separate upper-boundary C3 source-gate blocker.
