# P3-specific C3 application theorem

Date: 2026-05-13

## Purpose

This note applies the standalone C3 first-moment-preservation lemma to the
rounded active P3 profiles.  It repairs the earlier L3 gap where the chain
jumped directly from `E[X^co]` to the C5 input `E[Z^co]`.

## Inputs

### Input 1: rounded P3 profile

The P3-specific rounding theorem constructs a rounded profile with:

```text
largest occupied size alpha-r,
r in {2,3},
total part count Theta(n/log n),
Gaussian tail/relevance hypotheses,
positive prefix margin.
```

Source:

```text
p3-specific-rounding-theorem-2026-05-13.md
```

### Input 2: fixed-partition restriction estimates

The C5 source table records the intended route by which HP/Heckel
fixed-partition `B,C,D` restriction estimates should become available for
the active `r=2/r=3` profiles once the profile supplies:

```text
tail/relevance hypotheses,
lower-boundbeta / prefix positivity,
large cocolouring first moment,
active scrambled scale.
```

The source-gate closure summary records that the checker now accepts the
table:

```text
gate_closed=true,
open_count=0,
blocked_count=0,
active_profile_unresolved_ids=[].
```

Sources:

```text
c5-source-gate-closure-summary-2026-05-12.md
p3-c3-source-gate-instantiation-2026-05-13.md
r4-c3-first-moment-preservation-full-lemma-2026-05-12.md
```

## Theorem

For the rounded active P3 profile `bf{k}^{(r)}`:

```text
E[Z_{bf{k}^{(r)}}^co]
  = (1-o(1)) E[X_{bf{k}^{(r)}}^co].
```

Consequently, if:

```text
E[X_{bf{k}^{(r)}}^co] >= exp(c n/log n),
```

then:

```text
E[Z_{bf{k}^{(r)}}^co] >= exp(c' n/log n)
```

for some fixed `c'>0`.

## Proof

By `p3-c3-source-gate-instantiation-2026-05-13.md`, the fixed-partition
source gate for the active `r=2/r=3` profiles is closed.  The rounded P3
profile satisfies the structural hypotheses of the standalone C3 lemma: all
nonzero class sizes lie in the active window, the total number of parts is
`Theta(n/log n)`, the HP tail/relevance condition follows from the Gaussian
tail, and the required fixed-partition `B,C,D` estimates are available.

The C3 lemma therefore gives:

```text
E[Z^co]=(1-o(1))E[X^co].
```

The exponential lower bound is preserved after multiplying by `1-o(1)`.

## Status

This repairs the structural C3 omission in L3 and closes the fixed-partition
source-gate dependency for the active P3 profiles.
