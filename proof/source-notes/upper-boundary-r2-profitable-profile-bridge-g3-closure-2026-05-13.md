# Upper-boundary r=2 profitable-profile bridge G3 closure

Date: 2026-05-13

## Purpose

This note closes `R2-G3` conditional on `R2-G1`.

It assembles:

```text
R2-G1 limiting interval certificate,
R2-G2 exact finite transfer,
U3 first-moment shift,
R2-U4 rounding stability,
R2-U5 C3 first-moment preservation,
R2-U6 C5 second moment/Azuma,
```

into the upper-boundary `zeta` bound:

```text
zeta(G) <= boldk_alpha-c n/log^3 n+o(n/log^3 n)
```

with high probability.

## Inputs

Assume `R2-G1` proves:

```text
Room_2(x) >= 0.07,
Prefix_2(x) >= 0.006
```

uniformly for:

```text
x in [0.95,1].
```

Then `R2-G2` exports exact finite margins:

```text
Room_{A,2}^{finite}(x) >= 0.035,
Prefix_{A,2}^{finite}(x) >= 0.003
```

for all sufficiently large:

```text
A=alpha.
```

The rounding theorem loses only:

```text
o(1)
```

on the profile scale, so for all sufficiently large `n` the rounded profile
has, conservatively:

```text
Room^{round} >= 0.03,
Prefix^{round} >= 0.002.
```

The first-moment shift theorem gives, for:

```text
D=c_D n/log^3 n,
K=boldk_alpha,
```

the exponent cost:

```text
(2/log 2+o(1))D log^2 n
  = (2c_D/log 2+o(1)) n/log n.
```

## Choice of saving constant

Choose:

```text
c_D = 0.001.
```

Then the shift cost coefficient is:

```text
2c_D/log 2 < 0.003.
```

This is much smaller than the conservative rounded room:

```text
0.03.
```

Therefore the rounded alpha-anchor `r=2` profile at:

```text
K-D = boldk_alpha-floor(0.001 n/log^3 n)
```

retains a positive first-moment exponent reserve:

```text
c_FM n/log n
```

with, for example:

```text
c_FM=0.01
```

after increasing `n0`.

The exact numerical values are not important; the proof only needs:

```text
0 < c_D < (log 2/2) * 0.03.
```

## Rounded profile output

The rounded profile `bf{k}^{up,2}` satisfies:

```text
sum_u k_u
  <= boldk_alpha-0.001 n/log^3 n+o(n/log^3 n),
sum_u u k_u=n,
k_u=0 for u>alpha-2,
tail/relevance hypotheses,
prefix/lower-boundbeta >= 0.002,
E[X_{bf{k}^{up,2}}^co] >= exp(0.01 n/log n).
```

Here `X^co` denotes the unrestricted/restricted cocolouring expectation
before fixed-partition exclusions, depending on the notation of the C3
interface.

## C3 preservation

By:

```text
upper-boundary-r2-c3-source-gate-adapter-2026-05-13.md
```

the fixed-partition restrictions preserve the first moment:

```text
E[Z_{bf{k}^{up,2}}^co]
  = (1-o(1))E[X_{bf{k}^{up,2}}^co].
```

Thus for some fixed positive constant, say after weakening:

```text
E[Z_{bf{k}^{up,2}}^co] >= exp(0.005 n/log n).
```

## C5 second moment and amplification

By:

```text
upper-boundary-r2-c5-active-profile-adapter-2026-05-13.md
```

the active second moment satisfies:

```text
E[(Z^co)^2]/E[Z^co]^2 <= exp(Q(n)),
Q(n)=o(n/log^6 n).
```

Paley-Zygmund gives a positive-probability existence event of size:

```text
exp(-o(n/log^6 n)).
```

The existing parameterized Azuma amplification then upgrades this to a whp
existence statement with colour-count loss:

```text
o(n/log^3 n).
```

Therefore:

```text
zeta(G)
  <= boldk_alpha-0.001 n/log^3 n+o(n/log^3 n)
```

with high probability on:

```text
x in [0.95,1].
```

## Combination with lower bound

The ordinary lower-bound side is already closed:

```text
chi(G) >= boldk_alpha-o(n/log^3 n)
```

whp by:

```text
upper-boundary-alpha-lower-bound-u8a-closure-2026-05-13.md
upper-boundary-alpha-to-ordinary-transfer-u8b-closure-2026-05-13.md
```

Intersecting the whp lower and upper events yields:

```text
chi(G)-zeta(G)
  >= 0.001 n/log^3 n-o(n/log^3 n)
  -> infinity
```

on the upper-boundary `r=2` interval.

## Status

`R2-G3` is closed conditional on `R2-G1`.

Consequently, the full upper-boundary `r=2` route is now reduced to:

```text
R2-G1 proof-grade directed interval certificate.
```
