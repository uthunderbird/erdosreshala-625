# Upper-boundary r=2 C5 active-profile adapter

Date: 2026-05-13

## Purpose

This note adapts the existing C5 active-profile theorem to the upper-boundary
alpha-anchor `r=2` route from:

```text
upper-boundary-alpha-anchor-r2-robust-candidate-2026-05-13.md
```

It closes the C5 source/scale side for that route, conditional on the finite
rounded profile and source-gate inputs being supplied by `R2-U1`--`R2-U5`.

## Existing C5 theorem

The available theorem is:

```text
c5-active-profile-theorem-2026-05-12.md
```

with source gate:

```text
c5-source-gate-closure-summary-2026-05-12.md
r4-c5-source-table-2026-05-12.md
```

and correction bound:

```text
c5-scrambled-correction-active-r23-2026-05-12.md
```

The theorem is phrased for P3 `r=2,3` profiles, but its proof uses only the
following active-profile interface:

```text
1. exact finite rounded profile;
2. largest occupied independent-set size s;
3. k_u=O(n/log n) for all occupied sizes;
4. tail/relevance hypotheses;
5. lower-boundbeta or equivalent prefix/source-gate margin;
6. large restricted cocolouring first moment;
7. active scrambled scale mu_s >> n log^4 n.
```

None of these inputs depends on the historical P3 anchor after the finite
profile has been constructed.

## Upper-boundary r=2 inputs

For the alpha-anchor `r=2` profile:

```text
p_0=p_1=0,
support i>=2,
largest occupied size s=alpha-2.
```

The total number of parts remains:

```text
k=Theta(n/log n),
```

so every occupied coordinate satisfies:

```text
k_u <= k = O(n/log n).
```

The upper-boundary interval has:

```text
x=alpha_0-alpha in [0.95,1),
mu_alpha = n^{x+o(1)}.
```

Using the standard ratio:

```text
mu_{alpha-2}
  = mu_alpha * Theta((n/log n)^2),
```

we get:

```text
mu_{alpha-2}
  = n^{x+2+o(1)}/log^2 n
  >> n log^4 n.
```

Therefore the C5 active scrambled-scale condition holds with large room.

## Correction-term bound

With:

```text
s=alpha-2,
k_s=O(n/log n),
mu_s=mu_{alpha-2}>>n log^4 n,
```

the correction theorem gives:

```text
k_s^2/mu_s + M_A+M_B+O(log^2 n)
  = o(n/log^6 n).
```

In fact the leading term is much smaller:

```text
k_s^2/mu_{alpha-2}
  <= O(n^2/log^2 n) / (n^{x+2+o(1)}/log^2 n)
  = n^{-x+o(1)}
  = o(1).
```

Thus the upper-boundary `r=2` route has no scrambled-scale obstruction.

## Adapter theorem

Assume the alpha-anchor `r=2` finite rounded profile exports:

```text
room >= c_room > 0,
prefix/lower-boundbeta margin >= c_prefix > 0,
tail/relevance hypotheses,
E[Z^co] >= exp(c_FM n/log n),
k_u=O(n/log n),
largest occupied size alpha-2.
```

Then the C5 active-profile theorem applies and yields:

```text
E[(Z^co)^2]/E[Z^co]^2 <= exp(Q(n)),
Q(n)=o(n/log^6 n).
```

By the existing Paley-Zygmund plus Azuma amplification interface:

```text
Z^co>0 whp
```

after an amplification loss:

```text
o(n/log^3 n).
```

Consequently, the alpha-anchor `r=2` upper-bound profile gives:

```text
zeta(G) <= |bf{k}^{up,r2}| + o(n/log^3 n)
```

whp.

## What remains outside C5

This note does not construct the finite rounded profile.  The remaining
upper-bound route obligations are:

```text
R2-U1: proof-grade interval certificate;
R2-U2: exact finite alpha-anchor transfer for support i>=2;
R2-U3: first-moment shift below boldk_alpha;
R2-U4: rounding stability;
R2-U5: C3 fixed-partition/source-gate row for the alpha-anchor r=2 profile.
```

Once those are supplied, C5 contributes no further open source or scale
blocker.

## Status

`R2-U6` is closed conditional on `R2-U1`--`R2-U5`.
