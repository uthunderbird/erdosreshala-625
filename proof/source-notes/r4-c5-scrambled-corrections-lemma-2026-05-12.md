# R4 C5 scrambled correction bounds

Date: 2026-05-12

## Purpose

This note targets the remaining S3/S4 rows in
`r4-c5-source-table-2026-05-12.md`.

HP Lemma 6.3 gives the scrambled contribution in terms of

```text
exp(k_a^2/mu_a + O(M_A+M_B)).
```

For the active R4 constrained `alpha-1` profile, we need the corresponding
correction terms to be harmless:

```text
k_a^2/mu_a + M_A + M_B = O(log^2 n)
```

or better.  Since C5 only needs an overall `exp(O(log^2 n))` second-moment
bound, `O(log^2 n)` is sufficient, though `O(1)` is preferable.

## Source formulas

HP Lemma 6.3 states, for `a=alpha_0-O(1)`,

```text
scrambled contribution
  <= exp(k_a^2/mu_a + O(M_A+M_B)),
```

where

```text
M_B = k_a^4 log^2 n / (n mu_a^2),
```

and

```text
M_A =
  n/(mu_a log n)
  + (k_a^2 log^3 n + k_a k_{a-1} log^2 n)/(mu_a n)
  + (k_{a-2} log n + k_{a-1} log^2 n + k_a log^3 n)^2/(mu_a n^2).
```

Here `k_u` are profile coordinates and `mu_u` is the expected number of
independent `u`-sets.

## R4 specialization

For the constrained `alpha-1` profile:

```text
a = alpha-1,
k = O(n/log n),
k_u <= k,
u in [u_*, alpha-1],
u_* = alpha-O(sqrt(log n)).
```

The low-regime endpoint for the R4 constrained proof includes

```text
mu_alpha <= n^{x0+o(1)}.
```

But the scrambled formula uses `mu_a=mu_{alpha-1}`, not `mu_alpha`.
For `G(n,1/2)`,

```text
mu_{alpha-1}
  = mu_alpha * Theta(alpha/n) * 2^{alpha-1}
  = mu_alpha * n^{1-o(1)}.
```

Thus even in the endpoint where `mu_alpha` is polylogarithmic or smaller,
the relevant `mu_{alpha-1}` is typically `n^{1-o(1)} mu_alpha`.  The
endpoint branch must be checked separately if this product is too small.

## Sufficient condition

The scrambled correction is harmless if the certificate/source estimates
prove

```text
mu_{alpha-1} >= n/log^4 n.
```

Indeed, using `k_u<=O(n/log n)`:

```text
k_a^2/mu_a
  <= O(n^2/log^2 n)/(n/log^4 n)
  = O(n log^2 n),
```

which is too weak for C5.  For `exp(O(log^2 n))`, we need the stronger

```text
mu_{alpha-1} >= c n^2/log^4 n
```

to get

```text
k_a^2/mu_a = O(log^2 n).
```

This is the real scrambled-range constraint.

Under

```text
mu_{alpha-1} >= c n^2/log^4 n,
```

we have:

```text
M_B
 <= O((n/log n)^4 log^2 n / (n (n^2/log^4 n)^2))
 = O(log^8 n/n),
```

```text
n/(mu_a log n)
 <= O(log^3 n/n),
```

```text
(k_a^2 log^3 n + k_a k_{a-1} log^2 n)/(mu_a n)
 <= O((n^2/log^2 n)log^3 n / ((n^2/log^4 n)n))
 = O(log^5 n/n),
```

and

```text
(k_{a-2}log n+k_{a-1}log^2 n+k_a log^3 n)^2/(mu_a n^2)
 <= O((n log^2 n)^2 / ((n^2/log^4 n)n^2))
 = O(log^8 n/n^2).
```

Thus

```text
M_A+M_B=o(1),
k_a^2/mu_a=O(log^2 n).
```

This is enough for C5.

## Obstruction

The sufficient condition

```text
mu_{alpha-1} >= c n^2/log^4 n
```

is not automatic in the entire low-`mu_alpha` regime.  Since

```text
mu_{alpha-1} = mu_alpha n^{1-o(1)},
```

it corresponds roughly to

```text
mu_alpha >= n^{1-o(1)}/log^4 n,
```

which is far stronger than the low-regime endpoint.

Therefore the direct HP scrambled estimate, with its `k_a^2/mu_a` term,
does not close C5 throughout R4.

## Consequence for R4

Rows S3/S4 cannot simply be marked OK for the full constrained low regime.
There are two possible ways forward:

1. prove a sharper scrambled estimate for the constrained profile that
   removes or improves the `k_a^2/mu_a` term using the top-cap structure; or
2. split the low regime further and use a different cochromatic argument in
   the endpoint range where `mu_{alpha-1}` is too small.

This is a substantive mathematical blocker, not bookkeeping.

## Current status

This note records the obstruction for the original stronger
`exp(O(log^2 n))` target.  The active proof no longer uses that target in
the endpoint regime.  The parameterized-amplification replacement and the
`r=2,3` omitted-top correction calculation are recorded in:

```text
c5-scrambled-correction-active-r23-2026-05-12.md
```

S3/S4 remain open only until the active-profile source rows and exact-`d_u`
certificate fields are supplied.
