# Alpha0 floor endpoint split theorem

Date: 2026-05-12

## Purpose

This note packages the `alpha_0` Stirling calculation into the exact
endpoint split needed by the standard P3 route.

It is the final G6 theorem target.

## Definitions

Let:

```text
b=log 2,
L=log_2 n,
ell=log_2 L,
c=2/b-1,
alpha_0=2L-2ell+c,
alpha=floor(alpha_0),
x=alpha_0-alpha in [0,1).
```

For integer `t`, define:

```text
mu_t = binom(n,t) 2^{-t(t-1)/2}.
```

## Theorem 1: floor expectation asymptotic

As `n->infinity`,

```text
log mu_alpha = x log n + O((log log n)^2).
```

In particular:

```text
mu_alpha >= exp(-C(log log n)^2)
```

for some absolute constant `C`.

### Proof

By Stirling, uniformly for `t=2L+O(log L)`:

```text
log mu_t = F(t)+O(log log n),
```

where:

```text
F(t)=t log n-t log t+t-(b/2)t(t-1).
```

The direct expansion in

```text
alpha0-mu-floor-stirling-proof-2026-05-12.md
```

gives:

```text
F(alpha_0)=O((log L)^2).
```

For `u` between `alpha` and `alpha_0`, derivative bounds give:

```text
F'(u)=log n-log u-bu+b/2
     = -log n+O(log log n).
```

Since `alpha=alpha_0-x`, the mean value theorem gives:

```text
F(alpha)
  = F(alpha_0) - x F'(u)
  = x log n + O((log log n)^2).
```

The sign is important here: `alpha-alpha_0=-x`, while
`F'(u)=-log n+O(log log n)`.  Hence the product
`(alpha-alpha_0)F'(u)` contributes `+x log n+O(log log n)`, not
`-x log n`.

Combining with the Stirling error proves the claim.

This avoids treating `mu_{alpha_0}` as an actual combinatorial quantity;
`alpha_0` only appears inside the smooth function `F`.

## Theorem 2: endpoint r=2/r=3 split

Let:

```text
N_scr=n log^4 n.
```

Then:

```text
mu_{alpha-3} >> N_scr.
```

Consequently, for all sufficiently large `n`, exactly the following
standard endpoint split is enough:

```text
if mu_{alpha-2} >> N_scr, use P3 r=2;
otherwise use P3 r=3.
```

### Proof

From the explicit ratio window lemma, for fixed `j`:

```text
mu_{alpha-j} >= c_j mu_alpha (n/log n)^j
```

for all sufficiently large `n`.

Using Theorem 1 with `j=3`:

```text
mu_{alpha-3}
  >= c_3 exp(-C(log log n)^2) n^3/(log n)^3.
```

Divide by `N_scr=n log^4 n`:

```text
mu_{alpha-3}/N_scr
  >= c_3 n^2 exp(-C(log log n)^2)/(log n)^7 -> infinity.
```

Therefore:

```text
mu_{alpha-3} >> n log^4 n.
```

If `mu_{alpha-2} >> N_scr`, the `r=2` omitted-top profile has manageable
scrambled scale.  If not, the displayed estimate supplies the `r=3`
scrambled scale.  Thus no deeper shifted-anchor recursion is needed for
the standard `alpha=floor(alpha_0)` route.

## Consequence for G6

G6 reduces to citing:

```text
mu-ratio-explicit-window-lemma-2026-05-12.md,
alpha0-mu-floor-stirling-proof-2026-05-12.md,
this endpoint split theorem.
```

and integrating the split with the P3 `r=2/r=3` certificate.

## Status

This is the paper-ready G6 theorem statement and proof sketch.  It still
depends on the final P3 certificate for `r=2,3`; that dependency belongs to
G3/G4, not G6.
