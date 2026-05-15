# Stirling proof for `mu_floor(alpha_0)`

Date: 2026-05-12

## Purpose

This note supplies the missing proof behind:

```text
alpha0-mu-floor-asymptotic-lemma-2026-05-12.md
```

It proves the estimate needed by the endpoint SHIFT gate:

```text
mu_alpha = n^{x+o(1)},  x=alpha_0-floor(alpha_0).
```

The proof is intentionally written with an error term stronger than needed:

```text
log mu_alpha = x log n + O((log log n)^2).
```

## Definitions

Use natural logarithms unless explicitly marked otherwise.  Let

```text
b = log 2,
L = log_2 n = (log n)/b,
ell = log_2 L.
```

Define

```text
alpha_0 = 2L - 2ell + 2log_2(e/2)+1.
```

Since

```text
2log_2(e/2)+1 = 2/log 2 - 1,
```

write

```text
c = 2/b - 1,
alpha_0 = 2L - 2ell + c.
```

Let

```text
alpha = floor(alpha_0),
x = alpha_0-alpha in [0,1).
```

Finally:

```text
mu_t = binom(n,t)2^{-t(t-1)/2}.
```

## Stirling reduction

For `t=O(log n)`,

```text
log binom(n,t)
  = t log n - log(t!) + O(t^2/n)
  = t log n - t log t + t + O(log t).
```

Therefore:

```text
log mu_t
  = t log n - t log t + t - (b/2)t(t-1) + O(log t).
```

Define the smooth main term:

```text
F(t)=t log n - t log t + t - (b/2)t(t-1).
```

Then:

```text
log mu_t = F(t)+O(log log n)
```

uniformly for `t=2L+O(log L)`.

## Evaluation at `alpha_0`

Let

```text
y = -2ell+c,
alpha_0 = 2L+y.
```

Since `y=O(log L)`,

```text
log alpha_0
  = log(2L+y)
  = log(2L) + y/(2L) + O(y^2/L^2).
```

Multiplying by `alpha_0=2L+y` gives:

```text
alpha_0 log alpha_0
  = (2L+y)log(2L) + y + O(y^2/L).
```

Also:

```text
alpha_0 log n = b alpha_0 L = b(2L+y)L,
```

and

```text
(b/2)alpha_0(alpha_0-1)
  = (b/2)(2L+y)^2 - (b/2)(2L+y).
```

Substitute these into `F(alpha_0)`:

```text
F(alpha_0)
 = b(2L+y)L
   - [(2L+y)log(2L)+y+O(y^2/L)]
   + (2L+y)
   - (b/2)(2L+y)^2
   + (b/2)(2L+y).
```

The quadratic `2bL^2` terms cancel.  The remaining coefficient of `L` is:

```text
-bLy - 2L log(2L) + 2L + bL.
```

The sign is important: the `b alpha_0 L` term contributes `+bLy`, while
the quadratic term `-(b/2)alpha_0^2` contributes `-2bLy`, leaving `-bLy`.

Using `log(2L)=log 2 + log L = b + b ell`, this coefficient becomes:

```text
L[ -b(-2ell+c) - 2(b+b ell) + 2 + b ]
 = L[ 2b ell - bc -2b -2b ell +2+b ]
 = L[2-b-bc].
```

The constant `c=2/b-1` was chosen so that:

```text
bc=2-b.
```

Hence the linear-in-`L` term cancels.  The remaining terms are bounded by
`O(y log L + y^2) = O((log L)^2)`, so:

```text
F(alpha_0)=O((log L)^2).
```

Thus:

```text
log mu_{alpha_0} = O((log log n)^2).
```

Here `mu_{alpha_0}` is understood via the gamma interpolation; this is only
a notational device for evaluating the smooth main term.

## Moving from `alpha_0` to `alpha=floor(alpha_0)`

For integer ratios:

```text
log(mu_{t-1}/mu_t)
  = log t - log(n-t+1) + (t-1)log 2.
```

For `t=2L+O(log L)`, this is:

```text
log(mu_{t-1}/mu_t)
  = log n + O(log log n).
```

Moving down by fractional distance `x in [0,1)` from `alpha_0` to
`alpha=alpha_0-x` therefore changes the logarithm by:

```text
x log n + O(log log n)
```

at the smooth level.  More formally, the derivative of `F` satisfies:

```text
F'(t)=log n - log t - bt + b/2 + O(1/t)
     = -log n + O(log log n)
```

on the window, and hence:

```text
F(alpha_0-x)
  = F(alpha_0) + x log n + O(log log n).
```

Combining with the Stirling error:

```text
log mu_alpha
  = x log n + O((log log n)^2).
```

## Consequences

Since `x>=0`,

```text
mu_alpha >= exp(-C(log log n)^2)
```

for some absolute constant `C`.

For any fixed `j`, applying the explicit ratio window lemma `j` times gives:

```text
mu_{alpha-j}
  >= exp(-C(log log n)^2) * c_j (n/log n)^j.
```

In particular:

```text
mu_{alpha-3} >> n log^4 n.
```

This proves the bounded-depth endpoint split used by
`shift-index-alignment-regime-split-2026-05-12.md`.

## Status

This is a paper-level derivation of the needed asymptotic.  Before claiming
G6 fully closed, the final proof should still decide how much of the
`O((log log n)^2)` bookkeeping to spell out in the main text versus an
appendix.
