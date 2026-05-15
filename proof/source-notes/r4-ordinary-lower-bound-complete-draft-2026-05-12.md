# R4 ordinary chromatic lower bound: complete draft

Date: 2026-05-12

## Purpose

This note writes the ordinary chromatic lower-bound side of the R4
low-regime proof as a complete analytical draft.

The target is:

```text
chi(G(n,1/2)) >= k_{alpha-1}(n) - o(n/log^3 n)
```

throughout every fixed sublinear expectation regime

```text
mu_alpha(n) <= n^{theta+o(1)}
```

with fixed `theta<1`.  In particular, this applies to the active low-branch
interval of the integrated proof by taking `theta=0.029155`.

This is the lower-bound input needed to combine with the constrained
cochromatic upper bound

```text
zeta(G) <= k_{alpha-1} - c n/log^3 n + o(n/log^3 n).
```

## Notation

Let

```text
G ~ G(n,1/2),
alpha = alpha(n),
mu = mu_alpha(n),
beta = alpha-1,
k_beta = k_{alpha-1}(n).
```

Let `X_alpha(G)` be the number of independent sets of size `alpha` in
`G`.

## Lemma 1: bounded-to-ordinary conversion

For every graph `G` with independence number at most `alpha`,

```text
chi_beta(G) <= chi(G) + X_alpha(G).
```

Proof:

Take an ordinary optimal colouring of `G`. Since the independence number is
at most `alpha`, every colour class has size at most `alpha`. The only
classes violating beta-boundedness have size exactly `alpha`. There are at
most `X_alpha(G)` such classes, since each is an independent `alpha`-set.

Remove one vertex from each size-`alpha` class and make each removed vertex
a singleton colour class. This increases the number of colours by at most
`X_alpha(G)` and all original classes now have size at most `alpha-1`.
Thus

```text
chi_beta(G) <= chi(G)+X_alpha(G).
```

Equivalently,

```text
chi(G) >= chi_beta(G)-X_alpha(G).
```

For `G(n,1/2)`, the standard first-moment definition of `alpha(n)` gives
`alpha(G)<=alpha` whp; this event can be intersected with the estimates
below.

## Lemma 2: beta-bounded lower bound

HP/Heckel Lemma 8.1 gives, whp,

```text
chi_beta(G) >= k_beta - 1.
```

This is the same source used in Heckel 2024's lower-bound subsection.

Combining Lemmas 1 and 2 gives, whp,

```text
chi(G) >= k_beta - 1 - X_alpha(G).
```

It remains to control `X_alpha`.

## Regime A: endpoint, mu < log^5 n

Assume

```text
mu < log^5 n.
```

By Markov,

```text
Pr[X_alpha > log^6 n] <= mu/log^6 n < 1/log n -> 0.
```

Hence whp

```text
X_alpha <= log^6 n.
```

Therefore

```text
chi(G) >= k_beta - O(log^6 n)
```

whp.

Since

```text
log^6 n = o(n/log^3 n),
```

we obtain

```text
chi(G) >= k_beta - o(n/log^3 n).
```

## Regime B: log^5 n <= mu <= n^{theta+o(1)}, fixed theta<1

Use HR Lemma `alphashift` from:

```text
work/hr2023/HowDoes.tex, label lem:alphashift, around lines 1738--1744.
```

If

```text
log^5 n <= mu_alpha(n) = O(n/log^2 n),
```

then whp

```text
chi(G)
  >= k^*(n)
     - (1+eps(n)) mu log nu
       / (alpha(log n-log log n)),
```

where

```text
nu = (n/log n)/mu,
eps(n)=O(1/log nu)->0.
```

Here `k^*(n)=k_beta^*(n)` is defined in HR Lemma `k*`:

```text
work/hr2023/HowDoes.tex, label lem:k*, around lines 1680--1688.
```

That lemma states, for integer `n`, that:

```text
k_beta - k^*(n) = O(log^2 n).
```

Heckel 2024 uses exactly this translation in the commented sharper lower
bound:

```text
work/heckel2024/cochromatic-97.tex, around lines 404--414.
```

There Heckel cites HR Lemma 43 with Lemma 41 and says Lemma 43 gives the
lower bound with `k^*(n)` in place of `boldk_{alpha-1}`, while Lemma 41 gives
the `O(log^2 n)` difference.

Thus

```text
chi(G)
  >= k_beta
     - O(log^2 n)
     - (1+o(1)) mu log nu
       / (alpha(log n-log log n)).
```

In the current regime, write

```text
mu <= n^{theta+o(1)}
```

with fixed `theta<1`. Also

```text
alpha = Theta(log n),
log nu = O(log n).
```

Therefore

```text
mu log nu / (alpha(log n-log log n))
  <= n^{theta+o(1)} * O(log n) / Theta(log^2 n)
  = n^{theta+o(1)} / polylog(n).
```

Since `theta<1`,

```text
n^{theta+o(1)} / polylog(n) = o(n/log^3 n).
```

Also

```text
O(log^2 n)=o(n/log^3 n).
```

Hence

```text
chi(G) >= k_beta - o(n/log^3 n)
```

whp.

## Conclusion

Combining Regimes A and B:

If

```text
mu_alpha(n) <= n^{theta+o(1)}
```

for any fixed `theta<1`, then

```text
chi(G(n,1/2)) >= k_{alpha-1}(n) - o(n/log^3 n)
```

with high probability.

Taking `theta=0.029155` gives the ordinary lower-bound input on the full
active low branch:

```text
0 <= x <= 0.029155.
```

Equivalently, on that whole branch,

```text
mu_alpha(n) <= n^{0.029155+o(1)}
```

and hence

```text
chi(G(n,1/2)) >= k_{alpha-1}(n) - o(n/log^3 n)
```

with high probability.

then

```text
chi(G(n,1/2)) >= k_{alpha-1}(n) - o(n/log^3 n)
```

with high probability.

## Role in the prize proof

This lower-bound side is now no longer the main obstacle for R4.

The remaining missing theorem is the constrained cochromatic upper bound:

```text
zeta(G) <= k_{alpha-1} - c n/log^3 n + o(n/log^3 n)
```

in the same low regime.

Together, these two estimates would imply

```text
chi(G)-zeta(G) >= (c-o(1)) n/log^3 n -> infinity.
```

## Caveats

1. The statement `alpha(G)<=alpha` whp should be included explicitly in
   the final paper proof or absorbed into the standard definition of
   `alpha(n)`.

2. The exact HR notation/citation has now been localized to
   `HowDoes.tex` labels `lem:alphashift` and `lem:k*`, plus the Heckel 2024
   comment around lines 404--414.

3. The endpoint Markov argument only uses expectation of `X_alpha`; it is
   intentionally crude but sufficient.
