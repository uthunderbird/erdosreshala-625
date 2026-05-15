# Upper-boundary alpha lower-bound U8a closure

Date: 2026-05-13

## Purpose

This note closes `U8a` from:

```text
upper-boundary-alpha-anchor-r1-certificate-theorem-2026-05-13.md
```

It proves the alpha-anchor lower-bound event:

```text
E_alpha: chi_alpha(G) >= boldk_alpha(n)-1
```

with probability `1-o(1)`.

## Source chain

The required source inputs are:

```text
1. HR 2023, Lemma k* in revised-arxiv.tex.
2. HR/HP one-more-colour derivative estimate.
3. HP improved approximation for log E_{n,k,t}.
4. First-moment threshold definition.
```

## HR threshold-location input at beta=alpha

HR Lemma `k*` assumes a function `beta(n)` satisfying, for some fixed
`epsilon>0`,

```text
alpha_0(n)-1-2/log 2 + epsilon <= beta(n) <= alpha_0(n)+100,
```

and constant on each interval of its domain.

Take:

```text
beta(n)=alpha(n).
```

This satisfies the lower hypothesis with room, because:

```text
alpha - (alpha_0-1-2/log 2)
  = 1+2/log 2 - x
  >= 2/log 2 > 0.
```

It also satisfies the upper hypothesis trivially, and `alpha(n)` is
piecewise constant in `n`.

HR Lemma `k*` therefore gives a continuous threshold approximation
`k^*(n)` such that:

```text
n/k^*(n)
  = alpha(n)-1-2/log 2
    + log(mu_alpha(n))/(log n-log log n)
    + O(1/log n),
```

and:

```text
boldk_alpha(n)=k^*(n)+O(log^2 n).
```

Since:

```text
log(mu_alpha(n)) = (alpha-alpha_0+o(1)) log n,
```

we get:

```text
n/boldk_alpha(n)
  = alpha_0(n)-1-2/log 2+o(1).
```

Thus:

```text
boldk_alpha(n)=n/(alpha-Theta(1)),
```

and the HR one-more-colour derivative applies uniformly at:

```text
t=alpha,
k in {boldk_alpha-2,boldk_alpha-1}.
```

## Exponential drop below threshold

The derivative estimate gives:

```text
L_0(n,k+1,alpha)-L_0(n,k,alpha)
  = (2/log 2 + o(1)) log^2 n
```

uniformly for:

```text
k in {boldk_alpha-2,boldk_alpha-1}.
```

The HP lower-bound proof uses this one-more-colour comparison together with
the improved approximation to conclude:

```text
E_{n,boldk_alpha-2,alpha}
  <= exp(-Theta(log^2 n)).
```

The same argument applies at `a=alpha` because:

```text
1. HR Lemma k* places boldk_alpha in the required threshold window;
2. the derivative lemma is stated for t=alpha_0-O(1), hence includes t=alpha;
3. HP improved approximation is stated for t=alpha-O(1), hence includes
   t=alpha.
```

## Markov lower bound

Let `Y` be the number of alpha-bounded colourings with at most:

```text
boldk_alpha-2
```

colours.  Then:

```text
E[Y] <= E_{n,boldk_alpha-2,alpha}
     <= exp(-Theta(log^2 n))
     -> 0.
```

By Markov:

```text
P(Y>0) -> 0.
```

Therefore, with probability `1-o(1)`:

```text
chi_alpha(G) >= boldk_alpha-1.
```

## Output

This proves:

```text
E_alpha: chi_alpha(G) >= boldk_alpha(n)-1
```

with probability `1-o(1)`.

This is stronger than the `U8a` budget required in the upper-boundary
alpha-anchor route.

## Status

`U8a` is closed, subject only to citing the HR and HP lemmas by their final
publication identifiers.
