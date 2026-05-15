# R4 parameterized second-moment amplification

Date: 2026-05-12

## Purpose

The original R4 C5 target required

```text
E[Z^2]/E[Z]^2 <= exp(O(log^2 n)).
```

This is stronger than necessary.  The Azuma amplification step only needs
the Paley-Zygmund success probability to be large enough relative to the
cochromatic gap.

This note states the parameterized replacement.

## Lemma

Let `Y(G)` be a graph parameter that is 1-Lipschitz under vertex exposure.
Suppose that for some deterministic `k=k(n)` and `Q=Q(n)`:

```text
P[Y(G) <= k] >= exp(-Q).
```

Then

```text
E[Y] <= k + sqrt(2nQ) + o(sqrt(nQ)+1),
```

and, for any `s>0`,

```text
P[Y > k + sqrt(2nQ)+s] <= exp(-s^2/(2n)).
```

In particular, if `s=s(n)` satisfies `s->infinity` and `s=o(g(n))`, then
whp

```text
Y <= k + sqrt(2nQ)+s.
```

## Proof

Azuma-Hoeffding for vertex exposure gives

```text
P[Y <= E[Y]-t] <= exp(-t^2/(2n)).
```

If

```text
E[Y] > k+t,
```

then

```text
P[Y <= k] <= P[Y <= E[Y]-t] <= exp(-t^2/(2n)).
```

Taking `t=sqrt(2nQ)+o(1)` would contradict

```text
P[Y<=k] >= exp(-Q)
```

up to an arbitrarily small slack.  Thus

```text
E[Y] <= k+sqrt(2nQ)+o(sqrt(nQ)+1).
```

The upper-tail statement follows from Azuma:

```text
P[Y >= E[Y]+s] <= exp(-s^2/(2n)).
```

## Application to zeta

For

```text
Y=zeta(G),
```

vertex exposure is 1-Lipschitz: changing all edges incident to one vertex
changes `zeta` by at most one, since the vertex can be isolated as a
singleton cocolour class.

If a profile with `k` parts has restricted cocolouring count `Z` satisfying

```text
E[Z^2]/E[Z]^2 <= exp(Q),
```

then Paley-Zygmund gives

```text
P[zeta <= k] >= P[Z>0] >= exp(-Q).
```

Therefore whp

```text
zeta <= k + sqrt(2nQ)+s.
```

## R4 consequence

The constrained profile gives

```text
k <= k_{alpha-1}-c n/log^3 n.
```

The ordinary lower bound gives

```text
chi >= k_{alpha-1}-o(n/log^3 n).
```

Thus the proof still works if

```text
sqrt(nQ)=o(n/log^3 n),
```

equivalently

```text
Q=o(n/log^6 n).
```

## Direct HP scrambled bound

Using HP's scrambled estimate, the second moment can be bounded with

```text
Q = k_a^2/mu_a + O(M_A+M_B+log^2 n),
```

where `a=alpha-1`.

Since

```text
k_a = Theta(n/log n),
```

the condition

```text
k_a^2/mu_a = o(n/log^6 n)
```

is equivalent to

```text
mu_{alpha-1} >> n log^4 n.
```

Hence the direct HP scrambled bound is sufficient in the subregime

```text
mu_{alpha-1} >> n log^4 n.
```

Using

```text
mu_{alpha-1}=mu_alpha n^{1-o(1)},
```

this should correspond roughly to

```text
mu_alpha >> log^4 n * n^{o(1)}.
```

## New regime split

The low regime should be split into:

```text
L1: mu_{alpha-1} >> n log^4 n
L2: mu_{alpha-1} <= n log^4 n
```

L1 can use the existing constrained profile plus parameterized
amplification.

L2 remains the true endpoint blocker and needs a sharper scrambled estimate
or a separate cocolouring construction.

## Status

This lemma reduces the S3/S4 blocker to a smaller endpoint subregime.  It
does not close R4 completely.
