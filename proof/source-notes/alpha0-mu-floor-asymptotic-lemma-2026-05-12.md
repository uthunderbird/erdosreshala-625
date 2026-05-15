# `alpha_0` floor `mu_alpha` asymptotic lemma

Date: 2026-05-12

## Purpose

This note records the asymptotic input needed to make the recursive
SHIFT route finite.

The earlier notes repeatedly use the standard parameterization:

```text
alpha_0(n)=2log_2 n-2log_2 log_2 n+2log_2(e/2)+1,
alpha=floor(alpha_0),
x=alpha_0-alpha in [0,1).
```

The required fact is that the expected number of independent sets of size
`alpha` has the form

```text
mu_alpha = n^{x+o(1)}.
```

In particular:

```text
mu_alpha >= n^{-o(1)}.
```

The proof is a direct Stirling expansion of

```text
mu_t = binom(n,t)2^{-t(t-1)/2}
```

at `t=floor(alpha_0)`.

Detailed proof note:

```text
alpha0-mu-floor-stirling-proof-2026-05-12.md
alpha0-floor-endpoint-split-theorem-2026-05-12.md
```

## Lemma statement

Let `L=log_2 n` and `ell=log_2 L`.  Define:

```text
alpha_0=2L-2ell+2log_2(e/2)+1,
alpha=floor(alpha_0),
x=alpha_0-alpha.
```

Then:

```text
log mu_alpha = x log n + O((log log n)^2)
```

or equivalently:

```text
mu_alpha = n^x exp(O((log log n)^2)).
```

For the finite-shift route it is enough to use the weaker consequence:

```text
mu_alpha >= exp(-C(log log n)^2)
```

for an absolute constant `C`.

## Consequence: bounded endpoint shift depth

Let

```text
N_scr = n log^4 n.
```

For fixed `j`, the explicit ratio lemma gives:

```text
mu_{alpha-j} >= mu_alpha * c_j (n/log n)^j
```

for all sufficiently large `n`, with `c_j>0` depending only on `j`.

Using the weak lower bound on `mu_alpha`,

```text
mu_{alpha-3}
  >= exp(-C(log log n)^2) * c_3 n^3/(log n)^3
  >> n log^4 n.
```

Therefore:

```text
mu_{alpha-3} >> N_scr.
```

This is stronger than the earlier micro-endpoint split.  It means that at
the initial anchor

```text
a_0=alpha-1,
```

the recursive endpoint route always stops by `r=3`:

```text
if mu_{alpha-2} >> N_scr, use r=2;
otherwise mu_{alpha-3} >> N_scr, use r=3.
```

No further anchor shift is needed for the exact `alpha=floor(alpha_0)`
definition.

## Impact on SHIFT-GATE

If this Stirling lemma is included in the final proof, the recursive shift
mechanism becomes a safety net rather than an active infinite recursion.
The needed shifted-anchor certificates reduce to:

```text
initial anchor a_0=alpha-1,
r=2 and r=3.
```

The previous certificates for bounded shifts remain useful if the proof is
later generalized to alternate anchor definitions, but the prize route can
avoid proving arbitrary finite termination.

## Remaining work

This note is now packaged by
`alpha0-floor-endpoint-split-theorem-2026-05-12.md`, which avoids treating
`mu_{alpha_0}` as a combinatorial quantity and states the exact r=2/r=3
endpoint split.
