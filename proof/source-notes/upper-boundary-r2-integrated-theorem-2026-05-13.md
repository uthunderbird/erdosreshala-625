# Upper-boundary r=2 integrated theorem

Date: 2026-05-13

## Purpose

This note integrates the upper-boundary alpha-anchor `r=2` route and closes
the remaining good-branch endpoint:

```text
x in [0.95,1).
```

## Theorem

For all sufficiently large `n` with:

```text
x=alpha_0-alpha in [0.95,1),
```

we have, with probability `1-o(1)`:

```text
chi(G(n,1/2))-zeta(G(n,1/2)) -> infinity.
```

More quantitatively:

```text
chi(G)-zeta(G)
  >= 0.001 n/log^3 n-o(n/log^3 n).
```

## Lower-bound side

The ordinary chromatic lower bound is closed by:

```text
upper-boundary-alpha-lower-bound-u8a-closure-2026-05-13.md
upper-boundary-alpha-to-ordinary-transfer-u8b-closure-2026-05-13.md
```

It gives, with probability `1-o(1)`:

```text
chi(G) >= boldk_alpha-o(n/log^3 n).
```

The proof uses:

```text
1. HR Lemma k* with beta=alpha;
2. HR/HP one-more-colour derivative;
3. HP improved approximation;
4. Markov for alpha-bounded colourings below boldk_alpha-1;
5. Markov for X_{alpha+1}=n^{o(1)}.
```

## Upper-bound side

The cocolouring upper bound uses the alpha-anchor `r=2` profile:

```text
p_0=p_1=0,
support i>=2,
largest occupied size alpha-2.
```

### Certificate

The limiting certificate is closed by:

```text
upper-boundary-r2-directed-certificate-proof-2026-05-13.md
```

It proves:

```text
Room_2(x) >= 0.07,
Prefix_2(x) >= 0.006
```

uniformly on:

```text
x in [0.95,1].
```

### Exact finite transfer

The finite transfer is closed by:

```text
upper-boundary-r2-exact-finite-transfer-g2-closure-2026-05-13.md
```

It gives exact finite margins, for all sufficiently large `n`:

```text
Room_{alpha,2}^{finite}(x) >= 0.035,
Prefix_{alpha,2}^{finite}(x) >= 0.003.
```

### First-moment shift

The shift theorem is:

```text
upper-boundary-alpha-first-moment-shift-u3-closure-2026-05-13.md
```

For:

```text
K=boldk_alpha,
D=0.001 n/log^3 n,
```

it gives shift cost:

```text
(2/log 2+o(1))D log^2 n
  < 0.003 n/log n
```

for all sufficiently large `n`.

This is much smaller than the transferred/rounded room reserve.

### Rounding

Rounding stability is supplied by:

```text
upper-boundary-r2-rounding-stability-u4-closure-2026-05-13.md
```

It preserves room, prefix, tail/relevance, and the support condition
`i>=2` up to `o(1)` on the profile scale.

### C3

The C3 first-moment preservation adapter is:

```text
upper-boundary-r2-c3-source-gate-adapter-2026-05-13.md
```

It gives:

```text
E[Z_{bf{k}^{up,2}}^co]
  >= exp(c n/log n)
```

for some fixed `c>0`, after fixed-partition restrictions.

### C5

The active C5 adapter is:

```text
upper-boundary-r2-c5-active-profile-adapter-2026-05-13.md
```

The active scrambled scale is:

```text
mu_{alpha-2}
  = mu_alpha * Theta((n/log n)^2)
  >> n log^4 n
```

on `x in [0.95,1)`.  Hence:

```text
E[(Z^co)^2]/E[Z^co]^2 <= exp(o(n/log^6 n)).
```

Parameterized Paley-Zygmund plus Azuma amplification yields:

```text
zeta(G)
  <= boldk_alpha-0.001 n/log^3 n+o(n/log^3 n)
```

with probability `1-o(1)`.

This assembly is recorded in:

```text
upper-boundary-r2-profitable-profile-bridge-g3-closure-2026-05-13.md
```

## Final event intersection

Let:

```text
E_chi  = {chi(G) >= boldk_alpha-o(n/log^3 n)},
E_zeta = {zeta(G) <= boldk_alpha-0.001 n/log^3 n+o(n/log^3 n)}.
```

Both events hold with probability `1-o(1)`.  Therefore:

```text
P(E_chi ∩ E_zeta) = 1-o(1).
```

On this intersection:

```text
chi(G)-zeta(G)
  >= 0.001 n/log^3 n-o(n/log^3 n)
  -> infinity.
```

## Status

The upper-boundary endpoint `x in [0.95,1)` is closed, subject to the
standard publication appendix replacement of finite decimal certificate
checks by explicit directed interval tables.
