# P3-specific rounding theorem

Date: 2026-05-13

## Purpose

This note replaces the invalid use of the generic R4 C1 rounding lemma in the
low-branch P3 bridge.  It states a rounding theorem directly for the
`r=2/r=3` exact finite P3 profiles.

## Setup

Fix:

```text
r in {2,3},
x in [0,0.029155],
k = k_{alpha-1}(n)-floor(c_r n/log^3 n),
```

where `c_r>0` is fixed and sufficiently small.

Let `p^{(r)}_{A,x}` be the exact finite P3 profile from:

```text
g4-finite-objective-closure-theorem-2026-05-12.md
```

with deficit support:

```text
i >= r,
u = alpha-i.
```

## Quantitative stability lemma

The quantitative stability input is now isolated in:

```text
p3-rounding-stability-room-prefix-lemma-2026-05-13.md
```

It proves that the exact finite room and prefix functionals change by `o(1)`
under the `O(polylog(n)/k)` perturbation produced below on the Gaussian-tail
class.

## Theorem

For all sufficiently large `n`, there is an integer profile `bf{k}^{(r)}` such
that:

```text
sum_u k_u = k+O(1),
sum_u u k_u = n,
k_u=0 for u>alpha-r,
k_u=0 unless alpha-u <= C sqrt(log n),
k_u/k = p^{(r)}_{A,x}(alpha-u)+O(polylog(n)/k)
```

on the active support, and:

```text
tail/relevance hypotheses hold,
finite room/prefix margins survive up to o(1).
```

## Proof sketch

The exact finite P3 profile has Gibbs form:

```text
p_i proportional exp(mu i + H_A(i)),  i>=r,
```

with `mu=O(1)` and:

```text
H_A(i)=-(ln2/2)i^2+O(i^2/A)
```

on the active finite window, by:

```text
exact-du-large-anchor-expansion-2026-05-12.md.
```

Hence the profile has a Gaussian tail.  Choose
`I_n=C_0 sqrt(log n)` so the mass and first deficit moment beyond `I_n` are
smaller than any prescribed negative power of `n`.

Set preliminary counts:

```text
m_i = floor(k p_i),  r<=i<=I_n,
m_i=0,              i>I_n.
```

The mass and deficit errors are `O(I_n^2)`.  Since the support contains
consecutive deficits `i>=r` and the Gibbs profile has positive mass on a
fixed block around its mean, these errors can be corrected by changing
`O(I_n^2)` counts among adjacent allowed deficits.  This preserves the
constraint `i>=r`, hence preserves the largest occupied size `alpha-r`.

The final `O(1)` vertex-count discrepancy is removed by another bounded
number of adjacent allowed-deficit moves.  The perturbation in empirical
profile is `O(polylog(n)/k)=o(1)`.

The quantified stability lemma for exact finite room and prefix functionals
on the Gaussian-tail class is:

```text
p3-rounding-stability-room-prefix-lemma-2026-05-13.md
```

It shows that the rounding perturbation changes room and prefix by `o(1)`,
so the fixed positive G4 margins survive after increasing `n0`.

The tail/relevance hypotheses follow from the Gaussian tail exactly as in
HP's integer approximation: for `i=alpha-u`,

```text
k_u u/n <= C' p_i <= 2^{-i gamma(i)}
```

for some increasing `gamma(i)->infinity` after weakening constants and
choosing `n` large.

## Status

This is the P3-specific replacement for the invalid generic C1 instantiation.

The round-5 state is:

```text
closed:
- combinatorial rounding construction inside the allowed P3 support;
- tail/relevance transfer from the Gaussian exact-finite profile.
- quantified stability of exact finite room/prefix under the rounding
  perturbation.
```

This note is no longer conditional on a missing rounding-stability lemma.
