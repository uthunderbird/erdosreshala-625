# Upper-boundary alpha first-moment lower-bound sublemma

Date: 2026-05-13

## Purpose

This note sharpens U7.1 from:

```text
upper-boundary-alpha-anchor-ordinary-lower-bound-target-2026-05-13.md
```

The needed ordinary lower bound is:

```text
chi_alpha(G) >= boldk_alpha-1
```

with high probability.

## Source definition

HP-2023 defines the `t`-bounded first-moment threshold by:

```text
boldk_t(n) = min { k : E_{n,k,t} >= 1 }.
```

The definition is stated for general `t`-bounded colourings, and the source
notes that `E_{n,k,t}` is increasing in `k`.

Therefore:

```text
E_{n,boldk_alpha-1,alpha} < 1.
```

However, this alone is not enough for a whp lower bound
`chi_alpha >= boldk_alpha-1`.  It only gives a bounded first-moment estimate
at exactly `boldk_alpha-1`.

To prove:

```text
P(chi_alpha <= boldk_alpha-2) -> 0,
```

we need:

```text
E_{n,boldk_alpha-2,alpha} -> 0.
```

## Required sublemma

Prove:

```text
E_{n,boldk_alpha-2,alpha}
  <= exp(-Theta(log^2 n)).
```

or any bound tending to zero.

## Expected proof route

HP's proof of the corresponding lemma for `a in {alpha-2,alpha-1}` uses:

```text
1. the first-moment threshold definition;
2. one-more-colour comparison;
3. average-colour-class estimate;
4. improved L_0 approximation.
```

The same argument should extend to `a=alpha` if the one-more-colour and
`L_0` derivative estimates are uniform for:

```text
t=alpha,
k=boldk_alpha+O(1).
```

Equivalently, it is enough to prove the local threshold slope:

```text
log E_{n,k+1,alpha} - log E_{n,k,alpha}
  >= c log^2 n
```

uniformly for:

```text
k in {boldk_alpha-2,boldk_alpha-1}.
```

Then, since:

```text
E_{n,boldk_alpha-1,alpha}<1,
```

we get:

```text
E_{n,boldk_alpha-2,alpha}
  <= exp(-c log^2 n).
```

## Status

This is the remaining U7.1 source/theorem check.

It is a first-moment threshold-slope lemma at `a=alpha`.  It does not involve
HP tame profiles, lower-boundbeta, or second moments.

Once this sublemma is proved, U7.1 is closed by Markov:

```text
P(chi_alpha <= boldk_alpha-2)
  <= E_{n,boldk_alpha-2,alpha}
  -> 0.
```

Then:

```text
chi_alpha >= boldk_alpha-1
```

whp.

## Follow-up decomposition

The derivative/slope part is isolated in:

```text
upper-boundary-alpha-first-moment-slope-theorem-2026-05-13.md
```

The source audit is isolated in:

```text
upper-boundary-alpha-one-more-colour-source-check-2026-05-13.md
```

Current conclusion of that audit:

```text
1. HR one-more-colour derivative is source-backed for t=alpha.
2. HP improved approximation is source-backed for t=alpha.
3. The printed HP average-colour-class lemma is only stated for
   t in {alpha-1, alpha-2}.
```

Thus the remaining narrow theorem target is the alpha-anchor
average-colour-class estimate:

```text
n / boldk_alpha = alpha_0 - 1 - 2/ln 2 + o(1).
```
