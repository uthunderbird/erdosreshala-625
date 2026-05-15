# Upper-boundary alpha one-more-colour source check

Date: 2026-05-13

## Purpose

This note audits the source status of the first-moment lower-bound input
needed for the upper-boundary alpha-anchor route:

```text
chi_alpha(G) >= boldk_alpha(n)-1 whp.
```

It refines the remaining `U8a` question in:

```text
upper-boundary-alpha-anchor-r1-certificate-theorem-2026-05-13.md
upper-boundary-alpha-anchor-ordinary-lower-bound-target-2026-05-13.md
upper-boundary-alpha-first-moment-lowerbound-sublemma-2026-05-13.md
```

## Source facts checked

In `TameColourings.tex`, Lemma `onemorecolour` is quoted from HR as:

```text
Suppose t=t(n)=alpha_0(n)-O(1) is an integer.
Uniformly over k <= n/2 with k=n/(t-Theta(1)),
d/dk L_0(n,k,t) = (2/ln 2) ln^2 n + O(ln n ln ln n).
```

Thus the derivative/slope source itself is general enough to include:

```text
t = alpha.
```

The improved approximation lemma is also stated for:

```text
t = alpha - O(1),
n/k = t - Theta(1),
```

and therefore includes `t=alpha`.

However, the `averagecolourclass` lemma in the HP text is stated only for:

```text
t in {alpha-1, alpha-2}.
```

The printed lower-bound lemma then proves:

```text
chi_a(G) >= boldk_a - 1 whp
```

only for:

```text
a in {alpha-2, alpha-1}.
```

## Consequence

The upper-boundary route cannot honestly cite the printed HP lower-bound
lemma verbatim for `a=alpha`.

What is source-backed now:

```text
1. HR derivative / one-more-colour slope is available for t=alpha.
2. HP improved approximation is available for t=alpha.
```

What remains to be supplied:

```text
3. an alpha-anchor analogue of the average-colour-class estimate:
   n / boldk_alpha = alpha_0 - 1 - 2/ln 2 + o(1),
```

or a direct replacement showing:

```text
boldk_alpha = n/(alpha-Theta(1)).
```

Once this replacement is proved, the HP first-moment argument extends:

```text
E_{n,boldk_alpha-2,alpha}
  <= exp(-Theta(ln^2 n)),
```

and Markov gives:

```text
chi_alpha(G) >= boldk_alpha-1 whp.
```

## New narrow theorem target

The remaining theorem target for `U8a` is therefore:

```text
Alpha-anchor average-colour-class theorem.
```

Statement:

```text
n / boldk_alpha = alpha_0 - 1 - 2/ln 2 + o(1).
```

Equivalently:

```text
boldk_alpha = n/(alpha-Theta(1)).
```

Sharper endpoint issue:

```text
t=alpha means i_0=alpha-t=0.
```

The printed HP convergence and average-colour-class application are written
for:

```text
i_0 in {1,2}.
```

Thus the required extension is the endpoint `i_0=0` threshold-location
argument.  The current proof-grade subtargets are recorded in:

```text
upper-boundary-alpha-average-colour-class-theorem-2026-05-13.md
```

as:

```text
A0. endpoint convergence for i_0=0;
A1. threshold bracketing around rho=alpha_0-1-2/ln 2;
A2. transfer from L_0 to E via improved approximation.
```

This is a first-moment threshold-location statement only.  It does not use
tame profiles, second moments, lower-boundbeta, or profile realizability.

## Status

`U8a` is not closed yet.

The blocker is now narrower than before: it is not the HR derivative and not
the improved approximation.  It is the missing endpoint `i_0=0`
threshold-location input that lets the general derivative lemma be applied at
`k in {boldk_alpha-2,boldk_alpha-1}`.
