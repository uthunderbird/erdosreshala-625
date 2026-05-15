# Upper-boundary alpha-anchor ordinary lower-bound target

Date: 2026-05-13

## Purpose

This note isolates U7 from:

```text
upper-boundary-alpha-anchor-r1-certificate-theorem-2026-05-13.md
```

U7 is the ordinary lower-bound side needed for the upper-boundary
`alpha`-anchor route.

## Target

Prove, uniformly for the upper-boundary terminal interval:

```text
x in [x_1,1),
```

that whp:

```text
chi(G) >= boldk_alpha(n)-o(n/log^3 n).
```

It is enough to prove the two statements:

```text
1. chi_alpha(G) >= boldk_alpha(n)-1 whp;
2. chi(G) >= chi_alpha(G)-o(n/log^3 n) whp.
```

## U7.1 alpha-bounded first-moment lower bound

HP-2023 proves in the proof of Theorem `announcedbounds` a lemma labelled
`lowerbound`:

```text
For p=1/2 and a in {alpha(n)-2, alpha(n)-1}, whp,
chi_a(G_{n,1/2}) >= boldk_a-1.
```

The proof is first-moment only:

```text
by definition of the first-moment threshold,
E_{n,boldk_a-1,a}<1,
and one-more-colour / approximation lemmas push lower k even further below
threshold.
```

For the alpha-anchor route we need the same statement with:

```text
a=alpha.
```

### Required source check

Verify that the first-moment threshold definition and the approximation
lemmas used in `lowerbound` apply to `a=alpha`, not only to
`a in {alpha-2,alpha-1}`.

If yes, U7.1 is source-backed.

If no, prove the Markov bound directly from the definition of
`boldk_alpha`:

```text
E[number of alpha-bounded colourings with <= boldk_alpha-1 colours] -> 0.
```

This should be significantly easier than the upper-bound side because it is
only a first-moment nonexistence statement.

The precise remaining sublemma is isolated in:

```text
upper-boundary-alpha-first-moment-lowerbound-sublemma-2026-05-13.md
```

It is not enough to know `E_{n,boldk_alpha-1,alpha}<1`; we need:

```text
E_{n,boldk_alpha-2,alpha}->0.
```

This follows from a local one-colour threshold slope at `a=alpha`, if the
HP/HR `L_0` derivative estimates extend to this anchor.

## U7.2 transfer from chi_alpha to ordinary chi

For transfer from `chi_alpha` to `chi`, it suffices to hit all independent
sets of size `alpha+1`.  Deleting one vertex from each such set gives:

```text
chi_alpha(G) <= chi(G) + X_{alpha+1}(G),
```

where `X_{alpha+1}` is the number of independent sets of size `alpha+1`.

Therefore:

```text
chi(G) >= chi_alpha(G)-X_{alpha+1}(G).
```

The ratio calculation gives:

```text
mu_{alpha+1}
  = mu_alpha * Theta(log n/n).
```

On the upper-boundary terminal interval:

```text
mu_alpha <= n * exp(O((log log n)^2)),
```

hence:

```text
mu_{alpha+1}
  <= log n * exp(O((log log n)^2))
  = n^{o(1)}.
```

By Markov, for any fixed `eta>0`:

```text
X_{alpha+1}(G) <= n^eta
```

whp.  Since:

```text
n^eta = o(n/log^3 n)
```

for every fixed `eta<1`, U7.2 follows.

## Resulting theorem

Assuming U7.1, we get:

```text
chi(G)
  >= chi_alpha(G)-X_{alpha+1}(G)
  >= boldk_alpha-1-n^eta
  = boldk_alpha-o(n/log^3 n)
```

whp.

## Status

U7.2 is closed in:

```text
upper-boundary-alpha-to-ordinary-transfer-u8b-closure-2026-05-13.md
```

U7.1 is closed in:

```text
upper-boundary-alpha-lower-bound-u8a-closure-2026-05-13.md
```

The source/development chain is:

```text
upper-boundary-alpha-one-more-colour-source-check-2026-05-13.md
upper-boundary-alpha-average-colour-class-theorem-2026-05-13.md
upper-boundary-alpha-first-moment-slope-theorem-2026-05-13.md
```

The HR derivative and HP improved approximation are source-backed at
`t=alpha`; HR Lemma `k*` also supplies the required alpha-anchor
threshold-location estimate:

```text
n / boldk_alpha = alpha_0 - 1 - 2/ln 2 + o(1).
```

Thus the ordinary lower-bound side is closed:

```text
chi(G) >= boldk_alpha-o(n/log^3 n)
```

whp in the upper-boundary interval.
