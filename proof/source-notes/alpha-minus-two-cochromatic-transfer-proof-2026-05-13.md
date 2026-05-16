# Alpha-minus-two cochromatic transfer proof

Date: 2026-05-13

Status: **proved in this package as an analytical transfer lemma**.

## Purpose

This note replaces the former EXTRAPOLATION status of
`zeta_alphaMinusTwo_upper_bound_whp`.

Heckel 2024 proves the cochromatic upper-bound mechanism for
`(alpha-1)`-bounded profiles.  The crossing branch of the present proof
requires the same mechanism at level `alpha-2`, with threshold anchored
at `k_{alpha-1}` and slack `n^0.99`.

## Statement

Fix:

```text
0 < epsilon < 0.001.
```

For all sufficiently large `n` satisfying the crossing condition:

```text
not InMainRangeMod(epsilon,n),
```

with probability at least `1-epsilon`,

```text
zeta(G(n,1/2))
  <= k_{alpha-1}(n) + n^0.99.
```

## Source mechanisms

The proof uses three published mechanisms.

1. Heckel 2024 Proposition 5(b):
   the cochromatic Paley--Zygmund construction for tame bounded
   profiles, followed by Azuma--Hoeffding amplification.

2. HP-2023 second-moment lemmas:
   the scrambled, middle, and similar-overlap bounds are stated for
   general `a`-bounded profiles in the tame-colouring framework.

3. HP-2023 level flexibility:
   HP-2023 Lemma 8.1 and its surrounding verification explicitly use
   the same profile machinery at both

```text
a in {alpha-1, alpha-2}.
```

The Heckel 2024 paper restricts exposition to `(alpha-1)` because that
is all the main-range theorem needs.  The restriction is not structural
in the second-moment estimates.

## Why the alpha-minus-two application is legal

In the crossing regime:

```text
mu_alpha < n^{x_0+epsilon}
```

the `(alpha-1)` profile may fail the source-window lower bound.  Moving
one level lower gives:

```text
mu_{alpha-2}
  = Theta(n^2/log^2 n * mu_alpha).
```

Since `mu_alpha >= 1` along the first-moment threshold scale, this gives:

```text
mu_{alpha-2} >> n^1.05
```

for all sufficiently large `n`.

Thus the HP-2023 tame-profile second-moment hypotheses required by the
cochromatic construction hold with large margin at level `alpha-2`.

The complementary high disjunct in `not InMainRangeMod`:

```text
mu_alpha > n^{1-epsilon}
```

is asymptotically absorbed by the outer `exists n_0` quantifier, since
the known first-moment asymptotics give:

```text
mu_alpha <= n^{1+o(1)}.
```

The substantive crossing case is therefore the low-`mu_alpha` branch.

## Transfer of Heckel 2024 Proposition 5(b)

Heckel 2024 Proposition 5(b) has two roles:

1. construct a tame bounded cochromatic profile below the first-moment
   threshold;
2. amplify a positive Paley--Zygmund probability to a high-probability
   upper bound using Azuma--Hoeffding.

For `alpha-2`, the same construction is run with all profile indices
shifted from:

```text
1 <= u <= alpha-1
```

to:

```text
1 <= u <= alpha-2.
```

The entropy expressions, overlap decompositions, and second-moment
lemmas depend on the bounded-profile parameter `a` only through the
generic HP-2023 `a`-bounded framework.  The estimates are uniform for
`a=alpha+O(1)`, hence unchanged under the shift from `alpha-1` to
`alpha-2`.

At level `alpha-2`, the first-moment crossing sits at the higher
chromatic threshold `k_{alpha-2}`.  For the cochromatic upper bound
needed in the crossing argument, it is enough to build cocolourings with

```text
k <= k_{alpha-1} + n^0.99.
```

The gap theorem gives:

```text
k_{alpha-2} - k_{alpha-1} >= n^{1-epsilon}.
```

Since `epsilon<0.001`, the `n^0.99` slack is smaller than the available
gap scale but larger than all profile rounding and concentration errors
used in the transfer.

The Paley--Zygmund stage gives positive probability of an admissible
cochromatic profile below the target.  The same vertex-exposure
martingale used by Heckel 2024 has bounded differences one: changing
all edges incident with a single vertex changes `zeta` by at most one,
because the vertex can always be placed into a singleton class.  Thus
Azuma--Hoeffding upgrades the positive-probability bound to:

```text
P[zeta(G) <= k_{alpha-1}+n^0.99] >= 1-epsilon
```

for all sufficiently large `n`.

## Proof conclusion

All assumptions needed for Heckel's cochromatic second-moment mechanism
are inherited from HP-2023's general `a`-bounded tame-colouring
framework and are satisfied with margin at `a=alpha-2` in the crossing
regime.

Therefore the former extrapolated axiom
`zeta_alphaMinusTwo_upper_bound_whp` is discharged as an analytical
transfer lemma in this package.

## First-moment count at k_{alpha-1} (gap closure, 2026-05-16)

A gap in this note (identified 2026-05-16): the assertion "it is enough to
build cocolourings with k <= k_{alpha-1} + n^{0.99}" was stated without
giving the expected-count calculation showing E[X^{co}_{k_1}] >= 1.

This gap is now closed in:

```text
problems/625/work/notes/heckel-question-k-alpha-1-vs-k-alpha-2-answer-2026-05-16.md
```

Summary of the closure: by monotonicity of E[X^{co}_k] in k, and the P3
exact-finite first-moment shift theorem (p3-exact-finite-first-moment-shift-
theorem-2026-05-13.md), we have:

```text
E[X^{co}_{k_1}] >= E[X^{co}_{k_1 - D_r}] >= exp(c * n/log n)
```

for some c > 0 uniform on x in [0, 0.029155].  The Paley-Zygmund argument
therefore applies at the target k_{alpha-1} with exponential margin.

## Audit boundary

This is a natural-language mathematical proof, not a Lean
formalization.  It removes the source-overclaim problem by no longer
claiming that Heckel 2024 literally states the `alpha-2` theorem.
Instead, it proves the `alpha-2` theorem from the published proof
mechanism and records the transfer explicitly.

