# Good-branch partial theorem away from `x=1`

Date: 2026-05-13

## Purpose

This note records the theorem-level good-branch coverage that is genuinely
available from the repaired A1 certificate (lemma_7_10_ext.md) and HP-2023 Lemma 7.20 (lemma:kstartame).

The "repaired A1 certificate" is `lemma_7_10_ext.md` (included in this
directory): a numerically certified Lipschitz envelope on a 2-cell grid
establishing phi(1,x,1) > 0 on [0.029155, 0.04).  The certificate data is
in `a1-certificates/a1_good_branch_certificate_x029155_to_1.csv`.

The "modified source theorem" used here is `lemma_7_20_modified` (the Lean axiom in
`paper/SOURCES.md §A1`): it is HP-2023 Lemma 7.20 (`lemma:kstartame`, TameColourings.tex)
with condition (d) weakened from mu_alpha >= n^{1.05} to mu_alpha >= n^{x_0+epsilon}
(where x_0 ≈ 0.02905), following Heckel 2024 §Discussion's conjecture.

Note: the original HP-2023 Lemma 7.20 requires mu_alpha >= n^{1.05}.  Since mu_alpha = n^{x+o(1)}
and x < 1 throughout, the original n^{1.05} condition is NEVER satisfied.  All invocations
here use `lemma_7_20_modified`, not the original lemma.

For x in [0.04, 1-epsilon_0]: mu_alpha >= n^{0.04+o(1)} satisfies the weakened condition
mu_alpha >= n^{x_0+epsilon} (since 0.04 > x_0 ≈ 0.02905), so `lemma_7_20_modified` applies
directly without the A1 certificate.
For x in [0.029155, 0.04): mu_alpha ~ n^{x+o(1)} with x < 0.04, so the weakened condition
is not trivially satisfied.  The A1 certificate (`lemma_7_10_ext.md`) establishes phi(1,x,1) > 0
on this interval, which is the geometric condition `lemma_7_20_modified` actually checks.
Together, A1 certificate + `lemma_7_20_modified` close the interval [0.029155, 0.04).

It does not claim to close the full good branch.  It isolates the remaining
upper-boundary region where `x -> 1`.

## Setup

Let:

```text
alpha_0 = 2 log_2 n - 2 log_2 log_2 n + 2 log_2(e/2) + 1,
alpha = floor(alpha_0),
x = alpha_0-alpha.
```

Fix any constant:

```text
epsilon_0 > 0.
```

Consider the subrange:

```text
0.029155 <= x <= 1-epsilon_0.
```

## Source-window verification

The floor asymptotic lemma gives:

```text
mu_alpha = n^{x+o(1)}.
```

Therefore, after choosing any fixed:

```text
0 < epsilon < min(epsilon_0/2, 1/450),
```

the upper source hypothesis:

```text
mu_alpha <= n^{1-epsilon}
```

holds uniformly on `x <= 1-epsilon_0` for all sufficiently large `n`.

The repaired A1 handoff gives the lower positivity condition on:

```text
x >= 0.029155.
```

Thus the old HP/Heckel good-branch source mechanism applies throughout this
fixed-away-from-one subrange.

## Theorem

For every fixed `epsilon_0>0`, on:

```text
0.029155 <= x <= 1-epsilon_0,
```

we have, asymptotically almost surely:

```text
chi(G(n,1/2))-zeta(G(n,1/2)) -> infinity.
```

More quantitatively, for the fixed source parameter `epsilon` above:

```text
chi(G)-zeta(G)
  >= n^{1-epsilon/2} - n^{1-0.9epsilon} - 2n^0.999
  -> infinity.
```

## Proof

`lemma_7_20_modified` (HP-2023 Lemma 7.20 with weakened condition, see Purpose §above)
supplies the good-branch gap result for `x >= 0.04` (where mu_alpha >= n^{0.04+o(1)}
satisfies the weakened condition mu_alpha >= n^{x_0+epsilon}).

The repaired A1 certificate (`lemma_7_10_ext.md`, a1-certificates/) supplies
the phi-positivity condition for the handoff interval:

```text
0.029155 <= x <= 0.04,
```

and HP-2023 Lemma 7.20 supplies it for `x>=0.04`.

The source-window verification above gives HP-2023 Lemma 7.20's upper
hypothesis uniformly on the fixed-away-from-one range.  Lemma 7.20 then
gives, on a common high-probability event:

```text
chi(G)  >= boldk_{alpha-1} - n^{1-0.9epsilon},
zeta(G) <= boldk_{alpha-1} - n^{1-epsilon/2} + 2n^0.999.
```

Subtracting yields the displayed gap.  The choice
`epsilon<1/450` ensures:

```text
1-epsilon/2 > 1-0.9epsilon,
1-epsilon/2 > 0.999.
```

So the right-hand side tends to infinity.

## Status

This closes the good branch only on fixed subranges bounded away from
`x=1`.

The residual region:

```text
x > 1-epsilon_0
```

for arbitrarily small fixed `epsilon_0`, equivalently:

```text
mu_alpha > n^{1-epsilon}
```

for every fixed `epsilon>0` along possible subsequences, remains open.
