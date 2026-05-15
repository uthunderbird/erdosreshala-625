# Good-branch partial theorem away from `x=1`

Date: 2026-05-13

## Purpose

This note records the theorem-level good-branch coverage that is genuinely
available from the repaired A1 certificate (lemma_7_10_ext.md) and HP-2023 Lemma 7.20 (lemma:kstartame).

The "repaired A1 certificate" is `lemma_7_10_ext.md` (included in this
directory): a numerically certified Lipschitz envelope on a 2-cell grid
establishing phi(1,x,1) > 0 on [0.029155, 0.04).  The certificate data is
in `a1-certificates/a1_good_branch_certificate_x029155_to_1.csv`.

The "old HP/Heckel source theorem" is HP-2023 Lemma 7.20 (`lemma:kstartame`,
TameColourings.tex), which gives chi(G)-zeta(G)->infinity whp when
mu_alpha >= n^{1.05}, i.e. x >= 0.05 (generously).  For x in [0.04, 1-epsilon_0]
the lemma applies directly.  For x in [0.029155, 0.04) the A1 certificate
provides the phi-positivity input that substitutes for the n^{1.05} condition.

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

HP-2023 Lemma 7.20 (`lemma:kstartame`, TameColourings.tex) supplies the
good-branch gap result for `x >= 0.04` (where mu_alpha >= n^{1.05} holds
and the lemma's condition is satisfied).

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
