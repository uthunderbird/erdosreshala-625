# Good-branch partial theorem away from `x=1`

Date: 2026-05-13

## Purpose

This note records the theorem-level good-branch coverage that is genuinely
available from the repaired A1 package and the old HP/Heckel source theorem.

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

The repaired A1 certificate supplies the lower-boundbeta positivity input on
the handoff interval:

```text
0.029155 <= x <= 0.04,
```

and the original HP/Heckel source proof supplies it for `x>=0.04`.

The source-window verification above gives the old source theorem's upper
hypothesis uniformly on the fixed-away-from-one range.  The old theorem then
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
