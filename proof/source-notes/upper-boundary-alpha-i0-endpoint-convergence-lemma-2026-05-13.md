# Upper-boundary alpha i0 endpoint convergence lemma

Date: 2026-05-13

## Purpose

This note closes subtarget `A0` from:

```text
upper-boundary-alpha-average-colour-class-theorem-2026-05-13.md
```

It extends the HP convergence lemma for the Lagrange-multiplier optimizer
from:

```text
i_0 in {1,2}
```

to the alpha-anchor endpoint:

```text
i_0=0.
```

## Setup

Let:

```text
t=alpha,
rho=n/k,
i=alpha-u.
```

Assume:

```text
rho = alpha_0 - 1 - 2/ln 2 + o(1).
```

Equivalently:

```text
alpha-rho = 1 + 2/ln 2 - x + o(1),
x = alpha_0-alpha.
```

The continuous optimizer of `L_0(n,k,alpha)` has deficit weights:

```text
xi_i = exp(h_n(i)+lambda_n+mu_n i),
0 <= i <= alpha-1,
```

with:

```text
sum_{i=0}^{alpha-1} xi_i = 1,
sum_{i=0}^{alpha-1} i xi_i = alpha-rho.
```

Define the limiting endpoint profile by:

```text
zeta_i = exp(lambda+mu i-(ln 2)i^2/2),
i >= 0,
```

where:

```text
sum_{i>=0} zeta_i = 1,
sum_{i>=0} i zeta_i = T(x),
T(x)=1+2/ln 2-x.
```

## Lemma

Under the setup above:

```text
lambda_n -> lambda,
mu_n -> mu,
sum_{i>=0} |xi_i-zeta_i| -> 0.
```

The convergence is uniform for `x` in any compact subinterval of `[0,1]`,
and in particular for the upper-boundary interval `[0.95,1]`.

## Proof

The proof is the same compactness argument used in HP Lemma
`convergencemulambda`, with the lower endpoint changed from `i_0=1` or
`i_0=2` to `i_0=0`.

First, the HR/HP preliminary bound `mubound` applies whenever:

```text
t=alpha_0-O(1),
rho=t-Theta(1).
```

Here:

```text
t=alpha=alpha_0-O(1),
rho=alpha_0-1-2/ln 2+o(1)=alpha-Theta(1),
```

so:

```text
lambda_n=O(1),
mu_n=O(1).
```

Second, HP's asymptotic for `h_n(i)` gives, uniformly for bounded `i` and
with Gaussian domination for large `i`,

```text
h_n(i)=-(ln 2)i^2/2+o(1).
```

This includes the new endpoint `i=0`; indeed:

```text
h_n(0)=o(1).
```

Using the constraints defining `lambda_n,mu_n`, we therefore get:

```text
sum_{i>=0} exp(lambda_n+mu_n i-(ln 2)i^2/2) = 1+o(1),
sum_{i>=0} i exp(lambda_n+mu_n i-(ln 2)i^2/2) = T(x)+o(1).
```

Any subsequential limit of `(lambda_n,mu_n)` solves the limiting two-equation
system for `(lambda,mu)`.  The limiting system has a unique solution because,
after normalization, the mean

```text
M(mu)=
  sum_{i>=0} i exp(mu i-(ln 2)i^2/2)
  / sum_{i>=0} exp(mu i-(ln 2)i^2/2)
```

is strictly increasing in `mu`.  Therefore:

```text
lambda_n -> lambda,
mu_n -> mu.
```

Finally, total-variation convergence follows by splitting the sum into:

```text
0 <= i <= M,
i > M.
```

For fixed `M`, pointwise convergence gives:

```text
sum_{0<=i<=M}|xi_i-zeta_i| -> 0.
```

For the tail, `lambda_n,mu_n=O(1)` and the quadratic term
`-(ln 2)i^2/2` give a uniform bound:

```text
xi_i+zeta_i <= exp(-c i^2)
```

for all sufficiently large `i`.  Letting `M -> infinity` proves:

```text
sum_{i>=0}|xi_i-zeta_i| -> 0.
```

## Consequence

The endpoint `i_0=0` creates no convergence obstruction.  The remaining
content of the alpha-anchor average-colour-class theorem is not convergence
but threshold bracketing:

```text
L_0(n,k_-,alpha) <= -c_epsilon n/log n,
L_0(n,k_+,alpha) >=  c_epsilon n/log n.
```

That is subtarget `A1`.

## Status

`A0` is closed modulo citation of the same HP preliminary lemmas:

```text
mubound,
hasymp,
continuous optimizer formula.
```

`A1` remains open.
