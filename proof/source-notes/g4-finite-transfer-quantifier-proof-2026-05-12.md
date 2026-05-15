# G4 finite-transfer quantifier proof

Date: 2026-05-12

## Purpose

This note replaces the vague phrase "compactness transfer" by an explicit
quantifier-level proof skeleton for the finite-`d_u` transfer used in G4.

It does not introduce new numerics.  It explains exactly why positive
limiting certificate margins transfer to exact finite-anchor profiles once
the elementary perturbation bounds below are accepted.

## Setup

Fix:

```text
x in [0,0.029155],
r in {2,3}.
```

Let the limiting exponent be:

```text
h(i)=-(log 2)/2 * i(i-1).
```

Let the exact finite-anchor exponent be:

```text
h_A(i)=h(i)+F_A(i),
F_A(i)=sum_{j=1}^{i-1} log(1-j/A).
```

For `i<=A/2`:

```text
0 >= F_A(i) >= -i(i-1)/A.
```

Let:

```text
w_mu(i)=exp(mu*i+h(i)),
w_A,mu(i)=exp(mu*i+h_A(i)).
```

The mean targets are:

```text
T(x)=1+2/log(2)-x.
```

## Theorem

For each certified limiting margin set:

```text
Room_r(x) >= R_r > 0,
Prefix_r(x) >= c_r > 0,
```

there is `A0` such that for all `A>=A0`, all
`x in [0,0.029155]`, and `r in {2,3}`:

```text
Room_A,r(x) >= R_r/2,
Prefix_A,r(x) >= c_r/2.
```

In particular, using the accepted extended certificate:

```text
R_2 >= 0.2052464934...,
R_3 >= 0.0477897229...,
c_2 >= 0.0034155683...,
c_3 >= 0.0068813043...,
```

the conservative exact constants:

```text
R_2^exact = 0.1,
R_3^exact = 0.02,
c_2^exact = 0.001,
c_3^exact = 0.003
```

are valid after increasing `A0`.

## Proof with explicit quantifiers

### Step 1: choose a uniform limiting mu bracket

The limiting mean map:

```text
m_r(mu)=sum_i i w_mu(i)/sum_i w_mu(i)
```

is continuous and strictly increasing, because:

```text
m_r'(mu)=Var_mu(i)>0.
```

The target interval:

```text
T([0,0.029155])
```

is compact and lies strictly inside the range of `m_r` for each `r in {2,3}`.
Therefore choose finite numbers:

```text
B>0,
eta_T>0
```

such that:

```text
m_r(-B) <= min_x T(x)-eta_T,
m_r( B) >= max_x T(x)+eta_T
```

for both `r=2,3`.

### Step 2: choose a uniform variance lower bound

On the compact set:

```text
mu in [-B,B],
r in {2,3},
```

the limiting variance is continuous and positive.  Hence choose:

```text
v>0
```

such that:

```text
Var_{r,mu}(i) >= v.
```

Equivalently, one may use the explicit two-point lower bound:

```text
Var(i) >= p_r p_{r+1},
```

with `p_r,p_{r+1}` bounded below uniformly on `[-B,B]`.

### Step 3: choose a Gaussian tail cutoff

For every `epsilon>0`, choose `I` so large that, uniformly for:

```text
r in {2,3},
mu in [-B-1,B+1],
```

the limiting tails satisfy:

```text
sum_{i>I} w_mu(i) <= epsilon,
sum_{i>I} i w_mu(i) <= epsilon,
sum_{i>I} i^2 w_mu(i) <= epsilon.
```

This follows because:

```text
mu*i-(log2/2)i(i-1) <= -(log2/4)i^2
```

for all sufficiently large `i`, uniformly over bounded `mu`.

### Step 4: choose A0 after I

After `I` is fixed, choose `A0>=2I` such that for all `A>=A0` and all
`i<=I`:

```text
|F_A(i)| <= epsilon.
```

This follows from:

```text
|F_A(i)| <= i(i-1)/A <= I^2/A.
```

Then the finite and limiting weights differ by a relative factor:

```text
exp(-epsilon) <= w_A,mu(i)/w_mu(i) <= 1
```

for every `i<=I`.

The tail for finite weights is no larger than the limiting tail for the same
`mu`, since `F_A(i)<=0`.

### Step 5: uniform convergence of means

Steps 3 and 4 imply:

```text
sup_{r,mu in [-B,B]} |m_A,r(mu)-m_r(mu)| <= C epsilon.
```

Choose `epsilon` so small that:

```text
C epsilon < eta_T/2.
```

Then the finite mean solver remains inside `[-B,B]`.

Using the variance lower bound and monotonicity:

```text
|mu_A,r(x)-mu_r(x)| <= C epsilon / v + o(epsilon)
```

uniformly for:

```text
x in [0,0.029155],
r in {2,3}.
```

### Step 6: uniform convergence of probabilities

The weight convergence on `[r,I]`, tail control beyond `I`, and uniform
solver convergence imply:

```text
sum_i |p_A,r,x(i)-p_r,x(i)| <= C' epsilon.
```

The same argument controls first moments and all finitely many clipped-prefix
endpoint masses used by the certificate table.

### Step 7: uniform convergence of room and prefix functionals

The room functional is a finite combination of:

```text
log partition function,
mu*T(x),
linear/quadratic objective terms.
```

The prefix functional is a continuous entropy/linear functional on the
compact set of prefix endpoint masses bounded away from the singular boundary
by the accepted certificate's tail and prefix checks.

Therefore:

```text
sup_{x,r} |Room_A,r(x)-Room_r(x)| <= C'' epsilon,
sup_{x,r} |Prefix_A,r(x)-Prefix_r(x)| <= C'' epsilon.
```

Choose `epsilon` so that both errors are smaller than:

```text
min(R_2,R_3,c_2,c_3)/2.
```

This proves the theorem.

## Remaining publication obligation

This note is a proof-grade quantifier skeleton, but it still uses named
constants:

```text
C, C', C'', B, v, eta_T.
```

For a fully self-contained paper, either:

```text
1. give explicit formulas/bounds for these constants, or
2. state the compactness lemmas as conventional analytical lemmas and prove
   them in prose using the steps above.
```

The argument is now localized to elementary continuity, monotonicity, and
Gaussian tail estimates; it no longer relies on an unexplained compactness
black box.

