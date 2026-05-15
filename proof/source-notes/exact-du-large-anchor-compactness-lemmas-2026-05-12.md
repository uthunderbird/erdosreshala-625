# Exact-`d_u` large-anchor compactness lemmas

Date: 2026-05-12

## Purpose

This note fills the two compactness gaps left by:

```text
exact-du-large-anchor-expansion-2026-05-12.md
```

for the active standard route:

```text
x in [0,x0],
r in {2,3}.
```

## Limiting weights

For `r in {2,3}`, define:

```text
w_i(mu)=exp(mu i-a2 i(i-1)),     i>=r,
a2=log(2)/2.
```

The shifted quadratic `i(i-1)` is equivalent to the earlier `i^2`
normalization up to an affine term, which is absorbed by the mean-solver
parameter `mu`.

Let:

```text
Z_r(mu)=sum_{i>=r} w_i(mu),
M_r(mu)=sum_{i>=r} i w_i(mu),
m_r(mu)=M_r(mu)/Z_r(mu).
```

The target mean range is:

```text
T(x)=1+2/log2-x,
x in [0,x0].
```

This is a compact interval:

```text
T_* <= T(x) <= T^*
```

with `T_*>1`.

## Lemma 1: uniform mu bracket

For each `r in {2,3}`, there exists `B_r<infinity` such that the unique
solution of:

```text
m_r(mu)=T(x)
```

lies in:

```text
[-B_r,B_r]
```

uniformly for `x in [0,x0]`.

### Proof

The function `m_r(mu)` is continuous and strictly increasing because:

```text
m_r'(mu)=Var_mu(i)>0.
```

As `mu->-infinity`, `m_r(mu)->r`.  As `mu->+infinity`,
`m_r(mu)->infinity`, since the Gaussian tail shifts to larger `i`.

Numerically and symbolically:

```text
T(x) >= T(x0)=1+2/log2-x0 > 3.85.
```

Thus `T_* > 3`, so the target mean lies strictly above the support lower
endpoint for both active cases `r=2` and `r=3`.  The monotone equation is
therefore solvable in the stated convention.

## Lemma 2: uniform variance lower bound

Once `mu in [-B_r,B_r]`, there is `v_r>0` such that:

```text
Var_mu(i) >= v_r
```

for all `mu in [-B_r,B_r]`.

### Proof

For each fixed `mu`, the distribution has positive mass on at least two
indices, so variance is positive.  Variance is continuous in `mu`, and the
interval `[-B_r,B_r]` is compact.  Hence it has a positive minimum.

For a certificate proof, one can lower-bound explicitly using the first two
support points:

```text
Var(i) >= p_r p_{r+1}.
```

Both probabilities have uniform positive lower bounds on `[-B_r,B_r]`.

## Lemma 3: uniform Gaussian tail

For each `B` and `r in {2,3}`, there are constants `C,c>0` such that for
all `mu in [-B,B]`:

```text
sum_{i>I} exp(mu i-a2 i(i-1)) <= C exp(-c I^2),
sum_{i>I} i exp(mu i-a2 i(i-1)) <= C exp(-c I^2).
```

### Proof

For `i>=I`:

```text
mu i-a2 i(i-1) <= B i-a2 i(i-1)
              <= -(a2/2)i^2
```

once `i>=I0(B)`.  The remaining Gaussian tail is bounded by a geometric
tail because the ratio of consecutive terms is eventually at most `1/2`.

## Lemma 4: finite-`A` mean solver stability

Let `H_A(i)` be the exact centered finite-`d_u` exponent and let `m_{A,r}`
be the corresponding mean function.  For every epsilon `eps>0`, there is
`A0` such that for all `A>=A0`:

```text
sup_{mu in [-B_r,B_r]} |m_{A,r}(mu)-m_r(mu)| <= eps.
```

Using Lemma 2, the inverse solutions satisfy:

```text
|mu_{A,r}(x)-mu_r(x)| <= eps/v_r + o(eps)
```

uniformly in `x`.

### Proof

Use:

```text
H_A(i)=H_infty(i)+O(i^2/A)
```

on `i<=I`, and Lemma 3 for the tail `i>I`.  First choose `I`, then choose
`A` so large that `I^2/A` is small.

## Lemma 5: room and prefix stability

The exact finite-`A` profiles converge uniformly to the limiting profiles
in:

```text
total variation,
first moment,
entropy objective,
all finitely enumerated prefix Phi endpoints.
```

Therefore positive limiting margins imply positive exact finite-`A`
margins for all sufficiently large `A`.

## Index audit warning

The scripts use a one-index convention where `T(x)=1+2/log2-x` and support
`r=2,3` were numerically feasible.  In the final proof, one must state the
deficit coordinate convention so that the support lower endpoint and target
mean are compatible.  This is a notation issue, not a numerical obstruction,
but it must be fixed before publication.

## Status

These compactness lemmas complete the analytic transfer strategy from a
limiting interval certificate to exact finite-`d_u` margins for all large
anchors.  G4 still needs the actual limiting interval certificate and a
cleaned index convention.

The limiting certificate target is:

```text
p3-r23-limiting-certificate-theorem-2026-05-12.md
```
