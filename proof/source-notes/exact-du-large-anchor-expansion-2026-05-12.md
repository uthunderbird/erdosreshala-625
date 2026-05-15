# Exact finite-`d_u` large-anchor expansion

Date: 2026-05-12

## Purpose

This note supplies the analytic bridge needed by

```text
p3-exact-du-standard-anchor-reduction-2026-05-12.md
```

It expands the exact centered finite-`d_u` objective for large anchor
parameter `A` and identifies the uniform error terms.

## Definitions

Let:

```text
d_u = 2^{u(u-1)/2} Gamma(u+1),
L_A(i) = -log d_{A-i},
H_A(i)=L_A(i)-L_A(0)-i(L_A(1)-L_A(0)).
```

The affine subtraction makes `H_A(0)=H_A(1)=0`.

For integer `u`, `Gamma(u+1)=u!`.

## Exact quadratic part

The edge-density part is exact:

```text
- (log 2)/2 * (A-i)(A-i-1).
```

After subtracting the affine interpolation through `i=0,1`, this contributes:

```text
-(log 2)/2 * i(i-1).
```

Thus the finite-centered quadratic has the same sign/shape as the limiting
deficit objective.

## Factorial/Gamma part

Let:

```text
G_A(i) = -log Gamma(A-i+1).
```

Then:

```text
H_A(i) = -(log 2)/2 i(i-1)
       + [G_A(i)-G_A(0)-i(G_A(1)-G_A(0))].
```

For integer `A` and integer `i>=0`, the centered factorial term is exact:

```text
G_A(i)-G_A(0)-i(G_A(1)-G_A(0))
 = -log((A-i)!/A!) - i log A
 = log(A(A-1)...(A-i+1)) - i log A
 = sum_{j=0}^{i-1} log(1-j/A).
```

The `j=0` term is zero, so:

```text
F_A(i):=sum_{j=1}^{i-1} log(1-j/A).
```

Therefore:

```text
H_A(i)=-(log 2)/2 i(i-1)+F_A(i).
```

## Uniform bound

If `0<=i<=A/2`, then:

```text
0 >= F_A(i) >= -2/A * sum_{j=1}^{i-1} j
             = -i(i-1)/A.
```

This uses:

```text
log(1-y) >= -2y, 0<=y<=1/2.
```

Consequently:

```text
|H_A(i)+(log 2)/2 i(i-1)| <= i(i-1)/A
```

uniformly on `i<=A/2`.

## Tail-local uniformity

The active exact-`d_u` profiles have Gaussian deficit tails because the
dominant term is:

```text
-(log 2)/2 i(i-1).
```

For any fixed `B>0`, choose `I=I(B)` such that the profile mass and first
moment beyond `I` are at most `B^{-1}` uniformly in:

```text
x in [0,x0],
r in {2,3},
A>=2I.
```

On the finite range `i<=I`, the bound above gives:

```text
sup_{i<=I} |H_A(i)+(log 2)/2 i(i-1)| <= I^2/A.
```

Thus the exact finite profile and the limiting profile converge uniformly
as `A->infinity`, after controlling the Gaussian tail.

## Consequence for room and prefix margins

Let the limiting `r=2,3` certificates have margins:

```text
Room_r(x) >= R_r>0,
Prefix_{r,delta}(x) >= c_{r,delta}>0.
```

Uniform convergence of:

```text
weights,
normalizing constants,
mean-solver mu,
objectives,
prefix Phi values
```

on compact `x in [0,x0]` implies there exists `A0` such that for all
`A>=A0`:

```text
Room_A^{(r)}(x) >= R_r/2,
Prefix_A^{(r)}(x) >= c_{r,delta}/2.
```

This is the large-anchor stability theorem needed by G4.

## Remaining rigor obligations

The proof above still needs two standard compactness details in final form:

```text
1. uniform lower bound on variance of the limiting tilted distribution,
   so the mean-solver mu depends Lipschitz-continuously on the perturbation;
2. uniform Gaussian tail bound for the relevant mu range.
```

Both are finite-dimensional/elementary once `x in [0,x0]` and
`r in {2,3}` are fixed.

They are isolated in:

```text
exact-du-large-anchor-compactness-lemmas-2026-05-12.md
```

## Status

This note gives the correct large-anchor expansion and a clear route to
turn finite exact-`d_u` scans into an asymptotic theorem.  G4 is still open
until the compactness/tail details are written as a finished lemma and the
limiting margins are supplied by an interval certificate.
