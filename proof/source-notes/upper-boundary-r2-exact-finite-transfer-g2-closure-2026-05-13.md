# Upper-boundary r=2 exact finite transfer G2 closure

Date: 2026-05-13

## Purpose

This note closes `R2-G2` for the upper-boundary alpha-anchor `r=2` route,
conditional on the limiting interval certificate `R2-G1`.

It adapts the exact finite large-anchor transfer pipeline from the previous
G4/P3 work to:

```text
anchor A=alpha,
support i>=2,
x in [0.95,1].
```

## Source pipeline

The transfer uses:

```text
exact-du-large-anchor-expansion-2026-05-12.md
exact-du-large-anchor-compactness-lemmas-2026-05-12.md
g4-finite-transfer-publication-closure-2026-05-12.md
p3-exact-finite-normalization-bridge-theorem-2026-05-13.md
```

The G4 publication closure states the general principle:

```text
positive limiting margins survive exact finite-anchor perturbations for all
sufficiently large anchors.
```

Although the earlier application used:

```text
x in [0,0.029155],
anchor A=alpha-1,
r in {2,3},
```

the proof method is compactness plus large-anchor perturbation.  It applies
unchanged to any fixed compact `x`-interval and finite support-start set,
provided the limiting certificate has positive margins.

## Exact finite objective at anchor alpha

Let:

```text
A=alpha,
u=A-i.
```

The exact finite profile exponent uses:

```text
d_u=2^{u(u-1)/2}u!.
```

Define:

```text
L_A(i)=-log d_{A-i},
H_A(i)=L_A(i)-L_A(0)-i(L_A(1)-L_A(0)).
```

Then, exactly:

```text
H_A(i)=-(log 2)/2 i(i-1)+F_A(i),
F_A(i)=sum_{j=1}^{i-1} log(1-j/A).
```

For:

```text
0<=i<=A/2,
```

we have:

```text
|F_A(i)| <= i(i-1)/A.
```

Thus on every fixed or Gaussian-tail active window:

```text
H_A(i)=-(log 2)/2 i(i-1)+o(1)
```

uniformly as:

```text
A -> infinity.
```

The limiting objective used in the scan can be written with `-A i^2` instead
of `-A i(i-1)` because the difference is affine in `i`, and affine terms
are absorbed into the Lagrange multiplier and cancel in same-mean objective
differences.

## Support i>=2

The upper-boundary `r=2` profile has:

```text
p_0=p_1=0,
support i>=2.
```

This creates no new finite-transfer boundary term.  The exact finite
objective is defined for all `i>=0`, and restricting to `i>=2` simply changes
the compact feasible set.  The omitted `i=0,1` coordinates have zero mass in
the constrained profile and remain available only in the unconstrained
comparison profile.

The two profiles compared for room have:

```text
same total mass 1,
same mean deficit T_alpha(x).
```

Therefore the affine centering terms in the exact normalization bridge cancel
exactly.

## Compact interval

The relevant interval is:

```text
X=[0.95,1].
```

It is compact.  The limiting mean target:

```text
T_alpha(x)=1+2/ln 2-x
```

lies in:

```text
[2/ln 2, 0.05+2/ln 2],
```

which is strictly above the support lower endpoint `2`.  Hence the
mean-solver for the `r=2` Gibbs profile stays in a compact parameter range,
with variance bounded below uniformly.

The unconstrained comparison profile has support `i>=0`; its mean target is
also in a compact subset of `(0,infinity)`, so its mean-solver is likewise
uniformly stable.

## Transfer theorem

Assume `R2-G1` supplies limiting margins:

```text
Room_2(x) >= R_2 > 0,
Prefix_2(x) >= P_2 > 0
```

uniformly for:

```text
x in [0.95,1].
```

Then there exists `A0` such that for all:

```text
A=alpha >= A0
```

the exact finite alpha-anchor `r=2` profile satisfies:

```text
Room_{A,2}^{finite}(x) >= R_2/2,
Prefix_{A,2}^{finite}(x) >= P_2/2
```

uniformly for:

```text
x in [0.95,1].
```

It also has:

```text
Gaussian tail,
tail/relevance hypotheses after rounding,
k_u=O(n/log n)
```

when used at:

```text
k=boldk_alpha-D+O(1),
D=O(n/log^3 n).
```

## Normalization bridge

The exact finite normalization bridge applies with:

```text
A=alpha
```

because its algebraic identity is valid for every large integer anchor `A`.

For any two profiles with equal mass and equal mean deficit:

```text
[-sum_i p_i log(p_i d_{A-i})]
-
[-sum_i q_i log(q_i d_{A-i})]
  = J_A(p)-J_A(q).
```

Thus the finite room margin is in the same normalization as the HR/HP
first-moment exponent used by:

```text
upper-boundary-alpha-first-moment-shift-u3-closure-2026-05-13.md.
```

## Output

Once `R2-G1` is proved with, for example:

```text
R_2=0.07,
P_2=0.006,
```

this transfer exports exact finite margins:

```text
Room_{A,2}^{finite}(x) >= 0.035,
Prefix_{A,2}^{finite}(x) >= 0.003
```

for all sufficiently large `n` and all:

```text
x in [0.95,1].
```

These are the exact finite margins required by:

```text
upper-boundary-r2-rounding-stability-u4-closure-2026-05-13.md
upper-boundary-r2-c3-source-gate-adapter-2026-05-13.md
upper-boundary-r2-c5-active-profile-adapter-2026-05-13.md
```

## Status

`R2-G2` is closed conditional on `R2-G1`.

No additional finite-transfer obstruction is known for the alpha-anchor
`r=2` profile.
