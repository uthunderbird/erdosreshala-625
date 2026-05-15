# Upper-boundary r=2 directed interval certificate spec

Date: 2026-05-13

## Purpose

This note specifies a proof-grade directed interval certificate for `R2-G1`.

It is intended to replace the exploratory floating-point scan for the
upper-boundary alpha-anchor `r=2` route.

The target inequalities are:

```text
Room_2(x) >= 0.07,
Prefix_2(x) >= 0.006,
```

uniformly for:

```text
x in [0.95,1].
```

## Constants

Use:

```text
A = (ln 2)/2,
delta = 0.01,
T(x)=1+2/ln 2-x.
```

For `x in [0.95,1]`:

```text
T(x) in [2/ln 2, 0.05+2/ln 2].
```

## Truncation

Use truncation:

```text
I=40.
```

For all `mu<=2` and all `i>=40`:

```text
w_{i+1}/w_i
  = exp(mu-A((i+1)^2-i^2))
  <= exp(2-(ln 2)(40+1/2))
  < 5e-12.
```

Thus every tail:

```text
sum_{i>I} i^m exp(mu i-Ai^2),  m=0,1,2,
```

is bounded by a geometric tail with ratio `<5e-12`.  The resulting total
error is far below `1e-10` for all endpoint inequalities in this certificate.

## Mean parameter enclosures

The checker should prove by interval monotonicity of:

```text
M_r(mu)=sum_{i>=r} i exp(mu i-Ai^2)/sum_{i>=r} exp(mu i-Ai^2)
```

that:

```text
mu_0(T(1)) in [1.99,2.00],
mu_2(T(1)) in [1.68,1.69],
mu_2(T(x)) in [1.68,1.75] for all x in [0.95,1].
```

The monotonicity needed here is:

```text
dM_r/dmu = Var_{p^{(r)}_mu}(i)>0.
```

Since:

```text
T(1)=2/ln 2,
T(0.95)=0.05+2/ln 2,
```

and `T` decreases with `x`, the interval for `mu_2(T(x))` follows from
checking the two endpoints.

## Room certificate

The room monotonicity note:

```text
upper-boundary-r2-room-monotonicity-certificate-2026-05-13.md
```

reduces the room lower bound to:

```text
x=1.
```

At `x=1`, compute with directed intervals:

```text
Obj_r(T)= -mu_r T + log Z_r(mu_r),
Room_2(1)=(ln 2)^2/2-(Obj_0(T)-Obj_2(T)).
```

using:

```text
T=2/ln 2,
mu_0 in [1.99,2.00],
mu_2 in [1.68,1.69],
I=40 plus tail enclosure.
```

Required checker output:

```text
Room_2(1) in [0.075,0.076].
```

This implies:

```text
Room_2(x)>=0.075>0.07
```

for all:

```text
x in [0.95,1].
```

## Prefix guard endpoint

The prefix guard note:

```text
upper-boundary-r2-prefix-guard-reduction-2026-05-13.md
```

identifies the tight endpoint as:

```text
q=delta e_2,
x=0.95.
```

This value is explicit:

```text
Phi_{0.95}(delta e_2)
  = -(1-delta)log(1-delta)
    + A delta (0.95+1-2/ln 2).
```

Required checker output:

```text
Phi_{0.95}(0.01 e_2) in [0.00670,0.00672].
```

This proves the tight guard endpoint:

```text
Phi_x(delta e_2)>0.006
```

for all:

```text
x in [0.95,1],
```

because the expression is affine increasing in `x`.

## p2 lower bound

To ensure `delta e_2` is an admissible prefix endpoint, prove:

```text
p_2(x)>0.35
```

for all:

```text
x in [0.95,1].
```

It is enough to use:

```text
mu_2(x) in [1.68,1.75].
```

Then:

```text
p_i/p_2
  = exp(mu(i-2)-A(i^2-4)).
```

The checker should bound:

```text
1 + sum_{i=3}^{40} exp(1.75(i-2)-A(i^2-4)) + tail < 3.
```

Hence:

```text
p_2>1/3>0.35
```

is not literally implied by `<3`; for the stated `0.35`, prove instead:

```text
1 + sum_{i=3}^{40} exp(1.75(i-2)-A(i^2-4)) + tail < 20/7.
```

which gives:

```text
p_2>7/20=0.35.
```

The exploratory values are:

```text
p_2(0.95) ~= 0.37394,
p_2(1)    ~= 0.39580.
```

## Non-tight prefix endpoints

After concavity reduction on each prefix interval, only endpoint masses must
be checked:

```text
delta,
P_2(x),
P_3(x),
P_4(x),
1-delta.
```

The endpoint list stops at `P_4` because:

```text
P_4(0.95) ~= 0.9448 < 0.99,
P_5(0.95) ~= 0.9934 > 0.99,
```

and `P_s(x)` increases/decreases only within a range that does not create a
new guarded endpoint beyond `1-delta`; the checker should verify this
directly with intervals.

Required robust lower bounds:

```text
Phi_x(P_2(x)) > 0.15,
Phi_x(P_3(x)) > 0.20,
Phi_x(P_4(x)) > 0.10,
Phi_x(1-delta) > 0.03,
```

uniformly for:

```text
x in [0.95,1].
```

These margins are much larger than `0.006`, so coarse interval subdivision
is acceptable.

## Subdivision strategy

Use a small directed interval partition:

```text
[0.95,1] = union of 50 intervals of length 0.001.
```

On each interval:

```text
1. enclose T(x);
2. enclose mu_2(T(x)) by bisection with interval arithmetic;
3. enclose p_i for i=2,...,40 plus tail;
4. evaluate the prefix endpoint list.
```

The expected checker summary should be:

```json
{
  "room_lower": "> 0.075",
  "prefix_guard_lower": "> 0.00670",
  "p2_lower": "> 0.35",
  "non_tight_prefix_lower": "> 0.03",
  "certificate_passed": true
}
```

## Status

This is a proof-grade checker specification, not yet the checker output.

Once implemented and run, it should close `R2-G1`.
