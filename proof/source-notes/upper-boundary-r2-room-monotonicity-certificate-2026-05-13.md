# Upper-boundary r=2 room monotonicity certificate

Date: 2026-05-13

## Purpose

This note proves the analytic monotonicity part of `R2-G1` for the
upper-boundary alpha-anchor `r=2` route.

It reduces the room certificate on:

```text
x in [0.95,1]
```

to the endpoint:

```text
x=1.
```

## Setup

Let:

```text
A = (ln 2)/2,
T(x)=1+2/ln 2-x.
```

For `r in {0,2}`, define the Gibbs distribution on:

```text
i>=r
```

by:

```text
p_i^{(r)}(mu)
  = exp(mu i - A i^2)/Z_r(mu),
Z_r(mu)=sum_{j>=r} exp(mu j-Aj^2),
```

where `mu=mu_r(T)` is chosen so that:

```text
sum_{i>=r} i p_i^{(r)}(mu_r(T)) = T.
```

For the upper-boundary interval:

```text
T in [2/ln 2, 0.05+2/ln 2].
```

The `r=2` support is feasible because:

```text
2/ln 2 > 2.
```

## Objective identity

For the profile objective:

```text
Obj_r(T)=sum_i[-p_i log p_i - A i^2 p_i],
```

the Gibbs form gives:

```text
log p_i = mu i-Ai^2-log Z_r(mu).
```

Therefore:

```text
Obj_r(T)
  = -mu_r(T) T + log Z_r(mu_r(T)).
```

This is the Legendre transform of `log Z_r`.

Differentiating with respect to `T` and using the mean constraint gives:

```text
d Obj_r / dT = -mu_r(T).
```

## Room derivative

The limiting `r=2` room is:

```text
Room_2(x)
  = (ln 2)^2/2 - (Obj_0(T(x))-Obj_2(T(x))).
```

Since:

```text
dT/dx=-1,
```

we get:

```text
d Room_2/dx
  = mu_2(T(x))-mu_0(T(x)).
```

For every fixed `T>2`, the distribution supported on `i>=2` has a larger
minimum support than the distribution supported on `i>=0`.  To achieve the
same mean `T`, the `r=2` exponential tilt must be smaller:

```text
mu_2(T)<mu_0(T).
```

One formal proof is stochastic monotonicity: for fixed `mu`, the `r=2`
distribution is the conditional version of the `r=0` distribution on the
upper tail `i>=2`, hence has strictly larger mean.  Since the mean is
strictly increasing in `mu`, matching the same mean requires lowering `mu`.

Thus:

```text
d Room_2/dx < 0
```

throughout `[0.95,1]`.

Therefore:

```text
min_{x in [0.95,1]} Room_2(x) = Room_2(1).
```

## Endpoint numerical target

The endpoint value is:

```text
Room_2(1) ~= 0.0751817.
```

The proof-grade certificate target:

```text
Room_2(x) >= 0.07
```

therefore reduces to proving the single endpoint inequality:

```text
Room_2(1) > 0.07.
```

This remaining endpoint evaluation is suitable for a short directed-interval
calculation because it involves only two one-dimensional Gibbs distributions
with means:

```text
T(1)=2/ln 2.
```

## Tail bound for endpoint evaluation

At `x=1`, exploratory values are:

```text
mu_0 ~= 1.99482,
mu_2 ~= 1.68363.
```

A proof-grade endpoint calculation may enclose:

```text
mu_0 in [1.99,2.00],
mu_2 in [1.68,1.69].
```

For both intervals and all `i>=40`, the ratio of successive unnormalized
weights satisfies:

```text
w_{i+1}/w_i
  = exp(mu-A((i+1)^2-i^2))
  <= exp(2-(ln 2)(40+1/2))
  < 10^{-11}.
```

Thus the tail beyond `i=40` is bounded by a geometric series with negligible
effect on `Room_2(1)` compared with the margin:

```text
0.0751817-0.07 > 0.005.
```

## Status

The room part of `R2-G1` is reduced to a one-point directed-interval
endpoint check.

The remaining nontrivial part of `R2-G1` is the prefix certificate:

```text
Prefix_2(x) >= 0.006 on [0.95,1].
```
