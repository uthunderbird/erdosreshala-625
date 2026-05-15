# Upper-boundary alpha-anchor r=1 interval certificate target

Date: 2026-05-13

## Purpose

This note turns the exploratory `r=1` floating-point scan into an explicit
proof-grade interval-certificate target for `U1` in:

```text
upper-boundary-alpha-anchor-r1-certificate-theorem-2026-05-13.md
```

The goal is not to claim the interval certificate is already proved.  The
goal is to make the exact certificate obligations auditable.

## Interval

Use the terminal upper-boundary interval:

```text
x in [x_1,1),
x_1 = 0.95
```

unless later finite-transfer losses force a larger `x_1`.

For numerical certification, replace `[0.95,1)` by the compact interval:

```text
[0.95,1]
```

using the limiting value at `x=1`.

## Limiting target mean

At the alpha-anchor threshold, the limiting deficit mean is:

```text
T_alpha(x) = 1 + 2/ln 2 - x.
```

Thus on `[0.95,1]`:

```text
2/ln 2 <= T_alpha(x) <= 0.05 + 2/ln 2.
```

Numerically:

```text
2.885390... <= T_alpha(x) <= 2.935390...
```

## r=1 profile

For each `x`, define the `r=1` omitted-top profile on deficits:

```text
i >= 1
```

by:

```text
p_i(mu) = exp(mu i - (ln 2)i^2/2) / Z(mu),
Z(mu) = sum_{j>=1} exp(mu j - (ln 2)j^2/2),
```

where `mu=mu_1(x)` is the unique value satisfying:

```text
sum_{i>=1} i p_i(mu) = T_alpha(x).
```

The unconstrained alpha-anchor comparison profile is the same construction
with:

```text
i >= 0.
```

## Room function

Define:

```text
Obj(p) = sum_i [-p_i log p_i - (ln 2)i^2 p_i/2].
```

The limiting first-moment room is:

```text
Room_1(x)
  = (ln 2)^2/2 - (Obj(p^{un}_x)-Obj(p^{r=1}_x)).
```

Certificate target:

```text
Room_1(x) >= 0.21
```

uniformly for:

```text
x in [0.95,1].
```

The exploratory scan found:

```text
min Room_1(x) ~= 0.219981
```

near `x=1`, so `0.21` leaves about `0.0099` exploratory slack.

## Prefix function

For a partial prefix mass vector `q_i <= p_i`, let:

```text
r(q) = sum_i q_i,
Phi_x(q)
  = -(1-r(q))log(1-r(q))
    + (ln 2)/2 * sum_i q_i (x+i-1-2/ln 2).
```

The prefix margin is the minimum of `Phi_x(q)` over admissible prefix
subprofiles with total prefix mass away from the endpoints.  The exploratory
scan checked endpoint guards:

```text
delta in {0.01,0.05,0.1,0.2}.
```

Certificate target:

```text
Prefix_1(x) >= 0.003
```

uniformly for:

```text
x in [0.95,1].
```

The exploratory scan found:

```text
min Prefix_1(x) ~= 0.003242
```

near `x=0.95`, so `0.003` leaves only about `0.00024` exploratory slack.
This is the narrowest numerical part of `U1`.

## Tail truncation obligation

A proof-grade interval certificate may truncate the infinite sums at:

```text
1 <= i <= I
```

only if it proves explicit upper bounds for the omitted tail:

```text
sum_{i>I} exp(mu i - (ln 2)i^2/2),
sum_{i>I} i exp(mu i - (ln 2)i^2/2),
sum_{i>I} i^2 exp(mu i - (ln 2)i^2/2).
```

The exploratory script used:

```text
I = 220.
```

For publication, `I=40` or another modest value may already be enough, but
the chosen value must come with a rigorous geometric tail bound.  Since
`mu=O(1)` and the quadratic coefficient is `(ln 2)/2`, the ratio:

```text
w_{i+1}/w_i = exp(mu - (ln 2)(i+1/2))
```

is exponentially small once `i` is moderately large.

## Monotonicity / subdivision obligation

The certificate must prove the room and prefix lower bounds on a continuum of
`x`, not just on a grid.  Acceptable proof-grade routes:

```text
1. directed interval arithmetic over a partition of [0.95,1];
2. analytic derivative bounds between grid points plus interval-evaluated
   endpoints;
3. a monotonicity proof reducing room to x=1 and prefix to x=0.95.
```

The scan suggests:

```text
Room_1 is worst near x=1,
Prefix_1 is worst near x=0.95.
```

but this monotonicity is not yet proved.

## Certificate output required by U1

The finished certificate should export:

```text
x_1 = 0.95,
r_* = 0.21,
p_* = 0.003,
Room_1(x) >= r_* for all x in [x_1,1],
Prefix_1(x) >= p_* for all x in [x_1,1].
```

If finite-transfer or rounding losses consume more prefix slack than `0.003`,
then either:

```text
1. increase x_1 above 0.95;
2. switch to the r=2 fallback profile;
3. strengthen the prefix certificate definition;
4. or improve the finite/rounding loss bounds.
```

Follow-up scan showed that increasing `x_1` gives only minor prefix relief:

```text
x_1=0.96: Prefix_1 ~= 0.0032769;
x_1=0.97: Prefix_1 ~= 0.0033116;
x_1=0.98: Prefix_1 ~= 0.0033463.
```

The more meaningful fallback is `r=2`, recorded in:

```text
upper-boundary-alpha-anchor-r2-robust-candidate-2026-05-13.md
```

## Status

`U1` is not closed.

This note defines the proof-grade interval-certificate target and identifies
the narrow quantitative bottleneck:

```text
Prefix_1(x) >= 0.003 on [0.95,1].
```
