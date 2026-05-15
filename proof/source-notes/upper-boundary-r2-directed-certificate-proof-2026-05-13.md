# Upper-boundary r=2 directed certificate proof

Date: 2026-05-13

## Purpose

This note closes `R2-G1` for the upper-boundary alpha-anchor `r=2` route at
ordinary analytical-proof standard.

It proves:

```text
Room_2(x) >= 0.07,
Prefix_2(x) >= 0.006
```

uniformly for:

```text
x in [0.95,1].
```

The proof uses the monotonic reductions and explicit endpoint margins from:

```text
upper-boundary-r2-room-monotonicity-certificate-2026-05-13.md
upper-boundary-r2-prefix-guard-reduction-2026-05-13.md
upper-boundary-r2-directed-interval-certificate-spec-2026-05-13.md
upper-boundary-r2-numeric-certificate-check-result-2026-05-13.md
```

## Certificate convention

All decimal inequalities below are to be interpreted as short directed
computations over finite sums with the tail bound:

```text
I=40,
w_{i+1}/w_i <= exp(2-(ln 2)(40+1/2)) < 5e-12.
```

The endpoint margins are large enough that the final proof may replace the
displayed decimals by rational interval enclosures if desired.  The
important certified gaps are:

```text
Room margin gap: 0.075 - 0.07 = 0.005;
Prefix tight gap: 0.00670 - 0.006 = 0.00070;
Non-tight prefix gap: 0.03 - 0.006 = 0.024.
```

## Room lower bound

From:

```text
upper-boundary-r2-room-monotonicity-certificate-2026-05-13.md
```

we have:

```text
Room_2'(x)<0
```

on:

```text
[0.95,1].
```

Hence:

```text
Room_2(x) >= Room_2(1).
```

At `x=1`, the mean is:

```text
T=2/ln 2.
```

The mean solvers are enclosed by:

```text
mu_0 in [1.99,2.00],
mu_2 in [1.68,1.69].
```

Using:

```text
Obj_r(T)=-mu_r T+log Z_r(mu_r),
Z_r(mu)=sum_{i>=r} exp(mu i-(ln 2)i^2/2),
```

and truncating at `I=40` with the tail bound above gives:

```text
Room_2(1) in [0.075,0.076].
```

Therefore:

```text
Room_2(x) >= 0.075 > 0.07.
```

## Prefix tight endpoint

Let:

```text
delta=0.01.
```

For `r=2`, the first occupied coordinate is `i=2`.  The tight guard endpoint
is:

```text
q=delta e_2.
```

The prefix value is explicit:

```text
Phi_x(delta e_2)
  = -(1-delta)log(1-delta)
    + (ln 2)/2 * delta * (x+1-2/ln 2).
```

It is affine increasing in `x`, so the minimum on `[0.95,1]` is at `x=0.95`.
Direct evaluation gives:

```text
Phi_{0.95}(0.01e_2) in [0.00670,0.00672].
```

Thus:

```text
Phi_x(delta e_2)>0.006
```

uniformly on `[0.95,1]`.

## Admissibility of the tight endpoint

We need:

```text
p_2(x) >= delta.
```

In fact, for `x in [0.95,1]` the mean-solver satisfies:

```text
mu_2(x) <= 1.75.
```

For `i>=3`,

```text
p_i/p_2
  = exp(mu(i-2)-(ln 2)(i^2-4)/2)
  <= exp(1.75(i-2)-(ln 2)(i^2-4)/2).
```

The finite sum plus geometric tail satisfies:

```text
1 + sum_{i=3}^{40} exp(1.75(i-2)-(ln 2)(i^2-4)/2) + tail
  < 2.685 < 20/7.
```

Therefore:

```text
p_2(x) > 7/20 > 0.35 > 0.01.
```

So `delta e_2` is an admissible prefix endpoint throughout the interval.

## Non-tight prefix endpoints

By the standard prefix concavity reduction, it remains to check:

```text
P_2(x),
P_3(x),
P_4(x),
1-delta.
```

The directed finite-sum certificate gives:

```text
Phi_x(P_2(x)) > 0.15,
Phi_x(P_3(x)) > 0.20,
Phi_x(P_4(x)) > 0.10,
Phi_x(1-delta) > 0.03
```

uniformly on `[0.95,1]`.

The weakest of these is:

```text
Phi_{0.95}(1-delta) ~= 0.03648,
```

still far above the target `0.006`.  The endpoint list is complete because
the cumulative mass passes `1-delta` between the `i=4` and `i=5` layers
throughout the interval; this is certified by the same finite-sum enclosures:

```text
P_4(x)<0.99<P_5(x).
```

Thus every admissible prefix endpoint has value at least:

```text
0.006.
```

Concavity on each prefix interval then gives the same bound for every
admissible prefix subprofile.

## Output

We have proved:

```text
Room_2(x) >= 0.07,
Prefix_2(x) >= 0.006
```

uniformly for:

```text
x in [0.95,1].
```

This is exactly `R2-G1`.

## Status

`R2-G1` is closed.

The explicit finite interval appendix is:

```text
upper-boundary-r2-explicit-interval-tables-2026-05-13.md
```
