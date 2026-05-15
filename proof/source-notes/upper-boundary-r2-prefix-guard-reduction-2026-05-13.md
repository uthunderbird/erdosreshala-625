# Upper-boundary r=2 prefix guard reduction

Date: 2026-05-13

## Purpose

This note reduces the hardest observed prefix part of `R2-G1` to an explicit
guard endpoint calculation.

It does not yet replace a full directed-interval certificate for every
prefix endpoint, but it identifies why the `r=2` prefix margin is robust:
the minimum is attained at the fixed guard mass `delta=0.01`, not at a
moving cumulative endpoint.

## Prefix setup

For a prefix subprofile `q`, write:

```text
m=|q|=sum_i q_i.
```

The prefix functional is:

```text
Phi_x(q)
  = -(1-m)log(1-m)
    + (ln 2)/2 * sum_i q_i (x+i-1-2/ln 2).
```

The certificate guard is:

```text
delta <= m <= 1-delta,
delta=0.01.
```

For `r=2`, the first occupied layer is:

```text
i=2.
```

If:

```text
p_2(x) >= delta,
```

then the prefix endpoint `m=delta` is realized by:

```text
q_2=delta,
q_i=0 for i>2.
```

At this endpoint:

```text
Phi_x(delta e_2)
  = -(1-delta)log(1-delta)
    + (ln 2)/2 * delta * (x+1-2/ln 2).
```

This is an affine increasing function of `x`.

Therefore:

```text
min_{x in [0.95,1]} Phi_x(delta e_2)
  = Phi_{0.95}(delta e_2).
```

## Explicit value

For:

```text
delta=0.01,
x=0.95,
```

the value is:

```text
Phi_{0.95}(0.01 e_2)
  = -(0.99)log(0.99)
    + (ln 2)/2 * 0.01 * (1.95-2/ln 2)
  ~= 0.0067080175.
```

Hence the guard endpoint has slack:

```text
0.0067080175 - 0.006 > 0.0007.
```

## p2 lower bound

The exploratory endpoint values are:

```text
p_2(0.95) ~= 0.37394,
p_2(1)    ~= 0.39580.
```

Thus the condition:

```text
p_2(x)>=0.01
```

has enormous slack.  A proof-grade certificate can prove the weaker bound:

```text
p_2(x)>=0.35
```

by enclosing:

```text
mu_2(x) in [1.68,1.75]
```

and bounding the normalized tail ratio:

```text
p_i/p_2
  = exp(mu(i-2)-(ln 2)(i^2-4)/2),
  i>=3.
```

For `mu<=1.75`, the resulting denominator is less than `3`, giving
`p_2>1/3`; a sharper interval check gives the displayed values.

## Other prefix endpoints

For `x=0.95`, the exploratory cumulative endpoint values are:

```text
P_2 ~= 0.37394,  Phi ~= 0.17196;
P_3 ~= 0.75284,  Phi ~= 0.23272;
P_4 ~= 0.94481,  Phi ~= 0.11798;
1-delta=0.99,   Phi ~= 0.03648.
```

These have much larger slack than the guard endpoint.  The remaining
proof-grade work is to enclose these moving cumulative endpoints uniformly
over `x in [0.95,1]` and prove they stay above `0.006`.

The existing exploratory scan indicates that the global prefix minimum is:

```text
Phi_{0.95}(0.01 e_2) ~= 0.0067080175.
```

## Certificate strategy

A proof-grade prefix certificate for `r=2` should proceed as follows:

```text
1. prove p_2(x)>0.35 on [0.95,1];
2. certify the explicit guard endpoint Phi_x(delta e_2)>=0.0067;
3. use concavity on each prefix interval to reduce all interior masses to
   the finite endpoint list;
4. interval-bound the cumulative endpoints P_2,P_3,P_4 and the guard
   endpoint 1-delta;
5. prove every non-guard endpoint is >=0.03, leaving large slack.
```

The only tight endpoint is the explicit `delta e_2` guard.

## Status

The prefix part of `R2-G1` is not fully closed yet, but it is reduced to a
finite interval certificate with a single tight explicit guard endpoint.
