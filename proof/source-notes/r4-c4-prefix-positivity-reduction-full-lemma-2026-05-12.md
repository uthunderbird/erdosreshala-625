# R4 C4 prefix-positivity reduction: full lemma

Date: 2026-05-12

## Purpose

This note proves the analytic reduction behind C4.  It does not certify the
numerical margins.  It shows exactly what a finite interval certificate has
to check in order to imply the HP lower-boundbeta condition for the
constrained low-regime profile.

## Setup

Fix `x in [0,x0]` and let `p(x)=(p_i(x))_{i>=1}` be a limiting constrained
profile with

```text
p_i(x) >= 0,
sum_i p_i(x) = 1,
sum_i i p_i(x) = T(x),
```

and exponential Gaussian tail

```text
p_i(x) <= C exp(-c i^2)
```

uniformly for `x in [0,x0]`.

For a subprofile `q=(q_i)` with `0<=q_i<=p_i(x)`, write

```text
|q| = sum_i q_i.
```

The limiting lower-boundbeta exponent is

```text
Phi_x(q)
  = -(1-|q|)log(1-|q|)
    + a2 sum_i q_i (x+i-1-2/ln2),
```

where `a2=ln2/2`.

C4 requires: for every fixed `delta in (0,1/2)`, there is `c_delta>0` such
that

```text
Phi_x(q) >= c_delta
```

uniformly for all `x in [0,x0]` and all subprofiles satisfying

```text
delta <= |q| <= 1-delta.
```

## Lemma 1: prefix minimization

For fixed `x` and fixed mass `r`, among all `q` satisfying

```text
0 <= q_i <= p_i(x),
sum_i q_i = r,
```

the value `Phi_x(q)` is minimized by the prefix-saturated subprofile:

```text
q_i = p_i(x)       for i<s,
q_s = r-P_{s-1}(x),
q_i = 0            for i>s,
```

where

```text
P_s(x)=sum_{i<=s}p_i(x)
```

and `s` is chosen so that

```text
P_{s-1}(x) <= r <= P_s(x).
```

### Proof

For fixed `r`, the entropy term `-(1-r)log(1-r)` is constant.  The remaining
term is linear in `q` with coefficient

```text
c_i(x)=a2(x+i-1-2/ln2).
```

The sequence `c_i(x)` is strictly increasing in `i`.  Therefore any
subprofile which puts positive mass at a larger index while a smaller index
is not saturated can be improved by moving an infinitesimal amount of mass
from the larger index to the smaller one.  Iterating gives the
prefix-saturated minimizer.

## Lemma 2: endpoint reduction on each prefix interval

Define

```text
Psi_x(r)=Phi_x(q^prefix_x(r)).
```

On the interval `r in [P_{s-1}(x),P_s(x)]`, write

```text
theta = r-P_{s-1}(x).
```

Then

```text
Psi_x(r)
 = -(1-r)log(1-r)
   + a2 [
       sum_{i<s} p_i(x)(x+i-1-2/ln2)
       + theta(x+s-1-2/ln2)
     ].
```

Moreover

```text
Psi_x''(r) = -1/(1-r) < 0.
```

Thus `Psi_x` is concave on every prefix interval, and its minimum on any
closed subinterval of a prefix interval is attained at an endpoint.

## Lemma 3: finite truncation

Fix `delta in (0,1/2)` and choose `I` so that uniformly in `x`

```text
Tail0_I(x)=sum_{i>I}p_i(x) <= delta/4,
Tail1_I(x)=sum_{i>I}i p_i(x) <= 1.
```

If all prefix endpoints

```text
r in {delta, 1-delta}
    union {P_s(x): 1<=s<=I, delta<=P_s(x)<=1-delta}
```

obey

```text
Psi_x(r) >= m_delta > 0
```

uniformly for `x in [0,x0]`, and if additionally the last checked prefix
has

```text
P_I(x) >= 1-delta
```

uniformly, then

```text
Phi_x(q) >= m_delta
```

for every admissible `q`.

### Proof

By Lemma 1 it is enough to check `Psi_x(r)` for `r in [delta,1-delta]`.
Since `P_I(x)>=1-delta`, every relevant prefix interval intersecting
`[delta,1-delta]` has index at most `I`, except possibly intervals clipped
at `delta` or `1-delta`.  By Lemma 2, the minimum on each such clipped
interval occurs at one of the endpoints listed above.

## Uniform-in-x certificate theorem

For fixed `delta`, suppose `[0,x0]` is covered by finitely many intervals
`J`.  On each `J`, an interval certificate supplies rigorous enclosures for

```text
p_i(x), P_i(x), Psi_x(delta), Psi_x(1-delta), Psi_x(P_s(x))
```

for all required `s<=I_J`, and proves

```text
P_{I_J}(x) >= 1-delta,
Psi_x(r) >= m_{J,delta} > 0
```

for every listed endpoint and every `x in J`.

Then C4 holds for that `delta` with

```text
c_delta = min_J m_{J,delta}.
```

Since `delta` is arbitrary but fixed in the HP lower-boundbeta condition,
the final proof may state a family of certificates indexed by rational
`delta in (0,1/2)`, or a stronger analytic certificate valid uniformly for
all `delta` in compact subintervals of `(0,1/2)`.

## Endpoint and splice obligations

Two cases require separate certificate rows:

1. `x=0`, because a minimum can occur at the endpoint of the parameter
   interval even if all interior derivative tests are positive.
2. `x` near `x0`, because the unconstrained top-only obstruction has zero
   margin at the transition.  The constrained proof must either keep fixed
   cap slack through the splice interval or hand over to the original HP
   good-branch proof on an overlapping interval.

## Status

This note closes the analytic reduction from C4 to a finite interval
certificate.  It does not provide the certificate margins.  The remaining
C4 work is computational-rigorous:

1. choose the exact constrained profile `p(x)` and cap slack/splice rule;
2. generate interval enclosures for `rho_*(x)`, `mu_tail(x)`, and `p_i(x)`;
3. prove positive lower bounds for the endpoint list above for every fixed
   `delta` needed by the HP middle-overlap theorem.
