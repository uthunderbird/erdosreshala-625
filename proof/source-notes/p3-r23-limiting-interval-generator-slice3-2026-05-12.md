# P3 `r=2,3` limiting interval generator slice 3

Date: 2026-05-12

## Purpose

This note defines the third proof-grade slice for the limiting certificate
generator:

```text
prefix and clipped-prefix Phi lower bounds.
```

It assumes slices 1 and 2 have already certified:

```text
mu brackets,
tail bounds,
room lower bounds.
```

## Prefix objective

For a subprofile `q<=p^{(r)}(x)`, define:

```text
Phi_x(q)=-(1-|q|)log(1-|q|)
         +a2 sum_i q_i(x+i-1-2/log2).
```

The HP middle/similar source requires positivity for all relevant
subprofiles with:

```text
delta <= |q| <= 1-delta.
```

For the active certificate it is enough to check prefix and clipped-prefix
subprofiles because of the prefix-reduction lemma already isolated in the
R4 proof chain.

## Endpoint set

For each row, each `r in {2,3}`, and each listed `delta`, define cumulative
profile masses:

```text
P_s = sum_{i=r}^s p_i.
```

The finite endpoint set is:

```text
E_delta = {delta, 1-delta}
          union {P_s : delta <= P_s <= 1-delta}.
```

The generator must evaluate clipped-prefix `Phi` at every endpoint in
`E_delta`.

## Why endpoints suffice

Between consecutive cumulative masses, a clipped prefix has fixed full
coordinates and one partial coordinate.  On such an interval the function
of the partial mass `theta` has derivative:

```text
d/dtheta Phi
  = log(1-|q|) + a2(x+i-1-2/log2).
```

The derivative is monotone decreasing in `theta`, so the function is
concave on the interval:

```text
d^2/dtheta^2 Phi = -1/(1-|q|) < 0.
```

A concave function attains its minimum on a closed interval at an endpoint.
Therefore checking all clipped endpoints and cumulative endpoints suffices.

## Interval implementation

For each endpoint mass `m in E_delta`, the generator constructs the clipped
prefix:

```text
q_i = p_i for i<s,
q_s = m-P_{s-1},
q_i = 0 for i>s.
```

It then encloses:

```text
1-|q|,
log(1-|q|),
sum_i q_i(x+i-1-2/log2),
Phi_x(q).
```

All terms must be outward-rounded over the entire row interval `X`.

## Handling uncertain endpoint membership

Because `P_s` is interval-valued, a cumulative endpoint may have uncertain
membership in `[delta,1-delta]`.  The safe rule is:

```text
if P_s interval intersects [delta,1-delta], include it.
```

This may add extra endpoints but cannot miss a true endpoint.

## Tail handling

Choose `Imax` so that:

```text
P_{Imax} >= 1-delta_min
```

with directed lower bounds, where `delta_min` is the smallest listed delta.

If not, the row must set:

```text
clipped_endpoint_missing > 0
```

and will be rejected.

The tail error contribution to `Phi` must be bounded in:

```text
prefix_tail_error_upper.
```

If every relevant endpoint lies before `Imax` and the remaining tail mass
is below `delta_min`, this error can be zero for endpoint enumeration,
with the tail condition recorded separately.

## Row acceptance

The row may set:

```text
prefix_ok=True
```

only if:

```text
prefix_phi_lower_decimal > 0,
prefix_endpoint_skipped=0,
clipped_endpoint_missing=0.
```

After slices 1--3 are all certified, the row may finally use:

```text
certificate_status=limiting_row_ok.
```

## Status

This completes the proof-grade generator specification for the limiting
`r=2,3` certificate.  The remaining work is implementation with directed
interval arithmetic and production of a certificate table accepted by the
checker.

Initial implementation is in:

```text
work/scripts/p3_r23_limiting_interval_slice1.py
```

Despite the filename, the script now implements slices 1--3.  Rows are
emitted as `limiting_row_ok` only if mean, tail, room, and prefix checks all
pass; otherwise they are emitted with a failure status.
