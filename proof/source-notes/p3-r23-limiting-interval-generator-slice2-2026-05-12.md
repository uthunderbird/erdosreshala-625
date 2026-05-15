# P3 `r=2,3` limiting interval generator slice 2

Date: 2026-05-12

## Purpose

This note defines the second proof-grade slice for the limiting certificate
generator:

```text
objective intervals + room lower bounds.
```

It assumes slice 1 has already produced certified:

```text
mu brackets,
variance lower bounds,
tail0_upper,
tail1_upper,
tail_ratio_upper.
```

## Objective identity

For each `r in {1,2,3}`, the limiting objective is:

```text
J_r(x)= -sum_i p_i^{(r)} log p_i^{(r)}
        -a2 sum_i i(i-1)p_i^{(r)}.
```

Using:

```text
p_i = exp(mu i-a2 i(i-1))/Z,
sum_i i p_i = T(x),
```

the entropy term rewrites as:

```text
-sum_i p_i log p_i
  = -mu T(x) + a2 sum_i i(i-1)p_i + log Z.
```

Therefore:

```text
J_r(x)=log Z_r(mu_r(x))-mu_r(x)T(x).
```

This identity is preferable for interval certification because it avoids
direct entropy-tail estimates.

## Interval evaluation

For a row interval `X=[x_L,x_R]` and certified `mu_r in [mu_L,mu_R]`, the
generator must enclose:

```text
log Z_r(mu_r),
mu_r T(x),
J_r(X).
```

The partition function enclosure uses:

```text
Z_r = Z_r^{trunc} + TailZ_r,
0 <= TailZ_r <= tail_weight0_upper.
```

Then:

```text
log(Z_trunc_lower) <= log Z_r <= log(Z_trunc_upper+tail_weight0_upper).
```

The product `mu*T` must use directed interval multiplication because `mu`
may have either sign.

## Room lower bound

For `r=2,3`, define:

```text
Room_r=(log2)^2/2 - [J_1-J_r].
```

To lower-bound room, use:

```text
Room_r_lower
 = (log2)^2/2 lower
   - (J_1_upper - J_r_lower).
```

The row may set:

```text
room_ok=True
```

only if:

```text
room_lower_decimal > 0.
```

## Comparator dependency

Every `r=2,3` row needs a compatible `r=1` comparator enclosure over the
same `x` interval.  The final generator can implement this in either way:

```text
1. emit separate r=1 rows and join them by interval id;
2. include J_1 lower/upper fields directly in every r=2,3 row.
```

The preferred implementation is to include:

```text
interval_id,
J_lower,
J_upper,
J1_lower,
J1_upper.
```

## Tail error field

Slice 2 fills:

```text
objective_tail_error_upper.
```

If using `J=log Z-mu T`, this error is the contribution of the
partition-function tail to `log Z`:

```text
log(1+tail_weight0_upper/Z_trunc_lower).
```

## Acceptance status

Rows after slice 2 may have proof-grade:

```text
mu_bracket_ok=True,
variance_positive=True,
tail_ok=True,
room_ok=True.
```

They must still remain unaccepted until prefix positivity is certified:

```text
prefix_ok=False,
certificate_status=candidate_only.
```

Only after slice 3 may rows become:

```text
certificate_status=limiting_row_ok.
```

## Status

This note is the implementation target for objective/room certification.
It also identifies a schema improvement: add explicit objective interval
columns or interval ids before final certificate emission.

Initial implementation is in:

```text
work/scripts/p3_r23_limiting_interval_slice1.py
```

Despite the filename, the script now implements slices 1 and 2 and emits
`certificate_status=slice2_only`.
