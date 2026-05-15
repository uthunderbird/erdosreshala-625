# P3 `r=2,3` limiting interval generator slice 1

Date: 2026-05-12

## Purpose

This note defines the first proof-grade slice for the limiting certificate
generator:

```text
mean brackets + Gaussian/geometric tail bounds
```

for:

```text
r in {1,2,3},
x in [0,x0].
```

Rows for `r=1` are comparator rows needed for `Room_r`; rows for `r=2,3`
are endpoint certificate rows.

## Directed interval objects

For each row interval:

```text
X=[x_L,x_R],
T(X)=1+2/log2-X,
```

and each `r`, the generator must enclose:

```text
mu in [mu_L,mu_R],
Z_r(mu),
M_r(mu),
Mean_r(mu)=M_r/Z_r,
Var_r(mu).
```

All arithmetic must be outward-rounded.

## Mean bracket check

Since `Mean_r(mu)` is strictly increasing in `mu`, it is enough to prove:

```text
Mean_r(mu_L; lower arithmetic) <= T_low,
Mean_r(mu_R; upper arithmetic) >= T_high,
```

where:

```text
T_low = 1+2/log2-x_R,
T_high = 1+2/log2-x_L.
```

The row may then set:

```text
mu_bracket_ok=True.
```

## Variance check

The generator must emit:

```text
variance_lower > 0.
```

A simple robust bound is:

```text
Var(i) >= p_r p_{r+1},
```

where `p_r,p_{r+1}` are lower-bounded using the row's `mu` bracket and tail
upper bounds.  If using this bound, the row should record it in a
human-readable summary.

## Tail check

For terms:

```text
w_i(mu)=exp(mu i-a2 i(i-1)),
```

the ratio is:

```text
w_{i+1}/w_i = exp(mu-a2(2i)).
```

For all `mu<=mu_R` and `i>=Imax+1`, it is enough to prove:

```text
rho = exp(mu_R-a2*2(Imax+1)) < 1.
```

Then:

```text
tail_weight0 <= w_{Imax+1}/(1-rho),
tail_weight1 <= w_{Imax+1}*((Imax+1)/(1-rho)+rho/(1-rho)^2).
```

Dividing by a lower bound on the truncated partition function gives:

```text
tail0_upper,
tail1_upper.
```

The row may set:

```text
tail_ok=True
```

only if:

```text
tail_ratio_upper < 1
```

and all tail upper bounds are finite.

## Output columns used in slice 1

This slice fills:

```text
mu_left,
mu_right,
mu_bracket_ok,
variance_lower,
variance_positive,
tail0_upper,
tail1_upper,
tail_ratio_upper,
tail_ok.
```

It does not yet fill proof-grade:

```text
room_lower_decimal,
prefix_phi_lower_decimal,
room_ok,
prefix_ok.
```

## Acceptance status

Rows produced after slice 1 alone must still use:

```text
certificate_status=candidate_only
```

or a future intermediate status not accepted by the final checker.

Only the full generator with room and prefix intervals may emit:

```text
certificate_status=limiting_row_ok.
```

## Status

This is the implementation target for the first proof-grade upgrade from
`p3_r23_limiting_candidate_certificate.py`.

Initial slice-1 implementation:

```text
work/scripts/p3_r23_limiting_interval_slice1.py
```

It emits `certificate_status=slice1_only`, so final acceptance still waits
for slices 2 and 3.
