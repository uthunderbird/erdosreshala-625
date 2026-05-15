# P3 `r=2,3` limiting certificate table schema

Date: 2026-05-12

## Purpose

This schema is the machine-readable companion to:

```text
p3-r23-limiting-certificate-theorem-2026-05-12.md
```

It certifies the limiting deficit-coordinate margins before the
large-anchor exact-`d_u` transfer is applied.

Acceptance checker:

```text
work/scripts/p3_check_r23_limiting_certificate_table.py
```

Candidate-row generator:

```text
work/scripts/p3_r23_limiting_candidate_certificate.py
```

The candidate generator is not proof evidence: it emits
`certificate_status=candidate_only`, so the acceptance checker must reject
its rows.

First proof-grade implementation slice:

```text
p3-r23-limiting-interval-generator-slice1-2026-05-12.md
```

Second proof-grade implementation slice:

```text
p3-r23-limiting-interval-generator-slice2-2026-05-12.md
```

Third proof-grade implementation slice:

```text
p3-r23-limiting-interval-generator-slice3-2026-05-12.md
```

## Required row fields

Every row must include:

```text
mode,
x_left,
x_right,
r,
imax,
certificate_status,
transcendental_status,
mu_bracket_ok,
variance_positive,
tail_ok,
room_ok,
prefix_ok,
room_lower_decimal,
prefix_phi_lower_decimal,
mu_left,
mu_right,
variance_lower,
tail0_upper,
tail1_upper,
tail_ratio_upper,
objective_tail_error_upper,
prefix_tail_error_upper,
interval_id,
J_lower,
J_upper,
J1_lower,
J1_upper,
prefix_endpoint_skipped,
clipped_endpoint_missing.
```

## Accepted row

For:

```text
mode=p3_r23_limiting
```

the accepted status is:

```text
certificate_status=limiting_row_ok
transcendental_status=decimal_directed_exp_log
```

The following Boolean fields must be true:

```text
mu_bracket_ok,
variance_positive,
tail_ok,
room_ok,
prefix_ok.
```

The following numeric conditions must hold:

```text
room_lower_decimal > 0,
prefix_phi_lower_decimal > 0,
variance_lower > 0,
tail_ratio_upper < 1,
tail0_upper finite,
tail1_upper finite,
objective_tail_error_upper finite,
prefix_tail_error_upper finite,
prefix_endpoint_skipped = 0,
clipped_endpoint_missing = 0.
```

## Coverage check

For each required `r in {2,3}`, accepted rows must cover:

```text
[0,x0].
```

Rows for `r=1` may be present as comparator evidence but are not accepted
as endpoint certificates.

## Constant extraction

For each accepted `r`, the checker extracts:

```text
room_lower_by_r,
prefix_phi_lower_by_r,
variance_lower_by_r,
tail0_upper_by_r,
tail1_upper_by_r,
tail_ratio_upper_by_r.
```

The large-anchor transfer may use only the extracted positive lower bounds.

## Current status

Schema only.  A proof-grade generator must still be written.  Existing
float scans do not satisfy this schema.
The candidate generator exercises the row layout but intentionally does not
close the gate.
