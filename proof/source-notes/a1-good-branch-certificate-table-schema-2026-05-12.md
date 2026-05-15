# A1 good-branch certificate table schema

Date: 2026-05-12

## Purpose

This schema defines the machine-readable certificate table for the A1
modified Lemma 7.20 good-branch handoff.

It supports:

```text
phi(1,x,1) positivity,
source theorem references,
handoff coverage with constrained/P3 rows.
```

Acceptance checker:

```text
work/scripts/a1_check_good_branch_certificate_table.py
```

## Required row fields

Every row must include:

```text
mode,
x_left,
x_right,
certificate_status,
transcendental_status,
phi_lower_decimal,
phi_ok,
source_alignment_ok,
ordinary_chi_ok,
zeta_gap_ok,
azuma_scale_ok,
handoff_overlap_ok,
source_ref,
notes.
```

## Accepted rows

For:

```text
mode=good_branch
```

the accepted status is:

```text
certificate_status=good_branch_row_ok
transcendental_status=decimal_directed_or_symbolic_monotone
```

The following Boolean fields must be true:

```text
phi_ok,
source_alignment_ok,
ordinary_chi_ok,
zeta_gap_ok,
azuma_scale_ok,
handoff_overlap_ok.
```

The numeric condition is:

```text
phi_lower_decimal > 0.
```

## Coverage

Accepted good-branch rows must cover the interval required by the splice
policy:

```text
[x0-eta_splice/2, x_right_max],
```

where `x_right_max` is at least the upper edge of the proof's parameter
space.  If the proof parameter is only `x in [0,x0]`, then it is enough to
cover:

```text
[x0-eta_splice/2, x0].
```

The final bundle manifest must record:

```text
x0,
eta_splice,
good_branch_left=x0-eta_splice/2,
good_branch_right.
```

## Handoff overlap

The checker can verify row coverage, but the proof bundle must also include
a handoff statement:

```text
constrained/P3 rows cover [0, x0-eta_splice],
good-branch rows cover [x0-eta_splice/2, x0],
eta_splice>0.
```

This proves no uncovered gap.

## Current status

Schema only.  A checker exists, but no accepted certificate table has been
produced.

