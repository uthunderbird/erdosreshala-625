# P3 `r=2,3` limiting certificate theorem

Date: 2026-05-12

## Purpose

This theorem is the remaining limiting certificate needed before the
exact-`d_u` large-anchor transfer can close G4 for the standard endpoint
route.

It replaces the exploratory scans:

```text
p3-rtruncated-scan-result-2026-05-12.md
p3-p1zero-scan-result-2026-05-12.md
```

by a finite interval-certificate target for:

```text
r in {2,3},
x in [0,x0].
```

## Limiting profile

Let:

```text
a2 = log(2)/2,
T(x)=1+2/log(2)-x,
x0=0.02905.
```

For `r in {1,2,3}`, define:

```text
p_i^{(r)}(x) = exp(mu_r(x)i-a2 i(i-1))/Z_r(mu_r(x)),  i>=r,
p_i^{(r)}(x) = 0,                                      i<r,
```

where `mu_r(x)` is the unique solution of:

```text
sum_i i p_i^{(r)}(x)=T(x).
```

The unrestricted comparator is `r=1`.

## Room function

Define:

```text
J_r(x)= -sum_i p_i^{(r)}(x) log p_i^{(r)}(x)
        -a2 sum_i i(i-1)p_i^{(r)}(x).
```

The limiting room for truncation `r` is:

```text
Room_r(x) = (log 2)^2/2 - [J_1(x)-J_r(x)].
```

The certificate must prove:

```text
Room_2(x) >= R2 > 0,
Room_3(x) >= R3 > 0
```

for all `x in [0,x0]`.

## Prefix positivity

For fixed deltas:

```text
DeltaSet = {0.01,0.05,0.1,0.2}
```

and every prefix/clipped-prefix subprofile `q<=p^{(r)}(x)` with:

```text
delta <= |q| <= 1-delta,
```

define:

```text
Phi_x(q)=-(1-|q|)log(1-|q|)
         +(log2/2) sum_i q_i (x+i-1-2/log2).
```

The certificate must prove:

```text
Phi_x(q) >= c_{r,delta}>0
```

for `r=2,3`, all listed `delta`, and all prefix/clipped-prefix endpoints.

## Certificate format

A certificate consists of a finite interval cover:

```text
[0,x0] subset union_j [x_j,x_{j+1}],
```

and, for each row, directed interval enclosures for:

```text
mu_1(x), mu_2(x), mu_3(x),
Z_r, M_r, Var_r,
p_i^{(r)} for i<=Imax,
tail0_r, tail1_r,
J_r,
Room_2, Room_3,
prefix Phi endpoint lower bounds.
```

The generator may truncate the infinite sums at `Imax` if it supplies a
geometric tail bound:

```text
tail_ratio_upper < 1,
tail0_upper,
tail1_upper,
objective_tail_error_upper,
prefix_tail_error_upper.
```

The machine-readable schema and checker are:

```text
p3-r23-limiting-certificate-table-schema-2026-05-12.md
work/scripts/p3_check_r23_limiting_certificate_table.py
```

The proof-grade generator is decomposed into implementation slices:

```text
p3-r23-limiting-interval-generator-slice1-2026-05-12.md
p3-r23-limiting-interval-generator-slice2-2026-05-12.md
p3-r23-limiting-interval-generator-slice3-2026-05-12.md
```

## Required checks

### L1: mean brackets

For each `r`, prove the bracketed `mu_r` solves the mean equation by:

```text
Mean_r(mu_left) <= T(x interval) <= Mean_r(mu_right)
```

with monotonicity certified via:

```text
Var_r >= v_r > 0.
```

### L2: room lower bounds

Using interval-enclosed objectives, prove:

```text
Room_2_lower > 0,
Room_3_lower > 0.
```

### L3: prefix lower bounds

For each row and each `delta`, enumerate all prefix endpoints that can
cross `[delta,1-delta]`, including clipped endpoints at `delta` and
`1-delta`, and prove:

```text
prefix_phi_lower > 0.
```

### L4: row coverage

Accepted rows cover all of `[0,x0]` for both `r=2` and `r=3`.

## Current numerical evidence

Existing exploratory scans indicate:

```text
r=2 room lower about 0.2186789,
r=3 room lower about 0.0659,
prefix lower about 0.0034155 for r=2,
prefix lower about 0.0068813 for r=3.
```

The exact-`d_u` finite-anchor scans at `A=30,40` give similar or larger
room for `r=2,3`, consistent with the large-anchor transfer.

## Consequence

Once this limiting interval certificate is supplied, the compactness and
large-anchor notes imply an exact finite-`d_u` certificate for all
sufficiently large anchors.  This closes the finite-objective part of G4
for the standard endpoint route.

## Status

Not proved yet.  This note is the precise theorem target for the next
proof-grade interval generator.
