# Upper-boundary alpha-anchor r=2 robust candidate

Date: 2026-05-13

## Purpose

This note records a more robust upper-boundary candidate than the primary
`r=1` route.

The `r=1` alpha-anchor omitted-top profile has large room but a very narrow
prefix margin:

```text
room ~= 0.21998,
prefix ~= 0.00324 on [0.95,1].
```

The `r=2` profile gives smaller room but roughly double the prefix margin:

```text
room ~= 0.07518,
prefix ~= 0.00670 on [0.95,1].
```

Since the prefix margin is the narrowest current quantitative bottleneck in
`U1`, the `r=2` profile may be the safer prize-candidate route.

## Profile

Use the alpha-anchor deficit coordinate:

```text
i = alpha-u.
```

The `r=2` profile has:

```text
p_0=p_1=0,
support i>=2,
largest occupied size alpha-2.
```

The mean target remains:

```text
T_alpha(x)=1+2/ln 2-x.
```

On the terminal interval:

```text
x in [0.95,1],
T_alpha(x) in [2/ln 2, 0.05+2/ln 2].
```

Since:

```text
2/ln 2 ~= 2.885 > 2,
```

the `r=2` support is compatible with the mean target throughout the interval.

## Exploratory evidence

Floating scan:

```text
python3 work/scripts/upper_boundary_alpha_anchor_omitted_top_scan.py \
  --x-left 0.95 \
  --x-right 0.999999 \
  --x-grid 80 \
  --imax 220 \
  --r-max 6
```

reported:

```text
r=2:
min_room   ~= 0.0751819864119 near x=1,
min_prefix ~= 0.00670801750543 near x=0.95.
```

This is not proof evidence, but it is strong enough to justify maintaining
`r=2` as a serious route.

## Comparison with r=1

Advantages:

```text
1. Prefix margin is about twice as large.
2. Active largest colour-class size is alpha-2, not alpha-1.
3. C5 scrambled scale becomes mu_{alpha-2}, which is larger than
   mu_{alpha-1} by another factor Theta(n/log n).
4. No alpha or alpha-1 colour classes appear in the cocolouring profile,
   so top-layer source-gate and scrambled penalties should be easier.
```

Cost:

```text
1. First-moment room drops from about 0.21998 to about 0.07518.
2. The finite-transfer and rounding budgets must preserve enough of that
   smaller room to keep exp(c_FM n/log n).
```

Given the current bottleneck, the tradeoff is favorable if finite-transfer
room losses are comfortably below `0.075`.

## Proof-grade certificate target

For a robust certificate, aim for:

```text
Room_2(x) >= 0.07,
Prefix_2(x) >= 0.006,
```

uniformly for:

```text
x in [0.95,1].
```

These targets leave exploratory slack:

```text
room slack   ~= 0.00518,
prefix slack ~= 0.00070.
```

The prefix slack is still not huge, but it is materially better than the
`r=1` target `0.003`.

## Route package

The `r=2` analogue of the upper-boundary theorem uses the same lower-bound
side:

```text
chi(G) >= boldk_alpha-o(n/log^3 n)
```

from:

```text
upper-boundary-alpha-lower-bound-u8a-closure-2026-05-13.md
upper-boundary-alpha-to-ordinary-transfer-u8b-closure-2026-05-13.md
```

The upper-bound side requires the same structural inputs as `r=1`, with the
support shifted to `i>=2`:

```text
R2-U1: interval certificate for room/prefix;
R2-U2: exact finite alpha-anchor transfer with support i>=2;
R2-U3: first-moment shift below boldk_alpha
  (closed in upper-boundary-alpha-first-moment-shift-u3-closure-2026-05-13.md);
R2-U4: rounding stability for consecutive support starting at i=2
  (closed conditionally in upper-boundary-r2-rounding-stability-u4-closure-2026-05-13.md);
R2-U5: C3 fixed-partition source gate for largest size alpha-2
  (closed conditionally in upper-boundary-r2-c3-source-gate-adapter-2026-05-13.md);
R2-U6: C5 active second moment with scrambled scale mu_{alpha-2}.
```

The active second-moment scale is:

```text
mu_{alpha-2}
  = mu_alpha * Theta((n/log n)^2)
  = n^{3-o(1)}/log^2 n
```

in the upper-boundary regime.  Therefore:

```text
k^2/mu_{alpha-2}
  = n^{-1+o(1)}
```

which is negligible compared with any required `n/log^6 n` budget.

The C5 adapter is recorded in:

```text
upper-boundary-r2-c5-active-profile-adapter-2026-05-13.md
```

It closes `R2-U6` conditional on `R2-U1`--`R2-U5`.

## Status

`r=2` is not yet a proved route.

It is now the preferred upper-boundary route because the lower-bound side,
first-moment shift, rounding adapter, C3 adapter, C5 adapter, finite-transfer
adapter, and profitable-profile bridge are all closed or conditionally closed
on one remaining certificate:

```text
R2-G1 proof-grade directed interval certificate.
```

The required certificate is:

```text
Room_2(x) >= 0.07,
Prefix_2(x) >= 0.006
```

uniformly on:

```text
x in [0.95,1].
```

The checker specification is:

```text
upper-boundary-r2-directed-interval-certificate-spec-2026-05-13.md
```

Reduced remaining-gates checklist:

```text
upper-boundary-r2-remaining-gates-checklist-2026-05-13.md
```
