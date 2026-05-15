# Upper-boundary r=2 numeric certificate check result

Date: 2026-05-13

## Purpose

This note records the numeric check for the `R2-G1` directed interval
certificate target.

Checker:

```text
work/scripts/upper_boundary_r2_certificate_check.py
```

Specification:

```text
upper-boundary-r2-directed-interval-certificate-spec-2026-05-13.md
```

## Command

```text
python3 work/scripts/upper_boundary_r2_certificate_check.py
```

## Output

```json
{
  "all_numeric_targets_pass": true,
  "grid_step": 0.001,
  "guard_target_pass": true,
  "imax": 80,
  "min_guard_delta": {
    "value": 0.006708017505425904,
    "x": 0.95
  },
  "min_guard_one_minus_delta": {
    "value": 0.036478134679873785,
    "x": 0.95
  },
  "min_non_tight_prefix": {
    "endpoint": "guard_one_minus_delta",
    "value": 0.036478134679873785,
    "x": 0.95
  },
  "min_p2_grid": {
    "value": 0.37393753723673995,
    "x": 0.95
  },
  "non_tight_target_pass": true,
  "p2_denominator_upper_mu_1_75": 2.684132621643932,
  "p2_lower_from_mu_1_75": 0.37255983252702957,
  "p2_target_pass": true,
  "room_at_1": 0.07518167521885649,
  "room_target_pass": true,
  "status": "NUMERIC_EVIDENCE_NOT_DIRECTED_INTERVAL_PROOF"
}
```

## Interpretation

The numeric check confirms the intended certificate shape:

```text
Room_2(1) ~= 0.075181675 > 0.07;
Phi_{0.95}(0.01 e_2) ~= 0.0067080175 > 0.006;
p_2(x) >= 0.3725 by the mu<=1.75 denominator bound;
all non-tight prefix endpoints are >=0.03647 on the sampled grid.
```

The tight prefix endpoint is:

```text
q=0.01 e_2,
x=0.95.
```

The next-smallest checked prefix endpoint has much larger margin:

```text
Phi_{0.95}(1-delta) ~= 0.03648.
```

## Proof status

This is not yet a proof-grade directed interval certificate because the
script uses ordinary floating-point `math.exp` and `math.log`, and the grid
check is not outward-rounded interval arithmetic.

What remains to close `R2-G1`:

```text
1. replace ordinary floats by directed interval enclosures, or write the
   endpoint inequalities analytically with explicit rational/log/exp bounds;
2. certify the monotonic reductions already isolated in:
   upper-boundary-r2-room-monotonicity-certificate-2026-05-13.md
   upper-boundary-r2-prefix-guard-reduction-2026-05-13.md;
3. interval-bound the non-tight prefix endpoint list over [0.95,1].
```

## Status

`R2-G1` is numerically confirmed but not yet closed.
