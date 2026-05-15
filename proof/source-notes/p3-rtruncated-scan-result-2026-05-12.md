# P3 r-truncated scan result

Date: 2026-05-12

## Command

```text
python3 work/scripts/p3_rtruncated_scan.py --x-grid 80 --imax 220 --r-max 10
```

Exploratory floating-point computation, not proof evidence.

## Output summary

```text
r  min_room       min_prefix
1   0.2402265    -0.0001789
2   0.2186789     0.0034155
3   0.0658963     0.0068813
4  -1.2510872     0.0103470
5  -4.3702495     0.0138128
...
```

## Interpretation

The r-truncated cascade remains first-moment viable for:

```text
r=2, r=3.
```

It fails at:

```text
r>=4
```

because the first-moment room becomes negative.  Prefix positivity improves
with larger `r`, so the obstruction is first-moment room, not lower-boundbeta.

## Consequence

The endpoint cascade can at most use:

```text
largest occupied size alpha-2  (r=2),
largest occupied size alpha-3  (r=3).
```

The `r=3` profile has smaller but still positive room:

```text
Room_3 >= about 0.0659.
```

Thus it can still give a cochromatic saving of order `n/log^3 n`, with a
smaller constant.

## Coverage estimate

For an `r`-truncated profile, the leading scrambled condition is:

```text
mu_{alpha-r} >> n log^4 n.
```

For `r=3`, this is:

```text
mu_{alpha-3} >> n log^4 n.
```

Using the heuristic ratio

```text
mu_{alpha-3}
  ~= mu_{alpha-1} * (n/log n)^2 * exp(O(1)),
```

this condition corresponds roughly to:

```text
mu_{alpha-1} >> log^6 n / n.
```

Since `mu_{alpha-1}` is an expectation and may be much smaller along some
subsequences, the remaining micro-endpoint is where

```text
mu_{alpha-1} <=~ log^6 n / n.
```

In that range, independent sets of size `alpha-1` are extremely rare.  It
may require a different argument, but it is much narrower than the original
residual endpoint.

## Important caveat

The heuristic ratios between `mu_{alpha-r}` values must be replaced by
source-backed asymptotics.  The scan only establishes that the profile
room/prefix side remains plausible for `r=3`.

## Next route

Build endpoint proof in layers:

```text
L2a: use r=2 when mu_{alpha-2} >> n log^4 n;
L2b: use r=3 when mu_{alpha-2} is too small but mu_{alpha-3} >> n log^4 n;
L2c: micro-endpoint below that threshold needs a separate argument.
```

## Status

The cascade helps but does not obviously cover every possible endpoint.
The full prize proof still has a micro-endpoint blocker unless a separate
argument handles extremely small `mu_{alpha-1}`.
