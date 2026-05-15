# P3 `p1=0` scan result

Date: 2026-05-12

## Command

```text
python3 work/scripts/p3_p1zero_scan.py --x-grid 80 --imax 160
```

This is exploratory floating-point evidence, not a proof certificate.

## Result

Across the grid `x in [0,x0]`:

```text
min Room_0(x) ~= 0.21867891935
min prefix margin ~= 0.00341556839
p1=0 identically
p2 ranges roughly from 0.1086 to 0.1134
```

Worst room occurs at `x=x0`:

```text
x=0.02905,
room=0.21867891935,
min_prefix=0.00351624803.
```

Worst prefix margin occurs at `x=0`:

```text
x=0,
room=0.219981083465,
min_prefix=0.00341556839777.
```

## Interpretation

The `p1=0` endpoint profile appears uniformly viable:

1. first-moment room remains strongly positive;
2. prefix positivity remains positive;
3. the top-size scrambled term for size `alpha-1` vanishes.

The endpoint proof can therefore aim to use an effective maximum occupied
size

```text
a_eff = alpha-2.
```

This avoids the residual blocker caused by

```text
(k_{alpha-1}^{profile})^2 / mu_{alpha-1}.
```

## New technical requirement

The second-moment source transcription must support applying HP scrambled,
middle, and similar estimates to a profile with:

```text
anchor: k_{alpha-1},
largest occupied class size: alpha-2.
```

This is different from the earlier failed alpha-minus-two route:

1. ordinary lower bound stays at `k_{alpha-1}`;
2. only the cocolouring profile has no `alpha-1` parts;
3. the cochromatic saving is measured below `k_{alpha-1}` using the
   cocolouring first-moment room.

## Next proof target

Build a `p1=0` endpoint certificate theorem:

1. certify `Room_0(x)>0`;
2. certify prefix positivity;
3. prove finite rounding with no `alpha-1` parts;
4. prove C5 with `a_eff=alpha-2`;
5. integrate with endpoint ordinary lower bound.

## Status

The `p1=0` route is now the leading candidate for closing the residual
endpoint.  It still requires an interval certificate and HP/Heckel source
adaptation.
