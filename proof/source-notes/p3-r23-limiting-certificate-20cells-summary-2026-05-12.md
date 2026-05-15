# P3 `r=2,3` limiting certificate 20-cell summary

Date: 2026-05-12

## Purpose

This is the first accepted hard certificate artifact for the active P3
endpoint route.

It certifies the limiting `r=2` and `r=3` room/prefix margins on:

```text
x in [0,0.02905].
```

## Artifacts

Generator:

```text
work/scripts/p3_r23_limiting_interval_slice1.py
```

Checker:

```text
work/scripts/p3_check_r23_limiting_certificate_table.py
```

Certificate CSV:

```text
work/certificates/p3_r23_limiting_certificate_20cells.csv
```

Checker summary:

```text
work/certificates/p3_r23_limiting_checker_summary_20cells.json
```

## Command

```text
python3 work/scripts/p3_r23_limiting_interval_slice1.py \
  --x-cells 20 --imax 40 --precision 60 \
  > work/certificates/p3_r23_limiting_certificate_20cells.csv

python3 work/scripts/p3_check_r23_limiting_certificate_table.py \
  work/certificates/p3_r23_limiting_certificate_20cells.csv \
  --x0 0.02905 --required-r 2,3 \
  > work/certificates/p3_r23_limiting_checker_summary_20cells.json
```

## Accepted checker result

The checker reports:

```text
coverage_ok=true,
accepted_total=40,
r=2 accepted_row_count=20,
r=3 accepted_row_count=20.
```

Extracted constants:

```text
r=2:
  room_lower = 0.20526289172920852206570618646162673039440124600608892610080
  prefix_phi_lower = 0.00341556839776615331879952959055730495911103659264007531908512
  variance_lower = 1.0114636144979313077134334636031264517590440860007440190762

r=3:
  room_lower = 0.04783406012929202212439954401623557991327683115639675195243
  prefix_phi_lower = 0.00688130430056587986588569019855730495911103659264007531908512
  variance_lower = 0.2858298412051926627128900197844206596066960718510870627892
```

Tail ratios:

```text
r=2 tail_ratio_upper = 4.52619160650350624946213080829672290337184676087904086577416e-12
r=3 tail_ratio_upper = 3.46450732535451226665040517697971658527800552018235486915297e-12
```

## SHA256 hashes

```text
a1ace3ae845c6bde27b3077aab13a3826d0daf093ff6d98a45ff62c522586531  work/scripts/p3_r23_limiting_interval_slice1.py
a762a3d35dff32e2942759cf19130400e6d6f8afcb203b2a25d35b4481e2080d  work/scripts/p3_check_r23_limiting_certificate_table.py
2c177e60a76cdb9dd248fcababa4efbf33f02954fdc24b1fb94af797ed900989  work/certificates/p3_r23_limiting_certificate_20cells.csv
95ead5b85ddaae41aa69b3979f4b90a559883b0d41623a68b14bab25099b72f5  work/certificates/p3_r23_limiting_checker_summary_20cells.json
```

## Caveat

This closes the limiting certificate milestone only.  It does not by
itself close G4, because the exact finite-`d_u` large-anchor transfer and
exact certificate layer still need to be connected.

## Status

Accepted limiting certificate artifact for `r=2,3`.

