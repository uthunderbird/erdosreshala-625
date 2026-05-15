# P3 r=2/r=3 limiting certificate summary, 20 cells, x0=0.029155

Date: 2026-05-12

## Purpose

This note records the extended P3 limiting certificate used to remove the
numerical handoff gap between the low-parameter P3 branch and the older A1
good-branch interval.

The earlier accepted certificate covered:

```text
[0, 0.02905].
```

The extended certificate covers:

```text
[0, 0.029155].
```

This reaches beyond the older good-branch start near:

```text
0.02915439...
```

and therefore removes the numerical P3/A1 coverage gap, conditional on the A1
good-branch certificate and source transcription being accepted.

## Generation command

```bash
python3 ../../problems/625/work/scripts/p3_r23_limiting_interval_slice1.py \
  --x0 0.029155 \
  --x-cells 20 \
  --imax 40 \
  --precision 60 \
  > ../../problems/625/work/certificates/p3_r23_limiting_certificate_20cells_x029155.csv
```

## Checker command

```bash
python3 ../../problems/625/work/scripts/p3_check_r23_limiting_certificate_table.py \
  ../../problems/625/work/certificates/p3_r23_limiting_certificate_20cells_x029155.csv \
  --x0 0.029155 \
  --required-r 2,3 \
  > ../../problems/625/work/certificates/p3_r23_limiting_checker_summary_20cells_x029155.json
```

## Checker result

```json
{
  "accepted_total": 40,
  "coverage_ok": true,
  "row_count": 60,
  "required_r": ["2", "3"],
  "by_r": {
    "2": {
      "accepted_row_count": 20,
      "coverage_ok": true,
      "covered_right": "0.029155",
      "gaps": [],
      "room_lower": "0.20524649344743071159912805570809451710084762536188230905481",
      "prefix_phi_lower": "0.00341556839776615331879952959055730495911103659264007531908512",
      "variance_lower": "1.0114529275630466999152305859776114352860621637324136238160",
      "tail_ratio_upper": "4.52618221309741830497754249599044824109796018848677134760509E-12"
    },
    "3": {
      "accepted_row_count": 20,
      "coverage_ok": true,
      "covered_right": "0.029155",
      "gaps": [],
      "room_lower": "0.04778972292697220321441354125115224858635559095223967517684",
      "prefix_phi_lower": "0.00688130430056587986588569019855730495911103659264007531908512",
      "variance_lower": "0.2857952114070963206574892765684860605401666873034962204537",
      "tail_ratio_upper": "3.46449571051302872924119767011152859021772094841705080773380E-12"
    }
  }
}
```

## SHA256

```text
a1ace3ae845c6bde27b3077aab13a3826d0daf093ff6d98a45ff62c522586531  work/scripts/p3_r23_limiting_interval_slice1.py
a762a3d35dff32e2942759cf19130400e6d6f8afcb203b2a25d35b4481e2080d  work/scripts/p3_check_r23_limiting_certificate_table.py
7aa8fff835985321cdb58ffb99cad8aebaeb05e9baea42acf216e6ea21e09914  work/certificates/p3_r23_limiting_certificate_20cells_x029155.csv
2bfcbc15a17e39a932d77db5631316929ed4c702cd4b3c5776e7da107f667f13  work/certificates/p3_r23_limiting_checker_summary_20cells_x029155.json
```

## Gate impact

This closes the numerical P3 side of the handoff gap up to `0.029155`.

It does not close G2, because the A1 side still requires:

```text
proof-grade A1 phi certificate,
HP/Heckel source transcription,
accepted A1 overlap rows.
```

