# C5 source gate closure summary

Date: 2026-05-12

## Purpose

Record the accepted source-table checker result for `C5-SOURCE-GATE`.

## Artifacts

Source table:

```text
work/notes/r4-c5-source-table-2026-05-12.md
```

Checker:

```text
work/scripts/check_r4_c5_source_table.py
```

Checker summary:

```text
work/certificates/r4_c5_source_table_checker_summary.json
```

## Checker result

```json
{
  "accepted_count": 11,
  "active_profile_row_count": 3,
  "active_profile_unresolved_ids": [],
  "blocked_count": 0,
  "gate_closed": true,
  "legacy_row_count": 8,
  "legacy_unresolved_ids": [],
  "open_count": 0,
  "row_count": 11,
  "unresolved_ids": []
}
```

## SHA256 hashes

```text
90942b975c884cfc8b0d22044ba2a9290738093bcf2aaf921d1cb97c5a886bc0  work/notes/r4-c5-source-table-2026-05-12.md
31d9a94c4ca8b8397aca006b554caa33c65ca5e19226ab717a11575a86f05411  work/scripts/check_r4_c5_source_table.py
49708bb9ebfae4ffbf29b9e50504693b158b8b390f73234c6f2ce632db05c46c  work/certificates/r4_c5_source_table_checker_summary.json
```

## Interpretation

The active C5 source dependency classification is closed:

```text
no OPEN rows,
no BLOCKED rows,
active P-S3a/P-S3b/P-S3c rows accepted,
S9 no-hidden ordinary expectation audit accepted.
```

This does not prove the whole prize theorem by itself.  It closes the
source-dependency gate needed by the P3/R4 second-moment amplification.

The active mathematical interface theorem is:

```text
c5-active-profile-theorem-2026-05-12.md
```
