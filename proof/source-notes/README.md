# Source theorem notes

This directory contains the source theorem notes for the middle and upper
branches of the three-regime proof of Erdős Problem 625.  All files were
developed in the parent Erdosreshala repository
(https://github.com/uthunderbird/erdosreshala-625, subdirectory
`problems/625/work/notes/`) and are copied here to make this package
self-contained.

## Middle branch

| File | Role |
|------|------|
| `good-branch-partial-away-from-one-theorem-2026-05-13.md` | Source theorem for Regime II (`x in [0.029155, 0.95]`). Proves `chi(G)-zeta(G) -> infinity` using HP-2023 Lemma 7.20 (for `x >= 0.04`) and the A1 certificate (for `x in [0.029155, 0.04)`). |
| `lemma_7_10_ext.md` | A1 numerical certificate (`lemma_7_10_ext`). Certifies phi(1,x,1) > 0 on `[0.029155, 0.04)` via a 2-cell Lipschitz envelope grid. Supports the middle branch for `x in [0.029155, 0.04)`. |
| `a1-good-branch-certificate-table-schema-2026-05-12.md` | Schema for the A1 good-branch certificate table. |
| `a1-certificates/` | Certificate data: `a1_good_branch_certificate_x029155_to_1.csv` (2-row grid), `a1_good_branch_certificate_x029155_to_1_summary.json`, `a1_good_branch_source_table_checker_summary.json`. |

## Upper branch

| File | Role |
|------|------|
| `upper-boundary-r2-integrated-theorem-2026-05-13.md` | Integrated source theorem for Regime III (`x in [0.95,1)`). Main entry point; cites all supporting files below. |
| `upper-boundary-r2-explicit-interval-tables-2026-05-13.md` | Explicit finite interval tables for the R2-G1 certificate. Supplies `Room_2(x) >= 0.07` and `Prefix_2(x) >= 0.006` on `[0.95,1]`. |
| `upper-boundary-r2-directed-certificate-proof-2026-05-13.md` | Limiting certificate proof for the r=2 profile. |
| `upper-boundary-alpha-lower-bound-u8a-closure-2026-05-13.md` | Alpha-bounded chromatic lower bound (U8a). Gives `chi(G) >= boldk_alpha - o(n/log^3 n)`. |
| `upper-boundary-alpha-to-ordinary-transfer-u8b-closure-2026-05-13.md` | Transfer from alpha-bounded to ordinary chromatic number (U8b). |
| `upper-boundary-r2-exact-finite-transfer-g2-closure-2026-05-13.md` | Exact finite transfer from limiting to finite-n margins (G2). |
| `upper-boundary-alpha-first-moment-shift-u3-closure-2026-05-13.md` | First-moment shift theorem (U3). |
| `upper-boundary-r2-rounding-stability-u4-closure-2026-05-13.md` | Rounding stability (U4). Preserves room, prefix, support conditions under rounding. |
| `upper-boundary-r2-c3-source-gate-adapter-2026-05-13.md` | C3 first-moment preservation adapter. |
| `upper-boundary-r2-c5-active-profile-adapter-2026-05-13.md` | C5 active-profile adapter. |
| `upper-boundary-r2-profitable-profile-bridge-g3-closure-2026-05-13.md` | Bridge to cochromatic upper bound (G3). Final assembly giving `zeta(G) <= boldk_alpha - 0.001 n/log^3 n`. |

## Upper branch — C3/C5 logical dependencies

These files are logical inputs cited by the C3 and C5 adapters above.

| File | Role |
|------|------|
| `c5-active-profile-theorem-2026-05-12.md` | C5 active-profile theorem for P3 r=2/r=3 profiles. Closes the C5/P3 interface. Cited by the C5 adapter as "the available theorem." |
| `r4-c5-source-table-2026-05-12.md` | R4 C5 source table. Maps each step of the C5 second-moment calculation to specific HP-2023 and Heckel 2024 lemmas. |
| `c5-source-gate-closure-summary-2026-05-12.md` | C5 source-gate closure summary. Records that all source-table rows are closed. |
| `r4-c3-first-moment-preservation-full-lemma-2026-05-12.md` | R4 C3 first-moment preservation: full lemma. Standalone lemma for C3 used in the C3 adapter. |
| `p3-rounding-stability-room-prefix-lemma-2026-05-13.md` | P3 rounding stability for room and prefix. Supports the rounding stability step (U4). |
| `p3-c3-source-gate-instantiation-2026-05-13.md` | P3 C3 source-gate instantiation. Instantiates the C3 lemma for the rounded P3 profile. |
