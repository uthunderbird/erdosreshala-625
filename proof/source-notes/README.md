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
| `good-branch-partial-away-from-one-theorem-2026-05-13.md` | Source theorem for Regime II (`x in [0.029155, 0.95]`). Proves `chi(G)-zeta(G) -> infinity` using the HP/Heckel good-branch source theorem. |

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
