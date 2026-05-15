# R4 C5 HP/Heckel source table

Date: 2026-05-12

## Purpose

This is the working source table for closing `C5-SOURCE-GATE`.

It implements the audit required by
`r4-c5-source-transcription-theorem-2026-05-12.md`: every HP/Heckel
second-moment dependency used in C5 must be classified as either replaced
by R4 hypotheses or forbidden.

## Status legend

```text
OPEN          exact source passage not yet pasted/transcribed;
OK-TAIL       uses only tail/fixed-partition/relevance hypotheses;
OK-C2         replaced by E[X^co] lower bound;
OK-C3         replaced by E[Z^co]~E[X^co];
OK-C4         replaced by lower-boundbeta/prefix positivity;
OK-TRANSFER   model-transfer loss accepted as exp(O(log^2 n));
RETIRED       source row belongs to a route no longer used in that regime.
BLOCKED       hidden ordinary E[X] lower bound remains.
```

## Source table

| ID | Range | Source mechanism | Source dependency to transcribe | R4 replacement | Status |
|---|---|---|---|---|---|
| S1 | B/C/D | Fixed-partition bad-event bounds | Heckel 2024 defines `B_pi,C_pi,D_pi` and cites HP Lemmas 5.1--5.3: `P(not B_pi\|A_pi)=o(1)`, etc.; then transfers to cocolouring by monotonicity and clique symmetry. | C3 fixed-partition preservation lemma; tail condition | OK-C3 |
| S2 | cocolouring transfer | Pair probability comparison | Heckel 2024 Proposition `prop:probabilities`: `P(A_pi^co)=2^k P(A_pi)` and `P(A_pi^co cap A_pi'^co) <= 2^(2k-ell)P(A_pi cap A_pi')`. | Heckel transfer; no ordinary expectation input | OK-TAIL |
| S3 | scrambled legacy | Scrambled pair estimate | HP Lemma 6.3: contribution `<= exp(k_a^2/mu_a+O(M))`; Heckel `lemmascrambledco` transfers to cocolourings with extra `exp(O(log^2 n))`. | Retired as full-low-regime row; active split uses P-S3a/b/c. | RETIRED |
| S4 | scrambled legacy | Correction terms | HP defines `M=M_B+M_A`, with explicit formulas for `M_B`, `M_A` in Lemma 6.3; see `r4-c5-scrambled-corrections-lemma-2026-05-12.md`. | Retired as full-low-regime row; active split uses P-S3a/b/c and `c5-scrambled-correction-active-r23`. | RETIRED |
| S5 | middle | Middle-overlap estimate | HP Lemma 6.4 assumes lower-boundbeta and gives middle contribution `o(1)`; Heckel `lemmamiddleco` transfers with `exp(O(log^2 n))`. | C4 prefix positivity | OK-C4 |
| S6 | similar | Similar-overlap enumeration | HP proof of Lemma 6.5 works for any `c0>0`; counts similar relevant pairs using tail/relevance and obtains enumeration cost before denominator. | tail/relevance only | OK-TAIL |
| S7 | similar | Similar denominator | Heckel `lemmasimilarco` concludes similar contribution `<= exp(O(n^(1-c0)/log n))/E_{1/2}[bar X^co_k]`. | C2 + C3 | OK-C2 |
| S8 | model transfer | `G(n,m)` to `G(n,1/2)` | Heckel equation `eq:gnhtransfer` gives probability and expectation ratios `exp(O(log^2 n))`. | absorbed in C5 bound | OK-TRANSFER |
| S9 | global | No ordinary expectation dependency | every occurrence of ordinary `E[X]` in source proof | `c5-s9-no-hidden-expectation-audit-2026-05-12.md`: replaced by C2/C3/C4, fixed-partition/tail-only, or active scrambled split | OK-C2 |

## Active-profile split update

The `BLOCKED` S3/S4 rows are not a blocker for the final architecture if
the source theorem is applied only in the profile's valid scrambled-scale
regime.  The active split is:

| ID | Regime | Active profile | Scrambled size | Required scale | Status |
|---|---|---|---|---|---|
| P-S3a | B1 | original constrained/top profile | `alpha-1` | `mu_{alpha-1} >> n log^4 n` | OK-TRANSFER |
| P-S3b | B2 | P3 `r=2` omitted-top profile | `alpha-2` | `mu_{alpha-2} >> n log^4 n`; G4 accepted margins; correction theorem gives `Q=o(n/log^6 n)` | OK-C4 |
| P-S3c | B3 | P3 `r=3` omitted-top profile | `alpha-3` | `mu_{alpha-3} >> n log^4 n`; G4 accepted margins; correction theorem gives `Q=o(n/log^6 n)` | OK-C4 |

The conceptual split is recorded in:

```text
c5-active-profile-source-split-2026-05-12.md
```

The active rows P-S3b/P-S3c now have quantitative replacements from:

```text
p3-r23-limiting-certificate-20cells-summary-2026-05-12.md
g4-finite-objective-closure-theorem-2026-05-12.md
c5-scrambled-correction-active-r23-2026-05-12.md
alpha0-floor-endpoint-split-theorem-2026-05-12.md
```

The remaining source obligation is S9: verify there is no hidden ordinary
expectation dependency in applying HP/Heckel rows to the active profiles.

## Parameterized update

The S3/S4 `BLOCKED` status applies to the original target

```text
E[Z^2]/E[Z]^2 <= exp(O(log^2 n))
```

throughout the full low regime.

For the weaker parameterized amplification in

```text
r4-parameterized-second-moment-amplification-2026-05-12.md
```

the direct HP scrambled estimate is sufficient in the subregime

```text
mu_{alpha-1} >> n log^4 n.
```

Thus S3/S4 should be considered:

```text
OK-TRANSFER in L1: mu_{alpha-1} >> n log^4 n,
BLOCKED in L2:    mu_{alpha-1} <= n log^4 n.
```

## Audit notes

### S1 B/C/D

Expected resolution:

```text
OK-TAIL + OK-C3
```

Reason: the C3 full lemma reduces first-moment preservation to
fixed-partition estimates.  The remaining task is exact definition
transcription.

### S3/S4 scrambled

Expected resolution:

```text
OK-TAIL
```

provided the certificate proves:

```text
M_A+M_B=O(1)
```

for the rounded constrained `alpha-1` profile.

This is a quantitative certificate obligation, not merely a source quote.

### S5 middle

Expected resolution:

```text
OK-C4
```

This is the most important no-hidden-dependency check.  If the middle proof
uses ordinary `E[X]` in addition to lower-boundbeta, C5 is not closed.

### S6/S7 similar

Expected resolution:

```text
OK-C2 + OK-C3
```

The similar range should be controlled because

```text
exp(O(n^(1-c0)/log n)) / E[X^co] = o(1).
```

### S8 transfer

Expected resolution:

```text
OK-TRANSFER
```

The final source transcription must state the transfer lemma and its loss.

## Completion rule

`C5-SOURCE-GATE` is closed only when every row has status in:

```text
OK-TAIL,
OK-C2,
OK-C3,
OK-C4,
OK-TRANSFER
```

and no row has status `BLOCKED` or `OPEN`.

## Current conclusion

Most source dependencies are now classified.  The original S3/S4 blocker is
resolved by switching active profiles in the endpoint split.  P-S3b/P-S3c
now have quantitative certificate replacements.  `C5-SOURCE-GATE` remains
open until S9 no-hidden-ordinary-expectation audit is closed and the checker
accepts the table.  See
`c5-active-profile-source-split-2026-05-12.md`,
`c5-scrambled-correction-active-r23-2026-05-12.md`, and
`r4-parameterized-second-moment-amplification-2026-05-12.md`.

S9 audit:

```text
c5-s9-no-hidden-expectation-audit-2026-05-12.md
```
