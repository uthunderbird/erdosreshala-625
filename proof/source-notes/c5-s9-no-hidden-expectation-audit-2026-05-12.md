# C5 S9 no-hidden ordinary-expectation audit

Date: 2026-05-12

## Purpose

This note discharges the remaining S9 source-table row:

```text
every occurrence of ordinary E[X] in the HP/Heckel second-moment proof
must be absent or replaced by active C2/C3/C4 hypotheses.
```

## Audit principle

The active C5 proof never imports a global ordinary-colouring expectation
lower bound.  Instead:

```text
C2 supplies the cocolouring first moment E[X^co],
C3 supplies E[Z^co] ~ E[X^co] after B/C/D restrictions,
C4 supplies lower-boundbeta / prefix positivity for middle overlaps,
tail/relevance hypotheses supply fixed-partition estimates,
active-profile split supplies scrambled-scale control.
```

## Occurrence table

| Source occurrence | Range | Ordinary expectation role | Active replacement | Status |
|---|---|---|---|---|
| First moment denominator in similar range | similar | denominator must be large | C2 + C3 give `E[Z^co]` large | OK |
| lower-boundbeta in middle range | middle | positivity input for overlap profile | C4 prefix positivity from accepted P3 certificate | OK |
| B/C/D bad event preservation | fixed partition | none; conditional on a fixed partition | tail/relevance fixed-partition estimates + C3 | OK |
| scrambled pair estimate | scrambled | none; depends on `mu_s`, profile coordinates, correction terms | active split P-S3a/b/c + correction theorem | OK |
| G(n,m) to G(n,1/2) transfer | transfer | none beyond model probability ratios | exp(O(log^2 n)) transfer absorbed in parameterized Q | OK |

## Active replacements

The following artifacts provide the replacements:

```text
p3-r23-limiting-certificate-20cells-summary-2026-05-12.md
g4-finite-objective-closure-theorem-2026-05-12.md
c5-active-profile-source-split-2026-05-12.md
c5-scrambled-correction-active-r23-2026-05-12.md
r4-parameterized-second-moment-amplification-2026-05-12.md
```

## S9 conclusion

For the active proof route, there is no remaining use of an ordinary
expectation lower bound in C5.  Every source occurrence is either:

```text
replaced by C2/C3/C4,
fixed-partition/tail-only,
or controlled by the active scrambled-scale split.
```

## Caveat

This audit is a source-transcription claim.  A final paper should still
quote the relevant HP/Heckel lemma statements around scrambled, middle, and
similar ranges.  The purpose here is to close the dependency classification
gate, not to reproduce the full paper proof verbatim.

