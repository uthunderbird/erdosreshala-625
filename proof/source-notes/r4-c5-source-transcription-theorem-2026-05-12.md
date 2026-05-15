# R4 C5 source transcription theorem

Date: 2026-05-12

## Purpose

This note states the exact source-transcription theorem needed to close
`C5-SOURCE-GATE`.

The mathematical C5 lemma is already isolated in

```text
r4-c5-co-tame-second-moment-full-lemma-2026-05-12.md
```

but the final proof must justify that the HP/Heckel second-moment estimates
used there do not smuggle in the ordinary expectation lower bound that
fails in the low-`mu_alpha` regime.

## Theorem to transcribe

Let `bf{k}` be the rounded constrained `alpha-1` profile certified by the
R4 interval certificate.  Assume:

```text
tail condition,
B/C/D restricted relevance,
C2: E[X^co] >= exp(c n/log n),
C3: E[Z^co]~E[X^co],
C4: lower-boundbeta,
scrambled corrections M_A+M_B=O(1).
```

Then HP/Heckel's pair decomposition implies

```text
E[(Z^co)^2]/E[Z^co]^2 <= exp(O(log^2 n)).
```

## Required source claims

### Claim S1: B/C/D fixed-partition restrictions

The source proof of

```text
P(not B_pi | A_pi)=o(1),
P(not C_pi | A_pi)=o(1),
P(not D_pi | A_pi)=o(1)
```

uses only fixed-partition conditional estimates and the profile tail
condition.

It does not use:

```text
E[X] large,
lower-boundbeta,
ordinary tameness.
```

This claim feeds C3.

### Claim S2: scrambled estimate dependencies

The scrambled-pair estimate, after imposing `B/C/D` relevance, depends only
on:

```text
tail condition,
correction terms M_A,M_B,
model-transfer loss.
```

The final bound may be written as

```text
scrambled contribution <= exp(O(M_A+M_B+log^2 n)).
```

For the R4 profile, the certificate/source calculation must prove

```text
M_A+M_B=O(1)
```

or at least `o(log^2 n)`.

### Claim S3: middle estimate dependencies

The middle-overlap estimate uses lower-boundbeta as its only macroscopic
positivity input.

Thus C4 may replace ordinary tameness in this range.

The source transcription must identify the exact step where lower-boundbeta
is invoked and verify that no ordinary expectation lower bound is also
required.

### Claim S4: similar estimate denominator

The cocolouring similar-overlap estimate has denominator

```text
E[X^co]
```

or, after restriction,

```text
E[Z^co]~E[X^co].
```

The source enumeration before this denominator uses only:

```text
tail condition,
similarity/relevance structure,
factor 2^(2k-ell).
```

Therefore C2 and C3 imply the similar contribution is `o(1)`.

### Claim S5: G(n,m) to G(n,1/2) transfer

Every transfer between fixed-edge and binomial random graph models costs at
most

```text
exp(O(log^2 n)).
```

The transfer hypotheses are satisfied by the rounded constrained profile.

## No-hidden-ordinary-expectation audit

The transcription must explicitly mark every occurrence of the following in
the source proof:

```text
E[X],
E[Z],
tame,
lower-boundbeta,
similar,
scrambled,
middle.
```

For each occurrence, record whether it is:

```text
allowed: replaced by C2/C3/C4,
allowed: fixed-partition/tail-only,
forbidden: ordinary expectation lower bound.
```

The theorem is accepted only if there are no forbidden occurrences.

## Output artifact required

The final proof should include a table:

```text
source lemma/line,
range (B/C/D, scrambled, middle, similar, transfer),
source hypothesis,
R4 replacement,
status.
```

Working table and checker:

```text
r4-c5-source-table-2026-05-12.md
work/scripts/check_r4_c5_source_table.py
c5-active-profile-source-split-2026-05-12.md
```

The checker must report `gate_closed=true` before C5 source transcription is
accepted.

## Current status

This theorem is a specification, not a completed transcription.  The source
table exists but currently has unresolved rows.  The P3/SHIFT endpoint
split removes the conceptual scrambled blocker, but the final source table
still has to include active-profile rows for the `r=2` and `r=3`
omitted-top profiles.
