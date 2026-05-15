# G4 finite-objective closure theorem

Date: 2026-05-12

## Purpose

This note packages the accepted limiting `r=2/r=3` certificate together
with the exact finite-`d_u` large-anchor transfer lemmas.

It is the theorem that should close G4 once its asymptotic transfer
bookkeeping is accepted in the final proof.

## Inputs

### Input 1: accepted limiting certificate

The accepted certificate used in the final splice is:

```text
p3-r23-limiting-certificate-20cells-x029155-summary-2026-05-12.md
work/certificates/p3_r23_limiting_certificate_20cells_x029155.csv
work/certificates/p3_r23_limiting_checker_summary_20cells_x029155.json
```

It proves, for `x in [0,0.029155]`:

```text
Room_2(x) >= 0.2052464934...,
Prefix_2(x) >= 0.0034155683...,
Room_3(x) >= 0.0477897229...,
Prefix_3(x) >= 0.0068813043....
```

### Input 2: exact finite-`d_u` expansion

From:

```text
exact-du-large-anchor-expansion-2026-05-12.md
```

for integer anchor parameter `A`:

```text
H_A(i)=-(log2/2)i(i-1)+sum_{j=1}^{i-1}log(1-j/A),
```

and for `i<=A/2`:

```text
|H_A(i)+(log2/2)i(i-1)| <= i(i-1)/A.
```

### Input 3: compactness transfer

From:

```text
exact-du-large-anchor-compactness-lemmas-2026-05-12.md
g4-finite-transfer-quantifier-proof-2026-05-12.md
g4-finite-transfer-publication-closure-2026-05-12.md
```

the exact finite-`A` tilted profiles converge uniformly to the limiting
profiles in:

```text
mean solver,
total variation on fixed windows,
objective J,
prefix Phi endpoint values.
```

## Theorem

There exists `A0` such that for all integer anchors `A>=A0`, all
`x in [0,0.029155]`, and `r in {2,3}`, the exact finite-`d_u` profile
satisfies:

```text
Room_A^{(r)}(x) >= R_r^exact > 0,
Prefix_A^{(r)}(x) >= c_r^exact > 0.
```

One may take, non-optimally:

```text
R_2^exact = 0.1,
R_3^exact = 0.02,
c_2^exact = 0.001,
c_3^exact = 0.003.
```

after increasing `A0` sufficiently.

## Proof

The accepted limiting certificate supplies strictly positive margins:

```text
R_2, R_3, c_2, c_3 > 0.
```

The large-anchor expansion gives pointwise convergence of the exact
centered exponent to the limiting exponent on every finite deficit window.

The compactness lemmas upgrade this to uniform convergence on:

```text
x in [0,x0],
r in {2,3},
all prefix endpoints used by the certificate.
```

Choose the Gaussian tail cutoff `I` and then `A0` so that the total
perturbation of every certified room and prefix value is less than half the
corresponding limiting margin.  Then for all `A>=A0`:

```text
Room_A^{(r)} >= Room_r/2,
Prefix_A^{(r)} >= Prefix_r/2.
```

The displayed conservative constants are below half the accepted limiting
margins, so they are valid after enlarging `A0`.

## Consequence

The finite-objective obstruction from the non-uniform Stirling shortcut is
removed for the standard endpoint route.  P3 may use exact finite-`d_u`
room/prefix margins for `r=2/r=3` at all sufficiently large active anchors.

## Remaining integration

This theorem closes the mathematical G4 finite-objective issue modulo the
standard compactness lemmas now expanded in:

```text
g4-finite-transfer-quantifier-proof-2026-05-12.md
```

The publication form is closed in:

```text
g4-finite-transfer-publication-closure-2026-05-12.md
```

The final integrated proof must still:

```text
1. cite the accepted limiting certificate bundle;
2. cite this transfer theorem;
3. use the resulting exact margins in C5 and the P3 endpoint theorem.
```

G5 is closed as source-dependency classification.  G7 remains open until the
final integrated proof cites this theorem without conditional gate language.
