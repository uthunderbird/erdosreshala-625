# G4 finite-transfer publication closure

Date: 2026-05-12

## Purpose

This note closes the red-team concern that G4 still contained unnamed
compactness constants.

The final proof does not need numerical values for the constants

```text
B, eta_T, v, C, C', C''.
```

It needs only the standard theorem:

```text
positive limiting margins survive exact finite-anchor perturbations for all
sufficiently large anchors.
```

The proof of that theorem is now decomposed in:

```text
g4-finite-transfer-quantifier-proof-2026-05-12.md.
```

## Publication form

In the paper, state the following lemma.

### Lemma: finite-anchor stability

Fix a compact interval:

```text
X=[0,0.029155]
```

and finite set:

```text
R={2,3}.
```

Let the limiting profile and exact finite-anchor profile be defined as in
G4.  If the limiting room and prefix functionals have positive margins on
`X x R`, then there exists `A0` such that the exact finite-anchor room and
prefix functionals have at least half those margins for all `A>=A0`.

### Proof method

Use:

```text
1. compact bracketing of limiting mean solvers;
2. positive variance lower bound on the compact solver range;
3. uniform Gaussian tails for bounded solver parameter;
4. finite-window perturbation |F_A(i)| <= i(i-1)/A;
5. continuity of the room and prefix functionals away from entropy singularities.
```

Every item is elementary and proved in detail in:

```text
g4-finite-transfer-quantifier-proof-2026-05-12.md.
```

## Why explicit numeric constants are unnecessary

The final theorem is asymptotic:

```text
there exists n0 such that for all n>=n0 ...
```

Therefore it is enough to prove:

```text
there exists A0 such that for all A>=A0 ...
```

The constants are used only to choose `A0`.  They do not enter the final
colour-saving constant except through the already-certified limiting margins.

The conservative exact margins:

```text
R_2^exact = 0.1,
R_3^exact = 0.02,
c_2^exact = 0.001,
c_3^exact = 0.003
```

are strictly below half of the accepted limiting margins, so the compactness
lemma guarantees them after enlarging `A0`.

## Optional machine strengthening

If a referee asks for fully explicit `A0`, the existing interval scripts can
be extended to emit:

```text
B, eta_T, v, I, A0
```

but this is not necessary for a standard asymptotic proof.

## Gate impact

G4 is closed in ordinary analytical-proof standards.  It remains open only if
the project demands an explicit numerical `n0`, which the prize claim does
not require.

