# R4 C5 co-tame second moment: full conditional lemma

Date: 2026-05-12

## Purpose

This note isolates C5 for the active R4 route.  It is not the older
alpha-minus-two A4-prime proposition.  The ambient profile here is the
low-regime constrained `alpha-1` profile, and the goal is exactly the
second-moment input used in
`r4-low-regime-cochromatic-proof-draft-2026-05-12.md`.

## Target lemma

Let `bf{k}` be a rounded constrained low-regime `alpha-1` profile satisfying
C1--C4:

1. `bf{k}` has all nonzero sizes in `u_* <= u <= alpha-1`, with
   `u_* = alpha-o(alpha)`;
2. `|bf{k}| = Theta(n/log n)`;
3. `bf{k}` satisfies the HP tail condition;
4. the cocolouring first moment is large:

   ```text
   E[X_bf{k}^co] >= exp(c_1 n/log n);
   ```

5. the restricted first moment satisfies C3:

   ```text
   E[Z_bf{k}^co] = (1-o(1)) E[X_bf{k}^co];
   ```

6. the lower-boundbeta/prefix-positivity condition holds for every fixed
   `delta>0`.

Then

```text
E[(Z_bf{k}^co)^2] / E[Z_bf{k}^co]^2 <= exp(O(log^2 n)).
```

Consequently,

```text
P[Z_bf{k}^co>0] >= exp(-O(log^2 n)).
```

## Pair decomposition

For two labelled partitions `pi,pi'` with profile `bf{k}`, let `ell` be
the number of common parts and let `lambda` denote the corresponding
overlap mass.  Relevant pairs are those which can satisfy the restricted
events for both partitions.

Use the HP/Heckel decomposition:

```text
scrambled: lambda < log^{-3} n,
middle:    log^{-3} n <= lambda <= 1-n^{-c_0},
similar:   lambda > 1-n^{-c_0},
```

where `c_0>0` is fixed sufficiently small.  HP's similar-overlap argument
is valid for arbitrary fixed `c_0>0`, so this split can be made without
changing the asymptotic scale of the R4 proof.

For each range, compare the cocolouring pair probability with the ordinary
pair probability by Heckel's transfer inequality

```text
P(A_pi^co cap A_pi'^co)
  <= 2^{2k-ell} P(A_pi^- cap A_pi'^-),
```

where `k=|bf{k}|`.  The same inequality applies after imposing the
restricted events, since restrictions can only reduce the left-hand side.

## Scrambled range

HP's scrambled-pair estimate uses:

1. the profile size range;
2. the tail condition;
3. the relevant-pair restrictions supplied by `B,C,D`;
4. finite correction terms `M_B,M_A`.

It does not use the global ordinary first moment except through the
normalization by the restricted count.  In the cocolouring version, the
normalization is supplied by C3 and C2:

```text
E[Z_bf{k}^co] >= exp((c_1/2)n/log n).
```

The Heckel cocolouring factor `2^{2k-ell}` is exactly the factor already
accounted for in the cocolouring scrambled estimate.  After the standard
`G(n,m)` to `G(n,1/2)` transfer loss, the scrambled contribution is bounded
by

```text
exp(O(M_A+M_B+log^2 n)).
```

For the low-regime `alpha-1` profile the certificate must include the
finite estimates

```text
M_A+M_B = O(1),
```

or more strongly `o(log^2 n)`.  Since all profile coordinates satisfy
`k_u <= O(n/log n)` and the profile has the HP tail condition, this is
expected to follow by the same calculation as in the alpha-minus-two
audit, with `alpha-1` replacing `alpha-2`.

Thus the scrambled range contributes at most

```text
exp(O(log^2 n)).
```

## Middle range

The middle-overlap contribution is the range in which lower-boundbeta is
used.  The required input is precisely C4: every macroscopic partial
profile has positive exponent uniformly for every fixed `delta>0`.

With C4, HP's middle estimate applies to the ordinary pair count for
relevant pairs.  Heckel's cocolouring transfer introduces only the
`2^{2k-ell}` factor and the standard `G(n,m)`/`G(n,1/2)` loss.  The same
normalization by `E[Z_bf{k}^co]^2` is valid by C3.

Therefore the middle range contributes at most

```text
exp(O(log^2 n)).
```

This is the most delicate part of C5 because it is only as strong as C4:
if prefix positivity fails at any macroscopic partial profile, the middle
range can dominate.

## Similar range

In the similar range, HP/Heckel's enumeration gives, after cocolouring
transfer,

```text
sum_similar P(A_pi^co cap A_pi'^co cap R_pi cap R_pi')
  <= exp(O(n^{1-c_0}/log n)) E[X_bf{k}^co].
```

Dividing by `E[Z_bf{k}^co]^2` and using C3 gives

```text
similar contribution
  <= exp(O(n^{1-c_0}/log n)) / E[X_bf{k}^co].
```

By C2,

```text
E[X_bf{k}^co] >= exp(c_1 n/log n).
```

Since `n^{1-c_0}/log n = o(n/log n)`, the similar contribution is

```text
exp(-(c_1+o(1))n/log n) = o(1).
```

This range therefore does not threaten the `exp(O(log^2 n))` bound.

## Combination

Adding the three ranges gives

```text
E[(Z_bf{k}^co)^2]
  <= exp(O(log^2 n)) E[Z_bf{k}^co]^2.
```

Paley-Zygmund then yields

```text
P[Z_bf{k}^co>0]
  >= E[Z_bf{k}^co]^2 / E[(Z_bf{k}^co)^2]
  >= exp(-O(log^2 n)).
```

This proves C5 conditional on the HP/Heckel pair estimates and C1--C4.

## Remaining audit points

The lemma above identifies the remaining source-check obligations for C5:

1. Transcribe the exact HP scrambled estimate and verify that its `M_A,M_B`
   terms remain `O(1)` for the rounded constrained `alpha-1` profile.
2. Transcribe the exact HP middle estimate and verify that its only
   macroscopic positivity input is C4.
3. Transcribe the exact HP/Heckel similar estimate and verify the displayed
   denominator is `E[X_bf{k}^co]`, not an ordinary-colouring first moment.
4. Check the `G(n,m)` to `G(n,1/2)` transfer loss is at most `exp(O(log^2 n))`
   in all three ranges.
5. Verify that the restrictions used in pair relevance are exactly those
   preserved by the C3 `B,C,D` lemma and its clique analogue.

## Status

C5 is reduced to source transcription plus two quantitative checks:

1. the scrambled correction bound `M_A+M_B=O(1)` for the rounded
   constrained `alpha-1` profile;
2. the C4 lower-boundbeta certificate.

The only genuinely new hard input inside C5 is therefore C4.  If C4 is
proved and the correction terms are bounded, the rest of C5 is a controlled
adaptation of HP/Heckel.
