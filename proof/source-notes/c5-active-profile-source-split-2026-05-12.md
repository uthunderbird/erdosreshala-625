# C5 active-profile source split after P3/SHIFT

Date: 2026-05-12

## Purpose

This note resolves the apparent C5 contradiction in the source table:

```text
S3/S4 are blocked for the original alpha-1 constrained profile
when mu_{alpha-1} <= n log^4 n.
```

The active architecture no longer uses that profile in this residual
subregime.  It switches to P3 omitted-top profiles whose largest occupied
size has a larger `mu` by one or two ratio steps.

## Active regimes

Let

```text
N_scr = n log^4 n,
a = alpha-1.
```

The proof uses the following second-moment source inputs.

### B1: original constrained/top profile

Condition:

```text
mu_a = mu_{alpha-1} >> N_scr.
```

Largest occupied size:

```text
alpha-1.
```

HP scrambled source cost:

```text
Q_scr <= O(k_a^2/mu_a + M_A + M_B + log^2 n).
```

Since `k_a=Theta(n/log n)`, the condition gives:

```text
Q_scr = o(n/log^6 n)
```

after absorbing the certified correction terms.  This is enough for
parameterized amplification.

### B2: P3 `r=2` omitted-top profile

Condition:

```text
mu_{alpha-1} <= N_scr,
mu_{alpha-2} >> N_scr.
```

Largest occupied size:

```text
alpha-2.
```

The top `alpha-1` layer has zero profile mass, so the HP scrambled cost is
controlled by:

```text
Q_scr <= O(k_{alpha-2,profile}^2/mu_{alpha-2}
          + M_A^{(2)}+M_B^{(2)}+log^2 n).
```

The exact-`d_u` P3 certificate supplies first-moment room and prefix
positivity; the source proof only needs that the HP pair decomposition is
valid for this rounded profile with largest occupied size `alpha-2`.

The condition `mu_{alpha-2} >> N_scr` again gives:

```text
Q_scr=o(n/log^6 n).
```

### B3: P3 `r=3` omitted-top profile

Condition:

```text
mu_{alpha-2} <= N_scr,
mu_{alpha-3} >> N_scr.
```

Largest occupied size:

```text
alpha-3.
```

The exact `alpha_0` floor asymptotic proves the second condition always
holds in the standard endpoint split when B2 fails:

```text
mu_{alpha-3} >> N_scr.
```

The scrambled cost is:

```text
Q_scr <= O(k_{alpha-3,profile}^2/mu_{alpha-3}
          + M_A^{(3)}+M_B^{(3)}+log^2 n)
       = o(n/log^6 n).
```

Thus parameterized amplification applies.

## Source-transcription rule

For every active profile, HP/Heckel C5 source use is accepted if:

```text
1. the profile satisfies the same tail/relevance hypotheses;
2. lower-boundbeta is supplied by the corresponding prefix certificate;
3. first moment is supplied by the exact-d_u room certificate;
4. the largest occupied size s has mu_s >> n log^4 n;
5. correction terms M_A^{(r)}+M_B^{(r)} are certified harmless.
```

The source table S3/S4 should therefore not be read as globally blocked;
it is blocked only for trying to use the wrong profile beyond its
scrambled-scale regime.

## Remaining quantitative obligations

This split does not by itself close C5.  It reduces C5 to certificate
obligations:

```text
P3 exact-d_u room/prefix interval certificate for r=2,3,
tail/relevance checks for the rounded omitted-top profiles,
correction-term bounds from `c5-scrambled-correction-active-r23-2026-05-12.md`,
source quotation that HP/Heckel Lemmas 6.3--6.5 apply to arbitrary rounded
profiles satisfying those hypotheses, not only to the original optimizer.
```

## Status

This note removes the conceptual C5 endpoint blocker.  The remaining G5
work is now quantitative and bibliographic: source rows must be updated for
the active split, and the certificate generator must emit the corresponding
correction-term fields.
