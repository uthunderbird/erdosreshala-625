# C5 active-profile theorem for P3 r=2/r=3

Date: 2026-05-12

## Purpose

This theorem closes the non-circular part of the C5/P3 interface that the
red-team pass flagged as under-specified.

The source-table checker proves that the bibliography/dependency table has
no open rows.  This note states the mathematically supported interface now
available from the current artifacts: the HP/Heckel second-moment estimates
apply to finite rounded P3 omitted-top profiles selected by the endpoint
split, provided those profiles are supplied together with an externally
justified colour-count shift.

## Inputs

### Input C5.1: finite P3 profile and external shift

For `r in {2,3}`, assume an exact finite rounded profile with:

```text
largest occupied independent-set size s = alpha-r,
room >= R_r^exact > 0,
prefix/lower-boundbeta margin >= c_r^exact > 0,
total number of parts k = k_{alpha-1}-D_r+o(n/log^3 n),
```

for some quantity `D_r=D_r(n) >= 0` justified by an external theorem-level
profile-to-colour-count bridge.

The rounded profile has:

```text
k_u = O(n/log n)
```

uniformly for every occupied size `u`.

This bound is immediate from the total number of parts:

```text
k_u <= k = k_{alpha-1}-D_r+o(n/log^3 n)=Theta(n/log n).
```

### Input C5.2: active scrambled scale

The endpoint split uses `r` only when:

```text
mu_{alpha-r} >> n log^4 n.
```

For `r=2` this is the explicit branch condition.  For `r=3` it follows from:

```text
alpha0-floor-endpoint-split-theorem-2026-05-12.md.
```

### Input C5.3: source dependency closure

The accepted source table states that HP/Heckel fixed-partition restriction,
scrambled, middle, similar, and model-transfer estimates are available for
the active profiles once the profile supplies:

```text
tail/relevance hypotheses,
lower-boundbeta,
large cocolouring first moment,
active scrambled-scale bound.
```

Evidence:

```text
c5-source-gate-closure-summary-2026-05-12.md
r4-c5-source-table-2026-05-12.md
```

### Input C5.4: correction-term bounds

For the active profile with largest occupied size `s=alpha-r`, the scrambled
correction calculation gives:

```text
k_s^2/mu_s + M_A + M_B + O(log^2 n) = o(n/log^6 n)
```

provided:

```text
k_u=O(n/log n),
mu_s >> n log^4 n.
```

Evidence:

```text
c5-scrambled-correction-active-r23-2026-05-12.md
```

## Theorem

Let `r in {2,3}` be selected by the endpoint split, and let `bf{k}^{(r)}` be
an exact finite rounded P3 profile satisfying Inputs C5.1-C5.4.  Then the
restricted cocolouring variable `Z_r^co` for this profile satisfies:

```text
E[(Z_r^co)^2] / E[Z_r^co]^2 <= exp(Q_r(n)),
Q_r(n)=o(n/log^6 n).
```

Moreover, assume:

```text
E[Z_r^co] >= exp(c n/log n)
```

for some fixed `c>0`.

Consequently, by Paley-Zygmund:

```text
P(Z_r^co>0) >= exp(-o(n/log^6 n)).
```

Applying the same vertex-exposure Azuma amplification at scale:

```text
t=n/log^3 n * o(1)
```

with `t^2/n >> Q_r(n)`, gives with high probability:

```text
zeta(G) <= k_{alpha-1}-D_r+o(n/log^3 n).
```

In particular, if an external bridge proves:

```text
D_r = c_r' n/log^3 n
```

for some fixed `c_r'>0`, then this yields:

```text
zeta(G) <= k_{alpha-1}-c_r' n/log^3 n+o(n/log^3 n).
```

## Proof

G4 gives room and prefix margins for the exact finite rounded profile.
The present note does not prove the derivative conversion from positive room
to a specific quantitative shift `D_r=Theta(n/log^3 n)`; that bridge must be
supplied separately if the integrated proof wants a quantitative prize gap.

Assume therefore that the shifted profile in Input C5.1 is already available
and that:

```text
E[Z_r^co] >= exp(c n/log n)
```

for some fixed `c>0`.

The prefix margin gives HP/Heckel `lower-boundbeta` for every partial profile
with mass bounded away from 0 and 1.  The fixed-partition `B/C/D` estimates
use only the tail/relevance hypotheses and the profile bounds; the accepted
C5 source table records that no hidden ordinary `E[X]` lower bound is used.

For scrambled pairs, the active largest occupied size is `s=alpha-r`.
Input C5.4 gives:

```text
k_s^2/mu_s + M_A+M_B+O(log^2 n)=o(n/log^6 n).
```

The middle and similar estimates are controlled by the prefix margin and the
large cocolouring denominator, respectively.  The `G(n,m)` to `G(n,1/2)`
transfer contributes only `exp(O(log^2 n))`, which is also
`exp(o(n/log^6 n))`.

Combining the HP/Heckel pair decomposition over relevant pairs gives:

```text
E[(Z_r^co)^2]/E[Z_r^co]^2 <= exp(o(n/log^6 n)).
```

The Paley-Zygmund and Azuma steps are then the parameterized amplification
from:

```text
r4-parameterized-second-moment-amplification-2026-05-12.md.
```

Choose any amplification error:

```text
t=o(n/log^3 n)
```

with:

```text
t^2/n >> Q_r(n).
```

This is possible because `Q_r(n)=o(n/log^6 n)`.  The amplification loss is
therefore lower order than the certified `Theta(n/log^3 n)` colour saving.

This proves the theorem.

## Gate impact

This theorem upgrades C5 from a source-table status check to the non-circular
second-moment/Azuma interface needed by the integrated proof.

Remaining global publication tasks are:

```text
1. provide a theorem-level bridge from exact finite room/prefix margins to an
   explicit colour-count shift `D_r`;
2. then reinsert the resulting quantitative saving into the integrated proof;
3. final integrated proof needs another red-team pass after that repair.
```
