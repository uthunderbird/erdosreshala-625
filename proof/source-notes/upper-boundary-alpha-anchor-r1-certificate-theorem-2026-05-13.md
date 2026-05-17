# Upper-boundary alpha-anchor r=1 certificate theorem

Date: 2026-05-13

## Purpose

This note states the proof-roadmap target for the positive exploratory route:

```text
alpha-anchor, r=1 omitted-top profile.
```

It is the current candidate route intended to close the remaining
upper-boundary good branch:

```text
x -> 1.
```

## Roadmap status

This is an **open candidate route memo**, not a completed proof. The theorem
statement below records the intended closure target, and the `U`-items record
the named theorem nodes currently believed sufficient to complete this route.
Every `U`-item remains open unless explicitly discharged elsewhere. The note is
meant to prevent hidden assumptions and overclaiming, not to assert that the
route is already closed.

Unless explicitly stated otherwise, every probabilistic statement below is a
statement about the same ambient random graph `G ~ G(n,1/2)`. Any conditioning
introduced inside a proof must be discharged before the theorem output is used
elsewhere in the route.

## Setup

Let:

```text
alpha_0 = 2 log_2 n - 2 log_2 log_2 n + 2 log_2(e/2) + 1,
alpha = floor(alpha_0),
x = alpha_0-alpha.
```

Assume the upper-boundary terminal interval:

```text
x in [x_1,1)
```

for some fixed `x_1<1` chosen so that **all** quantitative inequalities below
hold simultaneously on `[x_1,1)`, with exploratory evidence at `x_1=0.95`.

Let:

```text
K = boldk_alpha(n).
```

Use deficit coordinates:

```text
i = alpha-u.
```

The `r=1` alpha-anchor profile satisfies:

```text
p_0=0,
support i>=1,
largest occupied size alpha-1.
```

## Notation and event summary

Constants:

```text
c_D > 0: profile-size deficit scale, with D = c_D n/log^3 n;
c_room > 0: residual finite room margin after transfer and rounding;
c_prefix > 0: residual finite prefix margin after transfer and rounding;
c_FM > 0: residual first-moment exponent constant, giving exp(c_FM n/log n);
c_chi > 0: ordinary-chi loss constant at scale n/log^3 n;
delta_2(n) = o(n/log^6 n): second-moment correction exponent.
```

Events:

```text
E_zeta: upper-bound profile exists and yields the zeta upper bound;
E_alpha: alpha-anchor chromatic lower bound event;
E_tr: transfer event from chi_alpha to ordinary chi;
E_* = E_zeta ∩ E_alpha ∩ E_tr: final common good event.
```

## Target theorem

There exist constants:

```text
x_1<1,
c_D>0,
c_room>0,
c_prefix>0,
c_FM>0,
c_chi>0
```

such that for all sufficiently large `n` with `x in [x_1,1)`, there is a
rounded alpha-anchor `r=1` profile `bf{k}^{up}` satisfying:

```text
|bf{k}^{up}| <= boldk_alpha(n) - c_D n/log^3 n,
largest occupied size <= alpha-1,
tail/relevance hypotheses,
finite room margin >= c_room,
finite prefix margin >= c_prefix,
E[Z_{bf{k}^{up}}^co] >= exp(c_FM n/log n),
E[(Z_{bf{k}^{up}}^co)^2]/E[Z_{bf{k}^{up}}^co]^2 <= exp(delta_2(n)).
```

Moreover, with probability `1-o(1)`:

```text
Z_{bf{k}^{up}}^co > 0,
```

hence on that event,

```text
zeta(G) <= boldk_alpha(n)-c_D n/log^3 n+o(n/log^3 n).
```

Together with an ordinary alpha-anchor lower bound of the form:

```text
chi(G) >= boldk_alpha(n)-c_chi n/log^3 n-o(n/log^3 n)
```

with:

```text
0 < c_chi < c_D,
```

this gives, on the intersection of the two good events,

```text
chi(G)-zeta(G) >= (c_D-c_chi)n/log^3 n-o(n/log^3 n),
```

and therefore, with probability `1-o(1)`,

```text
chi(G)-zeta(G) -> infinity
```

on the upper-boundary region.

## Route-specific sufficient input package

The following inputs are the current explicit package intended to make the
alpha-anchor `r=1` route proof-complete as a roadmap. Some may later be
weakened or folded into more economical lemmas; for now the purpose is
sufficiency, provenance, auditability, and event-level composability.

The lower-bound side is split into `U8a/U8b` because it has two distinct tasks:
first prove the alpha-anchor lower bound itself, then prove the transfer from
`chi_alpha` to ordinary `chi` with a separately controlled cleanup loss.

### U1: alpha-anchor limiting certificate

Prove, with directed interval arithmetic, that the limiting `r=1`
alpha-anchor profile has positive room and prefix margins on:

```text
x in [x_1,1).
```

Exploratory evidence:

```text
upper-boundary-alpha-anchor-omitted-top-scan-result-2026-05-13.md
```

Proof-grade certificate target:

```text
upper-boundary-alpha-anchor-r1-interval-certificate-target-2026-05-13.md
```

The scan found:

```text
room >= about 0.21998,
prefix >= about 0.00324
```

on `[0.95,0.999999]`.

For quantitative closure, this item should export explicit limiting lower
bounds:

```text
room_limit(x) >= r_* > 0,
prefix_limit(x) >= p_* > 0
```

uniformly on `[x_1,1)`, with special attention to the narrow prefix budget.

### U2: exact finite large-anchor transfer checklist theorem

Prove a shifted-anchor finite-transfer theorem for the alpha-anchor `r=1`
profile, reusing the existing large-anchor transfer pipeline but recording the
provenance of each output explicitly.

Named prior sources intended for reuse:

```text
exact-du-large-anchor-expansion-2026-05-12.md
exact-du-large-anchor-compactness-lemmas-2026-05-12.md
g4-finite-transfer-publication-closure-2026-05-12.md
p3-exact-finite-normalization-bridge-theorem-2026-05-13.md
```

The anchor is shifted from `alpha-1` to `alpha`, and the deficit support
starts at `i=1`, so every reused component must be rechecked against the new
boundary convention.

The theorem should explicitly deliver, for the finite exact profile:

```text
1. the exact normalization/identity package after shifting the anchor;
2. the finite room inequality with residual margin >= c_room^pre;
3. the finite prefix inequality with residual margin >= c_prefix^pre;
4. every boundary term created by the missing i=0 mass and by the new
   lower support endpoint i=1;
5. the lower-boundbeta or equivalent source-gate input later required by C3;
6. quantitative error bounds showing these transferred inequalities remain
   stronger than the target rounding budget on x in [x_1,1).
```

The intended residual budget is:

```text
c_room^pre >= c_room + Delta_room^round,
c_prefix^pre >= c_prefix + Delta_prefix^round,
```

where `Delta_room^round, Delta_prefix^round > 0` are the rounding losses from
`U4`. In particular, the prefix side must satisfy:

```text
p_* - Delta_prefix^transfer - Delta_prefix^round >= c_prefix > 0.
```

Provenance map for the six outputs:

```text
1. normalization/identity package:
   p3-exact-finite-normalization-bridge-theorem-2026-05-13.md
   plus a new shifted-anchor boundary lemma for the i=1 convention;
2. finite room inequality:
   exact-du-large-anchor-expansion-2026-05-12.md
   + exact-du-large-anchor-compactness-lemmas-2026-05-12.md
   + a new shifted-anchor transfer corollary;
3. finite prefix inequality:
   exact-du-large-anchor-expansion-2026-05-12.md
   + exact-du-large-anchor-compactness-lemmas-2026-05-12.md
   + a new shifted-anchor transfer corollary;
4. boundary terms from missing i=0 mass and lower support endpoint i=1:
   new shifted-anchor boundary lemma;
5. lower-boundbeta/source-gate input:
   g4-finite-transfer-publication-closure-2026-05-12.md
   after translation through the shifted-anchor normalization package;
6. uniform positive error budget on x in [x_1,1):
   new shifted-anchor finite-transfer closure theorem combining 1-5.
```

This item is the place where the shifted anchor and omitted-top convention must
be audited most carefully.

### U3: alpha-anchor first-moment shift theorem

Closure note:

```text
upper-boundary-alpha-first-moment-shift-u3-closure-2026-05-13.md
```

Prove the analogue of the shift-cost theorem:

```text
L_0(n,K,alpha)-L_0(n,K-D,alpha)
  = ((2/log 2)+o(1))D log^2 n
```

for:

```text
D=O(n/log^3 n).
```

Named source dependency:

```text
HR derivative estimate theorem for threshold-window first-moment profiles
```

If the currently available HR source is only written for a fixed anchor or for
an anchor family not yet including `a=alpha`, then `U3` is the new theorem
that extends that HR derivative estimate uniformly to `a=alpha` on the terminal
interval.

With:

```text
D = c_D n/log^3 n,
```

the exported gain should be recorded as:

```text
Gain_FM(n) = ((2/log 2)+o(1)) c_D n/log n.
```

For this route, a one-sided lower bound strong enough to force a positive final
exponent after all downstream losses would suffice; the full asymptotic identity
is the current convenient package.

### U4: rounding stability and tail/relevance transfer theorem

Adapt:

```text
p3-specific-rounding-theorem-2026-05-13.md
p3-rounding-stability-room-prefix-lemma-2026-05-13.md
```

to the alpha-anchor `r=1` profile.

The support is still consecutive and starts at `i=1`, so the theorem should
be written as the alpha-anchor `r=1` analogue of the low-branch rounding
package.

This theorem must explicitly show that rounding preserves or supplies all finite
hypotheses needed later, namely:

```text
1. room loss at most Delta_room^round, leaving residual room >= c_room;
2. prefix loss at most Delta_prefix^round, leaving residual prefix >= c_prefix;
3. the required tail/relevance hypotheses for the rounded active profile;
4. compatibility with the lower-boundbeta/source-gate input transferred in U2.
```

No hidden automaticity is allowed here: if tail/relevance follows from an
existing generic consecutive-support theorem, that theorem must be cited inside
`U4`; otherwise the tail/relevance transfer is part of the new `U4` theorem
itself.

### U5: alpha-anchor profitable-profile bridge theorem

Combine `U1`-`U4` with the first-moment shift input to prove the explicit
bridge theorem:

```text
there exists D = c_D n/log^3 n
```

for some fixed `c_D>0` and a rounded alpha-anchor `r=1` profile at `K-D` such
that:

```text
1. |bf{k}^{up}| <= K-D;
2. finite room and prefix margins remain >= c_room and >= c_prefix;
3. the tail/relevance and source-gate hypotheses needed by C3 hold;
4. the total first-moment exponent remains >= c_FM n/log n.
```

This theorem must include the explicit quantitative ledger:

```text
Gain_FM(n)
- Loss_FM^transfer(n)
- Loss_FM^round(n)
- Loss_FM^row(n)
>= c_FM n/log n,
```

with each loss term individually bounded and uniform on `[x_1,1)`.

This is the missing bridge between the derivative gain in `U3` and the actual
profile claimed in the target theorem.

Focused target for this theorem node:

```text
upper-boundary-alpha-anchor-profitable-profile-bridge-2026-05-13.md
```

### U6: C3 first-moment preservation via an explicit active-profile row theorem

Instantiate the exact active first-moment source theorem `C3` by writing the
new alpha-anchor `r=1` row explicitly and checking each field against its
source.

Named source dependency:

```text
C3 active-profile first-moment preservation theorem
```

Named schema dependency:

```text
fixed-partition source-gate table / active-profile row schema used by C3
```

The new row should include at least:

```text
1. largest occupied size alpha-1;
2. consecutive deficit support starting at i=1;
3. total part count Theta(n/log n);
4. tail/relevance hypotheses;
5. finite room margin;
6. finite prefix margin;
7. lower-boundbeta or the exact source-gate surrogate used by C3;
8. active scrambled scale mu_{alpha-1};
9. any overlap or monotonicity side conditions required by the existing C3 row.
```

Field-by-field provenance for the row:

```text
1-2. setup plus U4;
3. size accounting inside the new U5 bridge theorem;
4-7. U2 + U4;
8. upper-boundary scale calculation recorded in this note and used again in U7;
9. exact C3 source theorem plus the active-row schema being extended.
```

The theorem should then export:

```text
E[Z_{bf{k}^{up}}^co] >= exp(c_FM n/log n).
```

### U7: active C5 second moment and existence event theorem

Adapt the exact active second-moment source theorem `C5` to the same
alpha-anchor `r=1` active-profile row used in `U6`.

Named source dependency:

```text
C5 active-profile second-moment / Azuma amplification theorem
```

Named inference dependency:

```text
second-moment existence inference (packaged inside C5, or otherwise invoked
explicitly via Paley-Zygmund / second-moment method)
```

Named schema dependency:

```text
the same fixed-partition active-profile row schema installed in U6
```

The active scrambled scale is:

```text
mu_{alpha-1}.
```

In the upper-boundary regime:

```text
mu_alpha=n^{1-o(1)},
mu_{alpha-1}=mu_alpha*Theta(n/log n)=n^{2-o(1)}/log n.
```

Therefore:

```text
k^2/mu_{alpha-1}=n^{o(1)}/log n=o(n/log^6 n).
```

This favorable scale helps only after the structural hypotheses of the exact
`C5` theorem are checked on the installed row. The theorem should conclude:

```text
E[(Z_{bf{k}^{up}}^co)^2]/E[Z_{bf{k}^{up}}^co]^2 <= exp(delta_2(n)),
delta_2(n)=o(n/log^6 n),
P(Z_{bf{k}^{up}}^co > 0) = 1-o(1).
```

On the event `Z_{bf{k}^{up}}^co > 0`, there exists the required co-profile, so

```text
zeta(G) <= boldk_alpha(n)-c_D n/log^3 n+o(n/log^3 n).
```

For the intended existence conclusion, this item should also record the scale
comparison explicitly:

```text
delta_2(n) = o(n/log^6 n) = o(n/log n),
```

so the second-moment correction is negligible compared with the first-moment
exponent `c_FM n/log n` exported by `U5/U6`.

### U8a: alpha-anchor lower-bound theorem near boldk_alpha

Probabilistic mode: this item should be a **whp lower-bound theorem** on the
same ambient random graph `G`.

Prove, with probability `1-o(1)`,

```text
chi_alpha(G) >= boldk_alpha(n)-O(1)
```

or at least:

```text
chi_alpha(G) >= boldk_alpha(n)-c_alpha n/log^3 n-o(n/log^3 n)
```

for some `c_alpha >= 0`.

Focused target:

```text
upper-boundary-alpha-anchor-ordinary-lower-bound-target-2026-05-13.md
```

Current source decomposition:

```text
upper-boundary-alpha-lower-bound-u8a-closure-2026-05-13.md
upper-boundary-alpha-to-ordinary-transfer-u8b-closure-2026-05-13.md
upper-boundary-alpha-one-more-colour-source-check-2026-05-13.md
upper-boundary-alpha-average-colour-class-theorem-2026-05-13.md
upper-boundary-alpha-first-moment-slope-theorem-2026-05-13.md
```

The alpha-anchor first-moment input is now source-backed via HR Lemma `k*`:

```text
n / boldk_alpha = alpha_0 - 1 - 2/ln 2 + o(1).
```

Together with the `X_{alpha+1}` Markov transfer, `U8a/U8b` export:

```text
chi(G) >= boldk_alpha-o(n/log^3 n)
```

whp on the upper-boundary interval.

### U8b: transfer theorem from chi_alpha to ordinary chi

Prove a separate **whp transfer theorem** converting the alpha-anchor lower
bound to an ordinary chromatic lower bound by deleting or hitting all
independent sets of size `alpha+1`.

Named quantitative input:

```text
mu_{alpha+1}=mu_alpha*Theta(log n/n)=n^{-o(1)}log n.
```

A crude first-moment estimate suggests a loss budget of size:

```text
O(mu_{alpha+1} polylog n)=o(n/log^3 n).
```

For proof-complete closure, this theorem must define the cleanup-cost random
variable `C_{alpha+1}(G)` and prove an event-level tail statement, for example
via Markov or a stronger concentration bound, of the form:

```text
P(C_{alpha+1}(G) <= c_tr n/log^3 n) = 1-o(1)
```

for some transfer constant `c_tr >= 0`.

It should then conclude, on that event together with the `U8a` event,

```text
chi(G) >= boldk_alpha(n)-c_chi n/log^3 n-o(n/log^3 n)
```

with:

```text
c_chi = c_alpha + c_tr,
c_chi < c_D.
```

If the cleanup uses several bad-object families or several stages, the theorem
must include the internal union/Markov bookkeeping needed to keep the full
transfer event at probability `1-o(1)`.

This theorem must also verify that the correction loss is uniform on the full
terminal interval `x in [x_1,1)`.

Focused target:

```text
upper-boundary-alpha-anchor-ordinary-lower-bound-target-2026-05-13.md
```

## Event ledger and final composition

Define the good events:

```text
E_zeta := { Z_{bf{k}^{up}}^co > 0 and hence
            zeta(G) <= boldk_alpha(n)-c_D n/log^3 n+o(n/log^3 n) },

E_alpha := { chi_alpha(G) >= boldk_alpha(n)-c_alpha n/log^3 n-o(n/log^3 n) },

E_tr := { C_{alpha+1}(G) <= c_tr n/log^3 n and hence
          chi(G) >= boldk_alpha(n)-c_chi n/log^3 n-o(n/log^3 n) }.
```

The route must export:

```text
P(E_zeta)=1-o(1),
P(E_alpha)=1-o(1),
P(E_tr)=1-o(1).
```

Then, on the common event

```text
E_* := E_zeta ∩ E_alpha ∩ E_tr,
```

we have:

```text
chi(G)-zeta(G)
>= (c_D-c_chi)n/log^3 n-o(n/log^3 n)
-> infinity.
```

Since all theorem nodes are interpreted on the same ambient random graph,

```text
P(E_*) >= 1 - P(E_zeta^c) - P(E_alpha^c) - P(E_tr^c) = 1-o(1).
```

Thus the final gap conclusion holds with high probability.

## Dependency map for the route

The proof route is intended to close in the following order:

```text
U1 + U2 + U4
  -> finite rounded certificate with residual room >= c_room,
     residual prefix >= c_prefix, and tail-relevance/source-gate data;
U3 + U5
  -> choose D = c_D n/log^3 n while keeping net first-moment exponent
     >= c_FM n/log n;
U6
  -> the exact C3 theorem applied to the installed alpha-anchor r=1 row gives
     E[Z_{bf{k}^{up}}^co] >= exp(c_FM n/log n);
U7
  -> the exact C5 theorem applied to the same row gives a second-moment
     correction exp(delta_2(n)) and the whp event E_zeta;
U8a
  -> whp event E_alpha for the alpha-anchor lower bound;
U8b
  -> whp transfer event E_tr, with c_chi = c_alpha + c_tr < c_D;
U7 + U8a + U8b
  -> common good event E_* with probability 1-o(1);
E_*
  -> chi(G)-zeta(G) -> infinity on x in [x_1,1).
```

This dependency map is intended as a theorem-provenance ledger, not merely a
roadmap: each node above is either a named source theorem application or a
new theorem obligation with a stable name, together with the quantitative and
event-level budget it must export.

## Dependency status

The blocker list below is the prioritized subset of this fuller status view.

```text
U1: open, but exploratory scan positive; must export uniform limiting room and
    prefix buffers r_*, p_* on [x_1,1).
U2: open shifted-anchor finite-transfer checklist theorem; prior source notes
    are named, but the shifted-anchor boundary lemmas and closure theorem are
    new, and must export pre-rounding residual budgets c_room^pre, c_prefix^pre.
U3: open alpha-anchor first-moment shift theorem; depends on a named HR
    derivative estimate source and may require a new uniform-a=alpha extension;
    exports Gain_FM(n) = ((2/log 2)+o(1)) c_D n/log n.
U4: open alpha-anchor rounding and tail/relevance transfer theorem; must bound
    Delta_room^round and Delta_prefix^round explicitly.
U5: open alpha-anchor profitable-profile bridge theorem with focused target
    upper-boundary-alpha-anchor-profitable-profile-bridge-2026-05-13.md; must
    prove the net first-moment inequality with constant c_FM.
U6: open explicit-row C3 installation theorem for the alpha-anchor r=1 active
    profile; exports exp(c_FM n/log n).
U7: open explicit-row C5 installation theorem for the same active profile;
    exports exp(delta_2(n)) with delta_2(n)=o(n/log^6 n) and the event
    P(E_zeta)=1-o(1).
U8a: open whp alpha-anchor lower-bound theorem near boldk_alpha; exports E_alpha.
U8b: open whp transfer theorem from chi_alpha to ordinary chi; exports E_tr and
    a final ordinary-chi constant c_chi strictly smaller than c_D.
```

## Current blocker list

The largest new risks are:

```text
1. narrow-prefix budget: the exploratory limiting prefix margin is only about
   0.00324, so U2/U4 must preserve an explicit positive residual c_prefix;
2. U5 first-moment ledger: the route still depends on a quantified net gain
   Gain_FM - Loss_FM^transfer - Loss_FM^round - Loss_FM^row >= c_FM n/log n;
3. U8a/U8b event logic: the lower-bound route still requires a whp alpha-anchor
   lower bound plus a whp cleanup-cost transfer with c_chi < c_D;
4. U6/U7 event logic: exact C3/C5 theorem installation on the new
   active-profile row, together with the explicit event P(E_zeta)=1-o(1);
5. final composition: the common-event step E_* must remain on the same ambient
   random graph and preserve probability 1-o(1);
6. U3: availability of the HR derivative estimate in the required uniform
   alpha-anchor regime.
```

The scan suggests the raw limiting room obstruction is not the blocker; the
more fragile issues are prefix preservation, net first-moment budgeting,
ordinary-chi transfer loss, event composition, and active-row installation.

## Status

Open candidate theorem roadmap. This remains the main candidate route for
closing the upper-boundary good branch, but the route is not yet proved and all
`U`-items remain open.

## Residual open issues

```text
1. the event-level theorems E_zeta, E_alpha, and E_tr remain open;
2. the constants and loss terms are still placeholders until the named theorem
   nodes are proved with compatible values;
3. some source dependencies may still need exact canonical proposition/file
   identifiers once the source notes stabilize.
```

## Repair ledger

```text
target document:
- proof/source-notes/upper-boundary-alpha-anchor-r1-certificate-theorem-2026-05-13.md

items fixed in order:
1. added a prominent Roadmap status section near the top stating explicitly that
   this is an open candidate route memo, not a completed proof;
2. added a compact notation-and-event summary near the top for constants and
   named good events;
3. explained the U8a/U8b split once in the route-package introduction;
4. clarified that the blocker list is a prioritized subset of the fuller
   dependency-status picture;
5. compressed the prior multi-round repair history into a single compact repair
   ledger so the note reads as a roadmap first rather than a changelog;
6. softened the strongest completion-sounding phrases into explicitly
   conditional roadmap language while preserving the honest residual-open-issues
   language.

items retired with justification:
- none.

residual issues still open:
- the route is still open: every U-item remains to be proved;
- the constants and event-level outputs are placeholders until the named
  theorem nodes are established with compatible values;
- some source dependencies still await exact canonical identifiers.
```
