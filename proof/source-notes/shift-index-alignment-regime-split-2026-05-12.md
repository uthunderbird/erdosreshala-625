# SHIFT index alignment and endpoint regime split

Date: 2026-05-12

## Purpose

This note fixes the indexing for the recursive endpoint route.  It
distinguishes:

```text
a       active bounded anchor / maximum allowed class size,
r       deficit truncation start in the old one-index convention,
mu_s    expected number of independent sets of size s.
```

The goal is to remove ambiguity from `SHIFT-GATE`.

## Deficit convention

At active anchor `a`, the top class size is `a`.  In the one-indexed
profile convention:

```text
i=1 corresponds to class size a,
i=2 corresponds to class size a-1,
i=3 corresponds to class size a-2.
```

Thus a truncation starting at `r` has largest occupied class size:

```text
a-r+1.
```

The HP/Heckel scrambled scale for that profile is controlled by:

```text
mu_{a-r+1}.
```

The active certificate evidence currently supports only:

```text
r=2 and r=3.
```

The scan rejects `r>=4`.

## Local endpoint alternatives at anchor a

Let

```text
N_scr = n log^4 n.
```

The endpoint route at anchor `a` uses the first applicable alternative:

### Alternative A: one-top omitted profile

If

```text
mu_{a-1} >> N_scr,
```

use the `r=2` exact-`d_u` shifted-anchor certificate.  The largest
occupied cocolouring class has size `a-1`, and the scrambled penalty is
manageable.

### Alternative B: two-top omitted profile

If Alternative A fails but

```text
mu_{a-2} >> N_scr,
```

use the `r=3` exact-`d_u` shifted-anchor certificate.  The largest occupied
cocolouring class has size `a-2`.

### Alternative C: scarcity shift

If

```text
mu_{a-2} <= N_scr,
```

then the explicit two-step ratio lemma gives

```text
mu_a=o(1),
```

provided `a,a-1,a-2` lie in the bounded threshold window.  Therefore whp
there are no independent or clique classes of size `a`, and:

```text
chi_a = chi_{a-1},
zeta_a = zeta_{a-1}.
```

The proof may shift from anchor `a` to anchor `a-1`.

## Initial anchor

The initial residual endpoint anchor is:

```text
a_0 = alpha-1.
```

The first split is therefore:

```text
if mu_{alpha-2} >> N_scr: use r=2 at a_0,
else if mu_{alpha-3} >> N_scr: use r=3 at a_0,
else mu_{alpha-1}=o(1), shift to a_1=alpha-2.
```

This fixes the earlier ambiguous wording: the shift is justified by
scarcity of size `a_0=alpha-1` classes, not by scarcity of size
`alpha-2` classes.

## Recursive step

At anchor

```text
a_j=alpha-1-j,
```

repeat:

```text
if mu_{a_j-1} >> N_scr: use r=2 at a_j,
else if mu_{a_j-2} >> N_scr: use r=3 at a_j,
else mu_{a_j}=o(1), shift to a_{j+1}=a_j-1.
```

Each shift is valid only after proving `mu_{a_j}=o(1)` and applying the
scarcity equality lemma.

## Finite termination obligation

For the standard choice

```text
alpha=floor(alpha_0),
alpha_0=2log_2 n-2log_2log_2 n+2log_2(e/2)+1,
```

the finite termination obligation is supplied by:

```text
alpha0-mu-floor-asymptotic-lemma-2026-05-12.md
```

It shows:

```text
mu_{alpha-3} >> n log^4 n.
```

Therefore at the initial anchor `a_0=alpha-1`, the split always stops by
Alternative A or B:

```text
if mu_{alpha-2} >> n log^4 n, use r=2;
else use r=3, since mu_{alpha-3} >> n log^4 n.
```

No recursive shift is required for the standard `alpha=floor(alpha_0)`
choice once that Stirling lemma is proved.

## Status

This note closes the index-alignment ambiguity but not the full SHIFT gate.
Remaining work:

```text
write the full Stirling proof for the alpha0-mu floor asymptotic,
quote HP lower bounds for every shifted anchor used,
attach exact-d_u certificates for r=2,3 over those shifted-anchor intervals.
```
