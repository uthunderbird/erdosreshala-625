# P3 C3 source-gate instantiation

Date: 2026-05-13

## Purpose

This note instantiates the C3 first-moment preservation lemma for the rounded
P3 active profiles.

It closes the stale conditional statement in:

```text
p3-specific-c3-application-theorem-2026-05-13.md
```

that still treated the C5 source gate as open.

## Source-gate evidence

The C5 source gate is closed in:

```text
c5-source-gate-closure-summary-2026-05-12.md
```

with checker result:

```json
{
  "gate_closed": true,
  "open_count": 0,
  "blocked_count": 0,
  "active_profile_unresolved_ids": []
}
```

The accepted source table is:

```text
r4-c5-source-table-2026-05-12.md
```

and records row `S1` as:

```text
fixed-partition B/C/D bad-event bounds -> OK-C3.
```

## Instantiation

The rounded P3 profiles supplied by:

```text
p3-specific-rounding-theorem-2026-05-13.md
```

satisfy the structural hypotheses of:

```text
r4-c3-first-moment-preservation-full-lemma-2026-05-12.md
```

namely:

```text
1. no alpha-1 classes for r=2 and no alpha-1/alpha-2 classes for r=3;
2. all occupied sizes lie in the active window u=alpha-i with i>=r;
3. total number of parts is Theta(n/log n);
4. Gaussian tail gives the HP relevance/tail condition;
5. fixed-partition B/C/D estimates are available by the closed source gate.
```

The clique-side restrictions are supplied in the C3 lemma by complement
symmetry of `G(n,1/2)`.

## Theorem

For the rounded active P3 profile `bf{k}^{(r)}`, `r in {2,3}`,

```text
E[Z_{bf{k}^{(r)}}^co]
  = (1-o(1)) E[X_{bf{k}^{(r)}}^co].
```

Consequently, if:

```text
E[X_{bf{k}^{(r)}}^co] >= exp(c n/log n),
```

then for some fixed `c'>0`:

```text
E[Z_{bf{k}^{(r)}}^co] >= exp(c' n/log n).
```

## Status

This closes the fixed-partition source-gate dependency for the P3 C3
application.  The closure is source/dependency closure, not an independent
replacement for the HP/Heckel fixed-partition estimates.
