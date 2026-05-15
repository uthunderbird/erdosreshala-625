# R4 low-regime cochromatic proof draft

Date: 2026-05-12

## Target

For the low regime

```text
mu_alpha(n) <= n^{x0+o(1)},
```

prove that there is a constant `c>0` such that, whp,

```text
zeta(G(n,1/2))
  <= k_{alpha-1}(n) - c n/log^3 n + o(n/log^3 n).
```

This is the remaining hard input for the R4 prize route.

## Certificate assumptions

Assume the following constrained-profile certificate has been proved for
`x in [0,x0]`.

### C1: constrained profile

There is an alpha-minus-one profile `bf{k}^{low}` with

```text
|bf{k}^{low}| <= k_{alpha-1}(n) - c0 n/log^3 n
```

for some `c0>0`, whose limiting deficit distribution `p(x)` satisfies the
tail condition and the top-layer cap.

### C2: cocolouring first moment

For some `c1>0`,

```text
E[X_{bf{k}^{low}}^co] >= exp(c1 n/log n).
```

### C3: restricted first moment preservation

For Heckel's restricted cocolouring count `Z_{bf{k}^{low}}^co`,

```text
E[Z_{bf{k}^{low}}^co] ~ E[X_{bf{k}^{low}}^co].
```

This is supplied by
`r4-c3-first-moment-preservation-full-lemma-2026-05-12.md`, conditional only
on the HP/Heckel fixed-partition `B,C,D` restriction estimates for the
rounded constrained profile.

### C4: lower-boundbeta / prefix positivity

For every fixed `delta>0`, every macroscopic partial profile has
positive exponent. Equivalently, the prefix-positivity certificate proves
the lower-boundbeta condition needed in the middle-overlap range.

### C5: co-tame second moment

The restricted cocolouring count satisfies

```text
E[(Z_{bf{k}^{low}}^co)^2] / E[Z_{bf{k}^{low}}^co]^2
  <= exp(O(log^2 n)).
```

## Proof

By C3 and C2,

```text
E[Z_{bf{k}^{low}}^co] >= exp((c1/2)n/log n)
```

for large `n`.

By C5 and Paley-Zygmund,

```text
Pr[Z_{bf{k}^{low}}^co > 0]
  >= E[Z]^2/E[Z^2]
  >= exp(-O(log^2 n)).
```

If `Z_{bf{k}^{low}}^co>0`, then `G` has a cocolouring with
`|bf{k}^{low}|` parts, so

```text
Pr[zeta(G) <= |bf{k}^{low}|] >= exp(-O(log^2 n)).
```

Now use the vertex-exposure martingale for `zeta`. Changing all edges
incident to one vertex changes `zeta` by at most one: isolate that vertex
as a singleton cocolour class if needed. Hence Azuma-Hoeffding gives

```text
Pr[zeta <= E[zeta]-t] <= exp(-t^2/(2n)),
Pr[zeta >= E[zeta]+t] <= exp(-t^2/(2n)).
```

Choose

```text
t = n/log^4 n.
```

Then

```text
t^2/n = n/log^8 n >> log^2 n.
```

If

```text
E[zeta] > |bf{k}^{low}| + t,
```

then

```text
Pr[zeta <= |bf{k}^{low}|]
  <= Pr[zeta <= E[zeta]-t]
  <= exp(-n/(2log^8 n)),
```

contradicting the Paley-Zygmund lower bound for large `n`. Therefore

```text
E[zeta] <= |bf{k}^{low}| + t.
```

Apply Azuma again:

```text
Pr[zeta > |bf{k}^{low}| + 2t]
  <= exp(-n/(2log^8 n)) = o(1).
```

Thus whp

```text
zeta(G) <= |bf{k}^{low}| + 2n/log^4 n.
```

Using C1,

```text
zeta(G)
  <= k_{alpha-1}(n)
     - c0 n/log^3 n
     + 2n/log^4 n.
```

For large `n`, `2n/log^4 n <= (c0/2)n/log^3 n`, so whp

```text
zeta(G)
  <= k_{alpha-1}(n) - (c0/2)n/log^3 n.
```

This proves the target with `c=c0/2`.

## What remains to make this proof unconditional

The proof above is complete conditional on C1--C5. The missing work is to
turn the constrained optimizer and co-tame second moment into rigorous
lemmas:

1. interval certificate for C1/C2/C4;
2. exact finite-`n` objective normalization for C2;
3. exact HP/Heckel definition transcription for the already isolated C3
   lemma;
4. co-tame second moment C5.

## Role in the full R4 proof

Combined with

```text
chi(G) >= k_{alpha-1}(n)-o(n/log^3 n)
```

from `r4-ordinary-lower-bound-complete-draft-2026-05-12.md`, this gives

```text
chi(G)-zeta(G) >= (c-o(1))n/log^3 n -> infinity
```

in the low regime.
