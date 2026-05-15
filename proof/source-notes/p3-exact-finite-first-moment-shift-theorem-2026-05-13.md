# P3 exact finite first-moment shift theorem

Date: 2026-05-13

## Purpose

This note replaces the attempted use of the old R4 C2 lemma in the
low-branch P3 bridge.  It records the exact-finite first-moment bridge in
the framework used by G4.

The round-5 red-team pass confirmed that the derivative / shift-cost sub-gap
is now closed by:

```text
p3-exact-finite-shift-cost-theorem-2026-05-13.md
```

The remaining rounding-stability input is now isolated in:

```text
p3-rounding-stability-room-prefix-lemma-2026-05-13.md
```

The exact-finite normalization bridge is now isolated in:

```text
p3-exact-finite-normalization-bridge-theorem-2026-05-13.md
```

## Setup

Let:

```text
r in {2,3},
x in [0,0.029155],
k_1 = k_{alpha-1}(n).
```

Let `p_A^{(r)}(x)` be the exact finite `r`-truncated P3 profile at the
standard anchor, with exact centered objective:

```text
J_A(p) = -sum_i p_i log p_i + sum_i p_i H_A(i).
```

Assume:

```text
Room_A^{(r)}(x) >= R_r > 0.
```

This is the exact finite room margin supplied by:

```text
g4-finite-objective-closure-theorem-2026-05-12.md.
```

Let:

```text
0<c_r<(ln2/4)R_r,
D_r=floor(c_r n/log^3 n),
k=k_1-D_r.
```

Let `bf{k}^{(r)}` be the rounded shifted profile supplied by:

```text
p3-specific-rounding-theorem-2026-05-13.md.
```

## Shift-cost theorem

The standalone shift-cost input is now isolated in:

```text
p3-exact-finite-shift-cost-theorem-2026-05-13.md
```

It proves, from the Heckel 2024 threshold derivative estimate for `L_0`, that
lowering the number of parts by:

```text
D_r = c_r n/log^3 n + O(1)
```

costs:

```text
((2c_r/ln2)+o(1)) n/log n
```

in the `L_0` exponent.  Its use in the exact-finite P3 chain still requires
the normalization bridge cited above.

## Conditional bridge theorem

For all sufficiently large `n`, uniformly for:

```text
x in [0,0.029155],
r in {2,3},
```

the rounded shifted P3 profile satisfies:

```text
log E[X_{bf{k}^{(r)}}^co] >= c n/log n
```

for some fixed `c>0`.

## Proof sketch

The exact finite centered objective is normalized so that affine terms in the
deficit index are removed.  Since compared profiles have the same total mass
and mean deficit, removing those affine terms does not change objective
differences relevant to the first-moment ratio.

This is the content of:

```text
p3-exact-finite-normalization-bridge-theorem-2026-05-13.md
```

At the ordinary `alpha-1` threshold profile, the cocolouring first moment has
the universal bonus:

```text
k_1 log 2 = ((ln2)^2/2+o(1)) n/log n.
```

Replacing the unrestricted profile by the `r`-truncated P3 profile costs:

```text
[(ln2)^2/2 - Room_A^{(r)}(x)] n/log n + o(n/log n)
```

in the normalized first-moment exponent.

By `p3-exact-finite-shift-cost-theorem-2026-05-13.md`, lowering the number of
parts by:

```text
D_r=c_r n/log^3 n+O(1)
```

costs:

```text
(2c_r/ln2+o(1)) n/log n,
```

in the exact-finite `D=O(n/log^3 n)` window.

Therefore the cocolouring exponent for the shifted profile is at least:

```text
[Room_A^{(r)}(x) - 2c_r/ln2 - o(1)] n/log n.
```

Since:

```text
0<c_r<(ln2/4)R_r
```

and `Room_A^{(r)}(x)>=R_r`, the bracket is at least `R_r/2` for all large
`n`.  Thus:

```text
log E[X_{bf{k}^{(r)}}^co] >= (R_r/3)n/log n
```

after increasing `n0`.

By `p3-rounding-stability-room-prefix-lemma-2026-05-13.md`, the rounding
perturbation from `p3-specific-rounding-theorem-2026-05-13.md` is
`o(n/log n)` in the first-moment exponent and is absorbed into the final
`o(1)` coefficient.

Taking the minimum over `r=2,3` gives a uniform positive constant.

## Residual open dependencies

The derivative / shift-cost theorem is now closed as a standalone input.
The exact-finite normalization bridge is closed as a standalone input.
The P3 rounding-stability lemma is closed as a standalone input.

There are no remaining theorem-level blockers inside this note.

## Status

The shift-cost derivative sub-gap is closed.
The exact-finite normalization bridge is closed.
The P3 rounding-stability dependency is closed.

This note may now be treated as a complete P3 exact-finite first-moment
shift theorem, subject only to the upstream G4 certificate and the stated
P3 rounding construction.
