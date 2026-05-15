# P3 exact finite normalization bridge theorem

Date: 2026-05-13

## Purpose

This note closes the normalization bridge between:

```text
1. the G4 exact finite room quantity computed with the centered objective
   J_A(p), and
2. the HP/HR first-moment exponent L_0 used in the P3 first-moment shift
   theorem.
```

It upgrades the normalization audit from:

```text
r4-objective-normalization-audit-2026-05-12.md
```

to the exact finite `d_u` framework used by:

```text
g4-finite-objective-closure-theorem-2026-05-12.md.
```

## Source definitions

HP/HR write the profile-dependent part of the first-moment exponent as:

```text
-sum_u p_u log(p_u d_u),
d_u = 2^{binom(u,2)} u!,
```

after removing the terms depending only on `n` and `k`.

Put:

```text
u = A-i.
```

For the standard low-branch anchor, `A=alpha-1`, and the P3 profiles are
expressed in the deficit coordinate `i`.

G4 uses the exact centered finite-anchor objective:

```text
J_A(p) = -sum_i p_i log p_i + sum_i p_i H_A(i),
```

where:

```text
H_A(i)=-(log 2/2)i(i-1)+sum_{j=1}^{i-1}log(1-j/A).
```

## Algebraic identity

There exist functions `C_A` and `B_A`, depending on `A` but not on the
profile `p`, such that for every admissible deficit profile:

```text
-sum_i p_i log(p_i d_{A-i})
  = J_A(p) + C_A + B_A sum_i i p_i.
```

Thus for any two profiles `p,q` satisfying:

```text
sum_i p_i = sum_i q_i = 1,
sum_i i p_i = sum_i i q_i,
```

we have the exact difference identity:

```text
[-sum_i p_i log(p_i d_{A-i})]
-
[-sum_i q_i log(q_i d_{A-i})]
  = J_A(p)-J_A(q).
```

## Verification of the identity

Expand:

```text
log d_{A-i}
  = (log 2) binom(A-i,2) + log((A-i)!).
```

The quadratic part satisfies:

```text
-(log 2) binom(A-i,2)
  = const_A + linear_A(i) - (log 2/2)i(i-1).
```

The factorial part satisfies:

```text
-log((A-i)!)
  = -log(A!) + sum_{j=0}^{i-1} log(A-j)
  = const_A + i log A + sum_{j=1}^{i-1} log(1-j/A).
```

The `j=0` term is zero after writing `log(A-0)=log A`, and the remaining
finite product is exactly the logarithmic correction in `H_A(i)`.

Combining the quadratic and factorial expansions gives:

```text
-log d_{A-i} = H_A(i) + C_A + B_A i.
```

Multiplying by `p_i`, summing over `i`, and adding the entropy term
`-sum_i p_i log p_i` proves the displayed identity.

## Consequence for G4 room

The G4 room comparison is made between profiles at the same low-branch
parameter `x`; by construction those profiles have:

```text
same total mass,
same mean deficit.
```

Therefore the affine terms in the HP/HR first-moment profile exponent cancel
exactly in the constrained-minus-unconstrained comparison.

Consequently, the exact finite G4 room margin:

```text
Room_A^{(r)}(x) >= R_r
```

is measured in the same profile-difference normalization as the HP/HR
`L_0` first-moment exponent.  No additional sign, base, or scale factor is
introduced.

## Theorem-level bridge

For every sufficiently large anchor `A`, every:

```text
x in [0,0.029155],
r in {2,3},
```

and every G4 constrained profile `p_A^{(r)}(x)` compared with the
corresponding unconstrained exact finite optimizer `p_A^{un}(x)`, the
profile exponent loss in `L_0` equals:

```text
J_A(p_A^{un}(x)) - J_A(p_A^{(r)}(x)).
```

In particular, the G4 lower bound:

```text
Room_A^{(r)}(x) >= R_r
```

may be inserted directly into the P3 first-moment shift theorem as the
available first-moment room.

## Status

This closes the exact-finite normalization bridge used by:

```text
p3-exact-finite-first-moment-shift-theorem-2026-05-13.md.
```

It does not address rounding stability.  The rounded integer profile must
still be shown to preserve room and prefix constraints up to `o(1)` at the
objective level, equivalently `o(n/log n)` in the first-moment exponent.
