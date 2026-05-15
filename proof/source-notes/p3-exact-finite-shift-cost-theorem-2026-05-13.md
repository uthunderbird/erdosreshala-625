# P3 exact finite shift-cost theorem

Date: 2026-05-13

## Purpose

This note isolates the threshold derivative input needed by:

```text
p3-exact-finite-first-moment-shift-theorem-2026-05-13.md
```

It closes the specific gap left by the old R4/C2 route: the cost of lowering
the number of colour classes by:

```text
D = O(n/log^3 n)
```

near the `alpha-1` threshold.

## Source input

The analytic source input is Heckel 2024, Lemma `delk`
(`HRHowdoes`, Corollary 39 in the source notation):

```text
d/dk L_0(n,k,alpha-1)
  = (2/log 2) log^2 n + O(log n log log n),
```

uniformly for:

```text
k <= n/2,
k = n/(alpha-1-Theta(1)).
```

The same source gives the threshold bracketing:

```text
L_0(n,k_{alpha-1}-1,alpha-1) <= O(log^4 n),
L_0(n,k_{alpha-1},alpha-1) >= -O(log^4 n).
```

The theorem below uses only this derivative estimate and the fact that the
whole interval:

```text
[k_{alpha-1}-D, k_{alpha-1}]
```

stays inside the same uniformity window when `D=O(n/log^3 n)`.

## Theorem

Let:

```text
k_1 = k_{alpha-1}(n),
D = D(n) = O(n/log^3 n),
k = k_1 - D.
```

Then:

```text
L_0(n,k_1,alpha-1) - L_0(n,k,alpha-1)
  = ((2/log 2)+o(1)) D log^2 n.
```

Equivalently, for every fixed `c>0`, if:

```text
D = c n/log^3 n + O(1),
```

then:

```text
L_0(n,k,alpha-1)
  = L_0(n,k_1,alpha-1)
    - ((2c/log 2)+o(1)) n/log n.
```

## Proof

For every intermediate real `u` in:

```text
[k_1-D,k_1],
```

we have:

```text
u = k_1 + O(n/log^3 n).
```

Since `k_1 = n/(alpha-1-Theta(1))` and `alpha=Theta(log n)`, this remains in
the source uniformity regime:

```text
u = n/(alpha-1-Theta(1)).
```

By the derivative input:

```text
d/du L_0(n,u,alpha-1)
  = (2/log 2) log^2 n + O(log n log log n)
```

uniformly across the interval.  Integrating from `k_1-D` to `k_1` gives:

```text
L_0(n,k_1,alpha-1)-L_0(n,k_1-D,alpha-1)
  = (2/log 2)D log^2 n
    + O(D log n log log n).
```

Because `D=O(n/log^3 n)`,

```text
D log n log log n = O(n log log n/log^2 n) = o(n/log n).
```

Also:

```text
D log^2 n = O(n/log n),
```

so the error is `o(D log^2 n)` whenever `D` has order `n/log^3 n`, and it is
still an additive `o(n/log n)` error throughout the required window.

This proves the stated shift-cost estimate.

## Exact-finite P3 use

This theorem is a threshold derivative theorem for `L_0`.  In the P3 exact
finite chain it may be used after the following normalization check:

```text
the exact finite centered objective differs from the relevant first-moment
exponent by affine terms whose differences vanish for compared profiles with
the same total mass and mean deficit.
```

Under that normalization, lowering the part count by:

```text
D_r = c_r n/log^3 n + O(1)
```

costs:

```text
(2c_r/log 2 + o(1)) n/log n
```

in the exact-finite first-moment exponent.

## What this does and does not close

Closed here:

```text
the missing threshold derivative / shift-cost estimate in the
D=O(n/log^3 n) window.
```

Still not closed here:

```text
1. the exact finite normalization match between G4 room and L_0 exponent;
2. the P3 rounding-stability lemma for objective and prefix constraints.
```

Thus this note removes one P0 sub-gap from the low-branch bridge, but it does
not by itself complete the low-branch proof.
