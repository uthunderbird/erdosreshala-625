# P3 rounding stability for room and prefix

Date: 2026-05-13

## Purpose

This note closes the missing quantitative stability input for:

```text
p3-specific-rounding-theorem-2026-05-13.md.
```

It proves that the P3-specific integer rounding perturbation changes the
exact finite room and prefix functionals by `o(1)` on the profile scale, and
therefore by `o(n/log n)` on the first-moment exponent scale.

## Setup

Fix:

```text
r in {2,3},
x in [0,0.029155],
A = alpha-1,
k = k_{alpha-1}(n)-floor(c_r n/log^3 n).
```

Let `p=p_{A,x}^{(r)}` be the exact finite P3 profile from G4, and let
`hat p` be the empirical profile produced by the P3-specific rounding
construction.

The construction gives an active cutoff:

```text
I_n = C sqrt(log n),
```

and:

```text
sum_{i>I_n} p_i <= n^{-B},
sum_{i>I_n} i p_i <= n^{-B}
```

for any fixed `B` after increasing `C`, together with:

```text
||hat p-p||_1 <= polylog(n)/k,
sum_i i(hat p_i-p_i)=0,
hat p_i=0 for i<r.
```

Since:

```text
k = Theta(n/log n),
```

the total variation perturbation is:

```text
epsilon_n := ||hat p-p||_1 = O(polylog(n) log n/n)=o(log^{-M} n)
```

for every fixed `M`.

## Objective stability

On the active window `i<=I_n`, the exact finite potential satisfies:

```text
H_A(i)=O(i^2)=O(log n).
```

The entropy derivative on every coordinate with nonzero rounded mass is:

```text
|log p_i|+1 = O(polylog n),
```

because the Gaussian tail gives `p_i >= exp(-O(i^2))` on the active
window before the negligible tail cutoff.

Changing `O(polylog n)` counts changes the unnormalized profile objective
by:

```text
O(polylog n).
```

Equivalently, after dividing by `k`, the centered objective changes by:

```text
O(polylog n/k)=o(1).
```

Therefore:

```text
|J_A(hat p)-J_A(p)|=o(1).
```

By the normalization bridge:

```text
p3-exact-finite-normalization-bridge-theorem-2026-05-13.md
```

this is exactly an `o(n/log n)` perturbation in the corresponding
first-moment exponent.

## Room stability

The G4 room functional is a difference between the unconstrained exact
finite objective at the same mass/mean and the constrained P3 objective.
The rounding construction preserves total mass and mean deficit exactly,
up to the final `O(1)` divisibility correction; that correction changes the
exponent by only `O(polylog n)`, hence changes the profile-scale room by
`o(1)`.

Thus:

```text
Room_A^{(r)}(hat p;x)
  = Room_A^{(r)}(p;x)+o(1).
```

In particular, if G4 supplies:

```text
Room_A^{(r)}(p;x) >= R_r > 0,
```

then for all large `n`:

```text
Room_A^{(r)}(hat p;x) >= R_r/2.
```

## Prefix stability

The prefix functionals used by G4/C5 are finite clipped-prefix objective
differences over prefix-saturated subprofiles with masses bounded away from
`0` and `1` by the certificate parameter `delta`.

The analytic reduction in:

```text
r4-c4-prefix-positivity-reduction-full-lemma-2026-05-12.md
```

reduces the lower-boundbeta condition to prefix endpoints:

```text
r = delta,
r = 1-delta,
r = P_s(x)=sum_{i<=s}p_i(x)
```

for `s` in the finite active endpoint list.  On each prefix interval the
one-dimensional prefix function is concave, so endpoint positivity implies
positivity throughout the interval.

It is therefore enough to prove stability for this finite endpoint list.

On the active window, each endpoint value is a finite sum of:

```text
-q_i log q_i,
q_i H_A(i),
affine mass/mean terms,
```

plus the fixed clipping normalization:

```text
-(1-|q|)log(1-|q|).
```

For masses in `[delta,1-delta]`, the derivative of the clipping
normalization is bounded by a constant depending only on `delta`.

For the coordinate terms, the derivative of `-z log z` is `-(log z+1)`.
On the active window before the negligible tail cutoff, the Gaussian profile
satisfies:

```text
p_i >= exp(-C i^2) >= n^{-C'}
```

for every occupied endpoint coordinate `i<=I_n=C_0 sqrt(log n)`.  Thus:

```text
|log p_i|+1 = O(log n).
```

The potential term satisfies:

```text
|H_A(i)|=O(i^2)=O(log n).
```

Consequently every endpoint functional has an `L^1` Lipschitz constant:

```text
O(log n)
```

on the active window.  The number of active endpoint coordinates is only
`O(sqrt(log n))`, and the rounded profile differs from the real profile by
changing `O(polylog n)` counts, so:

```text
||hat p-p||_1 = O(polylog n/k).
```

The perturbation `hat p-p` has `L^1` size `epsilon_n` and the discarded tail
has mass and first moment `n^{-B}`.  Hence every certified prefix endpoint
changes by:

```text
O(log n) epsilon_n + O(n^{-B} log n)=o(1).
```

Since the G4 transfer theorem supplies a fixed positive prefix margin:

```text
Prefix_A^{(r)}(p;x) >= c_r^{exact}>0,
```

the rounded profile satisfies, for all large `n`:

```text
Prefix_A^{(r)}(hat p;x) >= c_r^{exact}/2.
```

Finally, the endpoint list for `hat p` may be shifted by the rounding
perturbation because `hat P_s=sum_{i<=s}hat p_i` differs from
`P_s=sum_{i<=s}p_i` by at most `epsilon_n`.  On each prefix interval the
same one-dimensional endpoint function has derivative bounded by
`O_delta(log n)`, so moving the endpoint mass by at most `epsilon_n` changes
the value by another `O_delta(log n)epsilon_n=o(1)`.  Thus both the old
certificate endpoints and the rounded-profile endpoints retain positive
margin.

## Theorem

For the P3 rounded profile `hat p` produced by:

```text
p3-specific-rounding-theorem-2026-05-13.md,
```

uniformly for:

```text
x in [0,0.029155],
r in {2,3},
```

we have:

```text
Room_A^{(r)}(hat p;x)=Room_A^{(r)}(p;x)+o(1),
Prefix_A^{(r)}(hat p;x)=Prefix_A^{(r)}(p;x)+o(1).
```

Consequently all fixed positive G4 room and prefix margins survive rounding.

## Status

This closes the missing P3 rounding-stability dependency for room and prefix
margins, conditional only on the already stated P3 rounding construction
properties:

```text
1. Gaussian tail cutoff;
2. active support size O(sqrt(log n));
3. O(polylog n) count perturbation preserving total mass and mean deficit;
4. prefix endpoints bounded away from mass 0 and 1 by the certificate delta.
```
