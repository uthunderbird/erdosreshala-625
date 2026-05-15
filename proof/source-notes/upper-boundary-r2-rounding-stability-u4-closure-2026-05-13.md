# Upper-boundary r=2 rounding stability U4 closure

Date: 2026-05-13

## Purpose

This note closes the rounding-stability input `R2-U4` for the upper-boundary
alpha-anchor `r=2` route, conditional on the exact finite profile from
`R2-U1/R2-U2`.

It adapts:

```text
p3-specific-rounding-theorem-2026-05-13.md
p3-rounding-stability-room-prefix-lemma-2026-05-13.md
```

to the upper-boundary alpha-anchor profile with support:

```text
i>=2.
```

## Inputs

Assume `R2-U1/R2-U2` supply an exact finite alpha-anchor `r=2` profile
`p=p_{n,x}^{up,2}` with:

```text
support i>=2,
consecutive support on its active window,
mean deficit T_alpha(x)+o(1),
k=boldk_alpha-D+O(1)=Theta(n/log n),
D=O(n/log^3 n),
room >= R_2^{finite}>0,
prefix/lower-boundbeta margin >= P_2^{finite}>0,
Gaussian tail p_i <= exp(-c i^2+O(i)),
finite potential H_alpha(i)=O(i^2) on i<=C sqrt(log n).
```

These are the same structural hypotheses used by the P3 rounding theorem;
only the anchor family changes from `alpha-1` to `alpha`.

## Rounding construction

Choose:

```text
I_n=C sqrt(log n).
```

The Gaussian tail gives, for any fixed `B`, after increasing `C`:

```text
sum_{i>I_n} p_i <= n^{-B},
sum_{i>I_n} i p_i <= n^{-B}.
```

Set preliminary integer counts:

```text
m_i=floor(k p_i), 2<=i<=I_n,
m_i=0,             i>I_n.
```

The mass and deficit errors are:

```text
O(I_n^2)=O(log n).
```

Because the support is consecutive from `i=2` and the Gibbs profile has
positive mass on a fixed block around its mean, these errors can be corrected
by changing `O(polylog n)` counts among adjacent allowed deficits.  The
support condition `i>=2` is preserved throughout.

The resulting empirical profile `hat p` satisfies:

```text
||hat p-p||_1 = O(polylog n/k),
sum_i i(hat p_i-p_i)=0
```

up to an `O(1)` final divisibility correction.  Since:

```text
k=Theta(n/log n),
```

we have:

```text
||hat p-p||_1=o(log^{-M} n)
```

for every fixed `M`.

## Room stability

On the active window:

```text
|H_alpha(i)|=O(i^2)=O(log n),
|log p_i|+1=O(log n).
```

Therefore changing `O(polylog n)` counts changes the profile-scale objective
by:

```text
O(polylog n/k)=o(1).
```

The exact finite room functional is a difference of such objectives at fixed
mass and mean, and the rounding preserves mass and mean up to the harmless
final `O(1)` correction.  Hence:

```text
Room(hat p)=Room(p)+o(1).
```

In particular, if:

```text
Room(p)>=R_2^{finite}>0,
```

then for all sufficiently large `n`:

```text
Room(hat p)>=R_2^{finite}/2.
```

## Prefix stability

The prefix/lower-boundbeta functionals are evaluated on prefix-saturated
subprofiles with total mass bounded away from `0` and `1`.  On this domain
the clipping term:

```text
-(1-|q|)log(1-|q|)
```

has bounded derivative depending only on the guard parameter.

For coordinate terms on the active window:

```text
|d(-z log z)/dz|=|log z+1|=O(log n),
|H_alpha(i)|=O(log n).
```

Thus every certified prefix endpoint has `L^1` Lipschitz constant
`O(log n)`.  Since:

```text
||hat p-p||_1=O(polylog n/k),
```

each endpoint changes by:

```text
O(log n * polylog n/k)=o(1).
```

The rounded endpoint locations can move by at most `||hat p-p||_1`, and the
same one-dimensional Lipschitz bound controls this movement.  Therefore:

```text
Prefix(hat p)=Prefix(p)+o(1).
```

If:

```text
Prefix(p)>=P_2^{finite}>0,
```

then:

```text
Prefix(hat p)>=P_2^{finite}/2
```

for all sufficiently large `n`.

## Tail/relevance

The Gaussian tail also gives the standard HP relevance bounds after rounding:

```text
k_u u/n <= C p_i <= 2^{-i gamma(i)}
```

for an increasing `gamma(i)->infinity`, after weakening constants and taking
`n` large.  The omitted tail and `O(polylog n)` rounding perturbation are
absorbed into the same bounds.

## Output

Given the exact finite alpha-anchor `r=2` profile from `R2-U1/R2-U2`, there
is an integer rounded profile `bf{k}^{up,2}` satisfying:

```text
sum_u k_u = boldk_alpha-D+O(1),
sum_u u k_u = n,
k_u=0 for u>alpha-2,
tail/relevance hypotheses,
room >= R_2^{finite}/2,
prefix/lower-boundbeta >= P_2^{finite}/2.
```

## Status

`R2-U4` is closed conditional on `R2-U1/R2-U2` supplying the exact finite
Gaussian-tail profile and positive finite margins.
