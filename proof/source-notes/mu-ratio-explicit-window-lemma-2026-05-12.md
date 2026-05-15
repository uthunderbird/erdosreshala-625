# Explicit `mu_t` ratio window lemma

Date: 2026-05-12

## Purpose

This note replaces the informal statement

```text
mu_{t-1}/mu_t = Theta(n/log n)
```

by explicit eventual constants over the bounded anchor-shift window needed
by `SHIFT-GATE`.

## Setup

Let

```text
mu_t = binom(n,t) 2^{-t(t-1)/2}.
```

Then exactly:

```text
mu_{t-1}/mu_t = [t/(n-t+1)] 2^{t-1}.
```

Let

```text
L = log_2 n,
ell = log_2 L.
```

Fix a constant `C>=1`.  Assume `t` lies in the standard bounded-shift
threshold window

```text
2L-2ell-C <= t <= 2L-2ell+C.
```

This is the only input about the precise anchor location required by this
ratio lemma.

## Lemma

For all sufficiently large `n`, uniformly over all integer `t` in the
window above,

```text
2^{-C-1} n/L <= mu_{t-1}/mu_t <= 3*2^{C-1} n/L.
```

Equivalently, with natural logarithms,

```text
(log 2)2^{-C-1} n/log n
  <= mu_{t-1}/mu_t
  <= 3(log 2)2^{C-1} n/log n.
```

## Proof

The exact ratio gives

```text
mu_{t-1}/mu_t = [t/(n-t+1)] 2^{t-1}.
```

Since `t=2L+O(ell+C)`, for all sufficiently large `n`,

```text
L <= t <= 3L,
n/2 <= n-t+1 <= n.
```

The window also gives

```text
2^{-C-1} n^2/L^2 <= 2^{t-1} <= 2^{C-1} n^2/L^2.
```

Combining lower bounds:

```text
[t/(n-t+1)]2^{t-1}
  >= (L/n) * 2^{-C-1} n^2/L^2
  = 2^{-C-1} n/L.
```

Combining upper bounds:

```text
[t/(n-t+1)]2^{t-1}
  <= (3L/(n/2)) * 2^{C-1} n^2/L^2.
```

This gives `6*2^{C-1} n/L` with the crude `n/2` denominator.  A sharper
eventual bound uses `n-t+1 >= (1-o(1))n`; absorbing the `1+o(1)` factor
into `3` for large `n` gives:

```text
mu_{t-1}/mu_t <= 3*2^{C-1} n/L.
```

The constants are intentionally not optimized.

## Two-step consequence

For `t,t-1` in the same bounded-shift window, the reciprocal bound gives

```text
mu_t <= [2^{C+1} L/n] mu_{t-1},
mu_{t-1} <= [2^{C+1} L/n] mu_{t-2}.
```

Therefore, if

```text
mu_{t-2} <= n log^4 n,
```

then

```text
mu_t <= 2^{2C+2} L^2 log^4 n / n = o(1).
```

This is the explicit scarcity trigger used in the recursive endpoint
shift.

## Status

This closes the constant-level part of the ratio calculation, conditional
only on the standard bounded threshold-window inclusion for the active
anchors.  The remaining SHIFT work is index alignment and source quotation
for the bounded lower bounds.

