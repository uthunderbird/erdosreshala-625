# Upper-boundary alpha first-moment shift U3 closure

Date: 2026-05-13

## Purpose

This note closes the first-moment shift input `U3` for the upper-boundary
alpha-anchor route.

It applies both to:

```text
r=1 support i>=1,
r=2 support i>=2,
```

because the shift is an anchor-threshold statement at:

```text
K=boldk_alpha(n).
```

## Statement

Let:

```text
K=boldk_alpha(n),
D=O(n/log^3 n).
```

Then:

```text
L_0(n,K,alpha)-L_0(n,K-D,alpha)
  = (2/log 2 + o(1)) D log^2 n.
```

For:

```text
D=c_D n/log^3 n,
```

this is:

```text
(2c_D/log 2 + o(1)) n/log n.
```

## Source inputs

The source chain is:

```text
1. HR derivative / one-more-colour estimate for t=alpha_0-O(1);
2. HR Lemma k* with beta=alpha, locating boldk_alpha in the threshold window;
3. the same finite-shift integration argument used in
   p3-exact-finite-shift-cost-theorem-2026-05-13.md.
```

The relevant derivative is:

```text
partial_k L_0(n,k,alpha)
  = (2/log 2)log^2 n + O(log n log log n)
```

uniformly for:

```text
k=K+O(n/log^3 n).
```

Uniformity follows because HR gives the derivative for:

```text
t=alpha_0-O(1),
k=n/(t-Theta(1)),
```

and the closed alpha threshold-location result gives:

```text
K=boldk_alpha=n/(alpha-Theta(1)).
```

Changing `k` by `O(n/log^3 n)` changes `n/k` by only `O(1/log n)`, so the
whole interval remains in the same HR derivative window.

## Proof

Integrate the derivative estimate over:

```text
k in [K-D,K].
```

The main term contributes:

```text
(2/log 2)D log^2 n.
```

The error contributes:

```text
O(D log n log log n)
  = O(n log log n/log^2 n)
  = o(n/log n)
```

when:

```text
D=O(n/log^3 n).
```

Since the main term is `Theta(D log^2 n)`, the relative error is:

```text
O(log log n/log n)=o(1).
```

This proves:

```text
L_0(n,K,alpha)-L_0(n,K-D,alpha)
  = (2/log 2 + o(1))D log^2 n.
```

## Role in the upper-boundary route

This shift theorem supplies the colour-count-to-exponent conversion needed
by the profitable-profile bridge:

```text
D=c_D n/log^3 n
=> shift cost = Theta(n/log n).
```

Thus any limiting room certificate with fixed positive room can pay for a
small enough `c_D>0` and still leave:

```text
E[Z^co] >= exp(c_FM n/log n)
```

provided the finite-transfer and rounding losses are controlled.

## Status

`U3` / `R2-U3` is closed.

The remaining issue is not the derivative cost; it is choosing `c_D` small
enough after `U1/U2/U4` finite and rounding budgets are known.
