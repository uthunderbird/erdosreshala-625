# Upper-boundary alpha-to-ordinary transfer U8b closure

Date: 2026-05-13

## Purpose

This note closes `U8b` from:

```text
upper-boundary-alpha-anchor-r1-certificate-theorem-2026-05-13.md
```

It transfers the alpha-bounded lower bound:

```text
chi_alpha(G) >= boldk_alpha-1
```

to an ordinary chromatic lower bound with an `o(n/log^3 n)` loss.

## Transfer inequality

Let `X_{alpha+1}(G)` be the number of independent sets of size `alpha+1`.

Given any ordinary colouring of `G`, every colour class of size at least
`alpha+2` is impossible whp once `X_{alpha+1}=0`; but the following simpler
deterministic inequality is enough and does not require that stronger event.

Delete one vertex from each independent set of size `alpha+1`.  After at most
`X_{alpha+1}(G)` deleted vertices are handled as singleton additional colours,
all remaining colour classes have size at most `alpha`.  Therefore:

```text
chi_alpha(G) <= chi(G) + X_{alpha+1}(G),
```

and hence:

```text
chi(G) >= chi_alpha(G)-X_{alpha+1}(G).
```

## Markov bound for X_{alpha+1}

The standard ratio calculation gives:

```text
mu_{alpha+1}
  = mu_alpha * Theta(log n/n).
```

In the upper-boundary region:

```text
x=alpha_0-alpha in [x_1,1),
mu_alpha <= n * exp(O((log log n)^2)).
```

Thus:

```text
mu_{alpha+1}
  <= log n * exp(O((log log n)^2))
  = n^{o(1)}.
```

For any fixed `eta in (0,1)` Markov gives:

```text
P(X_{alpha+1} > n^eta)
  <= n^{o(1)-eta}
  -> 0.
```

So the event:

```text
E_tr: X_{alpha+1}(G) <= n^eta
```

holds with probability `1-o(1)`.

Since:

```text
n^eta = o(n/log^3 n),
```

the transfer loss is negligible at the required scale.

## Combined lower bound

On:

```text
E_alpha ∩ E_tr,
```

where `E_alpha` is supplied by:

```text
upper-boundary-alpha-lower-bound-u8a-closure-2026-05-13.md
```

we have:

```text
chi(G)
  >= chi_alpha(G)-X_{alpha+1}(G)
  >= boldk_alpha-1-n^eta
  = boldk_alpha-o(n/log^3 n).
```

Therefore the ordinary lower-bound event:

```text
chi(G) >= boldk_alpha-o(n/log^3 n)
```

holds with probability `1-o(1)`.

## Status

`U8b` is closed.
