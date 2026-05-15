# Upper-boundary alpha first-moment slope theorem

Date: 2026-05-13

## Purpose

This note supplies the slope input needed by:

```text
upper-boundary-alpha-first-moment-lowerbound-sublemma-2026-05-13.md
```

It is the `a=alpha` analogue of the shift-cost derivative theorem already
used at the `alpha-1` anchor.

## Source input

Heckel 2024 cites the HR derivative estimate:

```text
d/dk L_0(n,k,alpha-1)
  = (2/log 2) log^2 n + O(log n log log n)
```

uniformly in the threshold window.

HP/HR formulate `L_0(n,k,t)` for general:

```text
t=O(log n),
1<n/k<t.
```

The same calculation is local in `t` and applies for fixed bounded shifts
of the independence threshold.  The alpha-anchor route requires this
uniformity at:

```text
t=alpha.
```

This is a source-check item: the final paper must cite the general HR
statement rather than only the `alpha-1` specialization printed in Heckel
2024.

## Theorem

Assume the HR derivative estimate is available uniformly for:

```text
t=alpha,
k = boldk_alpha + O(1).
```

Then:

```text
L_0(n,k+1,alpha)-L_0(n,k,alpha)
  = (2/log 2 + o(1)) log^2 n
```

uniformly for:

```text
k in {boldk_alpha-2, boldk_alpha-1}.
```

## Proof

At the alpha-bounded threshold:

```text
boldk_alpha = Theta(n/log n),
n/boldk_alpha = alpha_0 - 1 - 2/log 2 + o(1).
```

Thus:

```text
boldk_alpha = n/(alpha-Theta(1)).
```

The two values:

```text
k = boldk_alpha-2,
k = boldk_alpha-1
```

remain in the same threshold window.  Integrating the derivative estimate
over an interval of length `1` gives:

```text
L_0(n,k+1,alpha)-L_0(n,k,alpha)
  = (2/log 2)log^2 n + O(log n log log n).
```

The error is `o(log^2 n)`, proving the theorem.

## Consequence for expected colourings

If the approximation:

```text
log E_{n,k,alpha}=L_0(n,k,alpha)+O(log^{3/2}n)
```

or the weaker:

```text
log E_{n,k,alpha}=L_0(n,k,alpha)+O(log^4 n)
```

is used naively, a one-colour slope of order `log^2 n` is not enough to
dominate an `O(log^4 n)` absolute error.  Therefore the cleanest proof of:

```text
E_{n,boldk_alpha-2,alpha}->0
```

should use the threshold definition plus a direct monotonicity/one-more
colour comparison for `E_{n,k,alpha}`, as HP's `onemorecolour` lemma does,
rather than subtracting two coarse `L_0` approximations.

With that one-more-colour comparison in hand, this slope theorem supplies
the needed exponential drop:

```text
E_{n,boldk_alpha-2,alpha}
  <= exp(-c log^2 n) E_{n,boldk_alpha-1,alpha}
  <= exp(-c log^2 n).
```

## Status

This closes the analytic slope calculation conditional on citing the general
HR derivative estimate at `t=alpha`.

The remaining source-check is:

```text
HP/HR one-more-colour comparison applies at a=alpha.
```

Once that is cited, U7.1 is closed.
