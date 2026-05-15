# C5 scrambled correction bounds for active `r=2,3` profiles

Date: 2026-05-12

## Purpose

This note updates the scrambled-correction requirement after the
parameterized amplification pivot.

The old target was:

```text
E[Z^2]/E[Z]^2 <= exp(O(log^2 n)).
```

The active target is weaker and sufficient:

```text
E[Z^2]/E[Z]^2 <= exp(Q(n)),
Q(n)=o(n/log^6 n).
```

Therefore the HP scrambled term `k_s^2/mu_s` is acceptable whenever:

```text
mu_s >> n log^4 n,
```

because `k_s=Theta(n/log n)`.

## HP scrambled form

For a rounded active profile with largest occupied size `s`, HP/Heckel give
a scrambled contribution bounded by:

```text
exp(k_s^2/mu_s + O(M_A+M_B+log^2 n)).
```

The terms `M_A,M_B` have the same formal shape as in HP Lemma 6.3 after
replacing the top size by the largest occupied size `s`.

## Uniform profile bounds

For the exact-`d_u` `r=2,3` profiles:

```text
k_u <= K n/log n
```

for all occupied sizes `u`, after rounding, for some absolute `K`.  This is
part of the certificate output.

The largest occupied sizes are:

```text
r=2: s=alpha-2,
r=3: s=alpha-3.
```

## Sufficient scale condition

Assume:

```text
mu_s >= omega(n) n log^4 n,
omega(n)->infinity.
```

Then:

```text
k_s^2/mu_s
  <= K^2 n^2/log^2 n / (omega n log^4 n)
  = O(n/(omega log^6 n))
  = o(n/log^6 n).
```

Also:

```text
log^2 n = o(n/log^6 n).
```

## Correction terms

Using `k_u <= K n/log n` and `mu_s >= omega n log^4 n`, the HP correction
terms satisfy:

```text
M_B = k_s^4 log^2 n/(n mu_s^2)
    <= O(n/(omega^2 log^6 n))
    = o(n/log^6 n),
```

```text
n/(mu_s log n)
  <= O(1/(omega log^5 n)) = o(1),
```

```text
(k_s^2 log^3 n + k_s k_{s-1} log^2 n)/(mu_s n)
  <= O(1/(omega log^3 n)) = o(1),
```

and

```text
(k_{s-2}log n+k_{s-1}log^2 n+k_s log^3 n)^2/(mu_s n^2)
  <= O(1/(omega n)) = o(1).
```

Thus:

```text
k_s^2/mu_s + M_A+M_B+O(log^2 n)=o(n/log^6 n).
```

## Application to active split

At anchor `a=alpha-1`:

```text
r=2 uses s=alpha-2 and requires mu_{alpha-2} >> n log^4 n;
r=3 uses s=alpha-3 and requires mu_{alpha-3} >> n log^4 n.
```

The index-aligned endpoint split ensures one of these active profiles is
used only in its valid scrambled-scale regime.

## Certificate fields needed

The exact-`d_u` certificate generator should emit enough data to confirm:

```text
largest_occupied_size,
profile_coordinate_upper <= K n/log n,
mu_largest_scale_status,
M_A_upper,
M_B_upper,
scrambled_Q_upper,
scrambled_Q_status=o(n/log^6 n).
```

For a paper proof, these may be stated as deterministic asymptotic lemmas
attached to the rounded profile construction rather than numeric CSV
fields.

## Status

This closes the quantitative correction-term calculation conditional on
the exact-`d_u` certificate supplying the uniform `k_u=O(n/log n)` profile
bound and the regime split supplying `mu_s >> n log^4 n`.

