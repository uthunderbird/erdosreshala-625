# R4 objective normalization audit

Date: 2026-05-12

## Purpose

Audit the objective used in the quick constrained-optimizer scan against
the HR/HP definitions of `L_0`.

## Source definitions

HP-2023 defines, for a real profile `k_u`,

```text
L_k = n log n - n + k - sum_u k_u log(k_u d_u),
d_u = 2^{binom(u,2)} u!.
```

Then

```text
L_0(n,k,t) = sup L_k.
```

Using `p_u=k_u/k` and `rho=n/k`, HP defines

```text
tilde L(rho,k,p)
  = rho log(rho k) - log k - rho + 1
    - sum_u p_u log(p_u d_u),
```

and

```text
L_0(n,k,t)=k tilde L_0(rho,k,t).
```

The maximizer has Gibbs form

```text
p_u = exp(x_t(rho)+u y_t(rho)) d_u^{-1}.
```

After changing variables `u=alpha-i`, HP rewrites this as

```text
xi_i = exp(h_n(i)+lambda_n+mu_n i),
```

with

```text
h_n(i)=-(ln2/2)i^2+o(1)
```

for bounded/small `i`.

## Audit result

The quick scan used the simplified limiting objective

```text
J(p) = -sum_i p_i log p_i - (ln2/2) sum_i i^2 p_i.
```

This gives the correct Gibbs shape

```text
p_i proportional exp(mu i - (ln2/2)i^2),
```

but it is not yet a proved normalization for objective differences in
`L_0/k`.

The missing derivation is:

```text
tilde L(p_con) - tilde L(p_un)
  = J(p_con)-J(p_un) + o(1)
```

uniformly for `x in [0,x0]`, with no extra linear or scale factor.

Additive constants independent of `p` cancel in differences, but a missing
linear term in `i` or a sign/scale error would change `DeltaJ` and hence
the first-moment room.

## Correct derivation path

Starting from

```text
-sum_u p_u log(p_u d_u)
```

put `u=alpha-i`. The term is

```text
-sum_i p_i log p_i - sum_i p_i log d_{alpha-i}.
```

HP's expansion gives

```text
-log d_{alpha-i}
  = h_n(i)
    + (alpha ln2 + ln alpha - ln2/2)i
    + f(alpha).
```

Under the profile constraints

```text
sum_i p_i = 1,
sum_i i p_i = alpha-rho = T(x),
```

the linear term in `i` and the constant `f(alpha)` are fixed. Therefore
they cancel when comparing two profiles with the same mean deficit.

Thus the profile-dependent objective difference is indeed

```text
[-sum p_i log p_i + sum p_i h_n(i)]_con
-
[-sum p_i log p_i + sum p_i h_n(i)]_un.
```

Since

```text
h_n(i)=-(ln2/2)i^2+o(1)
```

for the finite deficit range and the tail is exponentially small, the
limiting objective difference is the quick-scan `J` difference.

## Remaining proof requirement

For a rigorous certificate, replace the simplified objective by the exact
finite-`n` expression:

```text
J_n(p)
  = -sum_i p_i log p_i + sum_i p_i h_n(i),
```

with `h_n(i)` as HP defines it, and prove:

```text
J_n(p_con)-J_n(p_un)
  = J(p_con)-J(p_un)+o(1)
```

uniformly, with an explicit tail/truncation error.

The quick scan remains valid as plausibility evidence because it computes
the limiting objective difference, but it is not by itself a certificate.

## Status

Normalization concern is understood and appears fixable. The certificate
must use `J_n` or provide an explicit uniform error bound from `h_n(i)` to
`-(ln2/2)i^2`.
