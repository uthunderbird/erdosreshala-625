# Upper-boundary alpha average-colour-class theorem

Date: 2026-05-13

## Purpose

This note states the narrow first-moment threshold-location theorem needed to
close `U8a` in the upper-boundary alpha-anchor route.

It is the missing input isolated by:

```text
upper-boundary-alpha-one-more-colour-source-check-2026-05-13.md
```

## Theorem target

Let:

```text
boldk_alpha(n) = min { k : E_{n,k,alpha} >= 1 }.
```

Then:

```text
n / boldk_alpha(n)
  = alpha_0 - 1 - 2/ln 2 + o(1).
```

In particular:

```text
boldk_alpha(n) = n/(alpha-Theta(1)),
```

so the HR one-more-colour derivative lemma applies uniformly at:

```text
t = alpha,
k in {boldk_alpha-2, boldk_alpha-1}.
```

## Source route

The HP text proves the corresponding `averagecolourclass` lemma only for:

```text
t in {alpha-1, alpha-2}.
```

However, the immediately preceding source material is not inherently limited
to those two anchors:

```text
1. HR maximizer formula for L_0 is stated for general 1 < rho < t.
2. HR y-bound is stated for t = alpha_0 - O(1).
3. HR one-more-colour derivative is stated for t = alpha_0 - O(1).
4. HP improved approximation is stated for t = alpha - O(1).
```

Thus the expected proof is to repeat the printed derivation of
`averagecolourclass`, using `t=alpha`, but with one real new endpoint:

```text
i_0 = alpha-t = 0.
```

The printed HP convergence and partial-profile sections are written for
`i_0 in {1,2}` because their applications use `t in {alpha-1,alpha-2}`.
For the present theorem the optimizer includes `i=0`, corresponding to
`alpha`-sized colour classes.  This endpoint must be handled explicitly.

## Proof skeleton

Let:

```text
rho = n/k.
```

For `t=alpha`, the continuous optimizer of `L_0(n,k,t)` is described by the
same HR Lagrange multiplier equations:

```text
p_u = exp(x_t(rho)+u y_t(rho)) / d_u.
```

In deficit variables:

```text
i = alpha-u,
xi_i = p_{alpha-i},
```

the optimizer satisfies:

```text
xi_i = exp(h_n(i)+lambda_n+mu_n i),
0 <= i <= alpha-1,
sum_i xi_i = 1,
sum_i i xi_i = alpha-rho.
```

The source `ybound` lemma gives:

```text
lambda_n = O(1),
mu_n = O(1)
```

uniformly whenever:

```text
rho = t-Theta(1).
```

The threshold equation:

```text
E_{n,k,alpha} ~= 1
```

is equivalent, through the improved approximation

```text
ln E_{n,k,alpha} = L_0(n,k,alpha)+O(ln^{3/2} n),
```

to solving the continuous first-moment equation

```text
L_0(n,k,alpha) = o(n/log n)
```

at leading order.

The needed new convergence lemma is the `i_0=0` analogue of HP Lemma
`convergencemulambda`:

```text
lambda_n -> lambda(0,x),
mu_n -> mu(0,x),
sum_{i>=0}|xi_i-zeta_i| -> 0,
```

where:

```text
zeta_i = exp(lambda+mu i-(ln 2)i^2/2),
sum_{i>=0} zeta_i = 1,
sum_{i>=0} i zeta_i = T(x).
```

The proof should be identical to the printed proof for `i_0 in {1,2}` after
checking the endpoint `i=0`; the Gaussian tail and continuity arguments do
not rely on `i_0>=1`.

The remaining threshold-location evaluation should then yield:

```text
rho = alpha_0 - 1 - 2/ln 2 + o(1).
```

Since:

```text
rho = n/k,
```

this proves the theorem.

## Important boundary check

For `t=alpha`, the deficit support includes:

```text
i=0.
```

This is different from the `alpha-1` and `alpha-2` cases, but it is harmless
for the convergence part: the optimizer formula and the sums above already
include the endpoint `i=0`, and `h_n(0)=o(1)`.  The endpoint changes the
limiting normalization constants and may change intermediate limiting
profiles, so the threshold-location calculation must explicitly include it.
The theorem target is precisely that it does not change the leading location:

```text
rho = alpha - Theta(1).
```

and that the exact `Theta(1)` constant is still the HR/HP value:

```text
alpha_0 - alpha - 1 - 2/ln 2
```

after converting between `alpha` and `alpha_0`.

## Proof-grade subtargets

To close this theorem, prove the following three subtargets.

### A0. Endpoint convergence

Extend HP Lemma `convergencemulambda` to:

```text
i_0=0.
```

This is isolated and proved in:

```text
upper-boundary-alpha-i0-endpoint-convergence-lemma-2026-05-13.md
```

The proof is a direct adaptation of the printed proof, using:

```text
h_n(0)=o(1),
mu_n,lambda_n=O(1),
Gaussian tail domination.
```

### A1. Threshold bracketing

Show that for every fixed `epsilon>0`:

```text
L_0(n,k_-,alpha) <= -c_epsilon n/log n,
L_0(n,k_+,alpha) >=  c_epsilon n/log n,
```

where:

```text
n/k_- = alpha_0 - 1 - 2/ln 2 + epsilon,
n/k_+ = alpha_0 - 1 - 2/ln 2 - epsilon.
```

The sign convention reflects that increasing `k` decreases `rho=n/k` and
increases the expected number of colourings.

### A2. Transfer from L_0 to E

Use HP improved approximation at `t=alpha`:

```text
ln E_{n,k,alpha}=L_0(n,k,alpha)+O(ln^{3/2}n),
```

which is negligible compared with `n/log n`, to convert A1 into:

```text
E_{n,k_-,alpha} -> 0,
E_{n,k_+,alpha} -> infinity.
```

Then the threshold definition gives:

```text
k_- < boldk_alpha < k_+
```

for all sufficiently large `n`, yielding:

```text
n/boldk_alpha = alpha_0 - 1 - 2/ln 2 + o(1).
```

## Source-backed closure route for A1

HP states that its Lemma `averagecolourclass` is a direct consequence of
Lemma 41 in HR, after substituting:

```text
ln mu_alpha = theta ln n,
alpha_0 = alpha + theta + o(1).
```

HP only states the resulting lemma for:

```text
t in {alpha-1, alpha-2},
```

because those are the applications needed in that paper.  For the present
route, the desired citation is:

```text
HR Lemma 41 applies with t=alpha.
```

If HR Lemma 41 is formulated for arbitrary:

```text
t=alpha_0-O(1)
```

or equivalently for arbitrary bounded exponent:

```text
ln mu_t = theta_t ln n + o(ln n),
```

then A1 is source-backed directly.  In the alpha case:

```text
ln mu_alpha = x ln n + o(ln n),
x=alpha_0-alpha in [0,1],
```

so the substitution is exactly the same as the one described by HP.

### One-sided source already visible in HP

HP Lemma `lemmaupperbound` already gives the lower-threshold side of A1:
if:

```text
n/k > alpha_0 - 1 - 2/ln 2 + C,
```

then the expected number of complete colouring profiles is:

```text
< exp(-C ln 2 n/2 + o(n)).
```

Therefore:

```text
E_{n,k,alpha} -> 0.
```

This proves that `boldk_alpha` cannot occur at average class size larger
than:

```text
alpha_0 - 1 - 2/ln 2 + C.
```

The missing half, if HR Lemma 41 cannot be cited directly, is the matching
lower-average construction:

```text
n/k < alpha_0 - 1 - 2/ln 2 - C
    => E_{n,k,alpha} -> infinity.
```

That is the only remaining content of A1.

## Consequence for U8a

Combining this theorem with:

```text
upper-boundary-alpha-first-moment-slope-theorem-2026-05-13.md
```

gives:

```text
E_{n,boldk_alpha-2,alpha}
  <= exp(-Theta(ln^2 n)).
```

Therefore Markov gives:

```text
chi_alpha(G) >= boldk_alpha-1
```

with probability `1-o(1)`.

## Status

This note is a theorem target plus proof skeleton, not yet a fully audited
source citation.

Subtarget status:

```text
A0 endpoint convergence: closed in
  upper-boundary-alpha-i0-endpoint-convergence-lemma-2026-05-13.md;
A1 threshold bracketing: closed by HR Lemma k* with beta=alpha;
A2 transfer from L_0 to E: closed by the same HR Lemma k* plus HP improved
  approximation / threshold comparison.
```

To close it for publication, one must cite the exact HR statement equivalent
to HP's `averagecolourclass` derivation for the endpoint case `i_0=0`.  The
local source file `work/hr2023/HowDoes.tex` contains this as Lemma `k*`, whose
assumptions include `beta=alpha`.
