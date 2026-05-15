# R4 C3 first-moment preservation: full lemma

Date: 2026-05-12

## Purpose

This note upgrades C3 from a proof sketch to a standalone lemma usable in
the low-regime R4 proof.

The lemma is intentionally separated from the optimizer certificate.  It
does not prove that the constrained low-regime profile exists; it proves
that any profile satisfying the standard HP/Heckel fixed-partition
regularity hypotheses loses only a `1+o(1)` factor when Heckel's
restricted events are imposed on cocolourings.

## Definitions

Fix a complete profile `bf{k}` and a labelled vertex partition `pi` with
that profile.  Let `A_pi^co` be the event that every part of `pi` is either
an independent set or a clique.

Equivalently,

```text
A_pi^co = disjoint union over sigma in {-,+}^{|bf{k}|} A_{pi,sigma},
```

where `sigma(V_i)=-` means that the part `V_i` is required to be
independent, and `sigma(V_i)=+` means that it is required to be a clique.

Let `B_pi,C_pi,D_pi` denote the HP/Heckel restricted-colouring events for
forbidden independent-set structures:

1. `B_pi`: no relevant independent set has a forbidden intermediate
   composition pattern across parts;
2. `C_pi`: every relevant 2-composed independent set is extremal, with
   one vertex in one part and all remaining vertices in the other;
3. `D_pi`: the number of near-part independent sets is at most the
   permitted polylogarithmic bound.

Let `B_pi^+ , C_pi^+ , D_pi^+` denote the identical events after replacing
independent sets by cliques.  Define

```text
R_pi =
  B_pi cap C_pi cap D_pi
  cap B_pi^+ cap C_pi^+ cap D_pi^+.
```

Define the unrestricted and restricted cocolouring counts

```text
X_bf{k}^co = sum_{pi in Pi_bf{k}} 1_{A_pi^co},
Z_bf{k}^co = sum_{pi in Pi_bf{k}} 1_{A_pi^co cap R_pi}.
```

## Profile hypotheses

The lemma applies to any profile `bf{k}` satisfying:

1. `k_1=0`;
2. all nonzero class sizes lie in `u_* <= u <= alpha-1`;
3. `u_* = alpha-o(alpha)`;
4. total number of parts `|bf{k}| = Theta(n/log n)`;
5. the HP tail condition, uniformly in the deficit `r=alpha-u`,

   ```text
   k_u u/n <= 2^{-r gamma(r)}
   ```

   for some increasing `gamma(r)->infinity`;

6. the HP/Heckel fixed-partition restriction estimates hold uniformly for
   every labelled partition `pi` with profile `bf{k}`:

   ```text
   P(not B_pi | A_pi^-) = o(1),
   P(not C_pi | A_pi^-) = o(1),
   P(not D_pi | A_pi^-) = o(1),
   ```

   where `A_pi^-` is the event that all parts of `pi` are independent.

Hypothesis 6 is the only source-backed input.  In HP/Heckel it is proved
from the size range, `Theta(n/log n)` part count, and the tail condition by
fixed-partition union/Markov estimates.  It is stated explicitly here so
that C3 does not depend on the global ordinary-colouring first moment.

## Lemma

Under the profile hypotheses,

```text
P(R_pi | A_pi^co) = 1-o(1)
```

uniformly over labelled partitions `pi` with profile `bf{k}`.

Consequently,

```text
E[Z_bf{k}^co] = (1-o(1)) E[X_bf{k}^co].
```

## Proof

Fix `pi` and a sign assignment `sigma`.

Conditioning on `A_{pi,sigma}` only fixes internal edges of the parts:
edges inside `sigma=-` parts are absent and edges inside `sigma=+` parts
are present.  Edges between distinct parts remain mutually independent
with parameter `1/2`.

### Independent-set restrictions

The bad events `not B_pi`, `not C_pi`, and `not D_pi` are increasing in the
availability of independent-set witnesses.  For the fixed partition, every
such witness uses either cross-part edges or vertices inside parts.  Turning
an independent part into a clique can only add internal edges inside that
part, and adding edges cannot create new independent sets.

Therefore, for every sign assignment `sigma`,

```text
P(not B_pi | A_{pi,sigma})
  <= P(not B_pi | A_pi^-),
P(not C_pi | A_{pi,sigma})
  <= P(not C_pi | A_pi^-),
P(not D_pi | A_{pi,sigma})
  <= P(not D_pi | A_pi^-).
```

By the uniform HP/Heckel fixed-partition estimates, all three right-hand
sides are `o(1)`, uniformly in `pi` and `sigma`.

### Clique restrictions

Apply the same argument in the complement graph.  Under complementation,
`G(n,1/2)` has the same distribution, independent parts become clique
parts, clique parts become independent parts, and the events
`B_pi^+,C_pi^+,D_pi^+` become the corresponding independent-set events.

Thus the same uniform bounds give

```text
P(not B_pi^+ | A_{pi,sigma}) = o(1),
P(not C_pi^+ | A_{pi,sigma}) = o(1),
P(not D_pi^+ | A_{pi,sigma}) = o(1).
```

### Combine restrictions

The union bound gives, uniformly in `pi` and `sigma`,

```text
P(not R_pi | A_{pi,sigma}) = o(1).
```

Since the events `A_{pi,sigma}` are disjoint and their union is `A_pi^co`,

```text
P(not R_pi | A_pi^co)
 = sum_sigma P(A_{pi,sigma} | A_pi^co)
             P(not R_pi | A_{pi,sigma})
 = o(1).
```

Hence

```text
P(A_pi^co cap R_pi) = (1-o(1)) P(A_pi^co)
```

uniformly over `pi`.

Summing over all labelled partitions with profile `bf{k}` gives

```text
E[Z_bf{k}^co]
 = sum_pi P(A_pi^co cap R_pi)
 = (1-o(1)) sum_pi P(A_pi^co)
 = (1-o(1)) E[X_bf{k}^co].
```

This proves C3.

## What remains outside C3

This lemma deliberately leaves the following tasks to other C-conditions:

1. C1 constructs the constrained low-regime profile and verifies the tail
   condition after finite rounding.
2. C2 proves `E[X_bf{k}^co] >= exp(c n/log n)`.
3. C4 proves lower-boundbeta/prefix positivity for middle overlaps.
4. C5 uses C2--C4 and this C3 lemma to prove the co-tame second moment.

## Paper-integration note

In the final proof, Hypothesis 6 should be discharged by quoting the exact
HP/Heckel lemmas for `B,C,D`.  The important audit point is that these are
fixed-partition conditional estimates; they do not require the ordinary
global expectation lower bound that fails in the low-`mu_alpha`
alpha-minus-one regime.
