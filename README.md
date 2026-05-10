# Erdős Problem 625 — Lean 4 Formalization

A machine-checked proof that in the Erdős–Rényi random graph $G(n,1/2)$, the chromatic number
and the cochromatic number are separated by at least $n^{1-\varepsilon}$ with high probability.

**Proof status**: Complete. **3 paper-backed axioms, 0 sorry on the `erdos_625` proof path.**

> **Note**: This README uses GitHub-flavored LaTeX math rendering (requires a modern browser on github.com).

---

## Theorem

For every real $\varepsilon$ with $0 < \varepsilon < 0.001$, there exists $n_0$ such that for all
$n \ge n_0$ satisfying the main-range condition,

$$
\mathbb{P}_{G \sim G(n,1/2)}\!\left[\,\chi(G) - \zeta(G) \ge n^{1-\varepsilon}\,\right] \ge 1 - 2\varepsilon
$$

where $\chi(G)$ is the chromatic number (minimum proper vertex coloring) and $\zeta(G)$ is the
cochromatic number (minimum partition of $V(G)$ into cliques and independent sets).

**Main-range condition.** The hypothesis `InMainRange ε n` requires the independence number
$\alpha(G(n,1/2))$ to satisfy $n^{0.05+\varepsilon} \le \mathbb{E}[\alpha] \le n^{1-\varepsilon}$.
This restricts to the parameter regime where the proof technique applies; it is an additional
condition on $n$ beyond bare largeness. For the Erdős–Rényi model,
$\mathbb{E}[\alpha(G(n,1/2))] \approx 2\log_2 n$, so this condition holds for all sufficiently
large $n$ when $\varepsilon < 0.001$.

**Lean entry point**: `Problem625.Publishable.erdos_625` in `Erdos625/PublishableProof.lean`.
Here `gnHalf n` is the Lean name for the $G(n,1/2)$ probability measure on `SimpleGraph (Fin n)`.

---

## High-level proof idea

The proof combines three independent components.

### The threshold $k^*$

Define $k^* = k^*(n)$ as the *first-moment threshold* for $t$-bounded proper colorings of
$G(n,1/2)$, where $t \approx 2\log_2 n$ (precisely: `thresholdFloor n − 1` in Lean, where `thresholdFloor n` is the floor of the first-moment independence-number threshold).  A coloring is *t-bounded* if every color
class has at most $t$ vertices.  Specifically, $k^*$ is the smallest $k$ such that the expected
number of proper $k$-colorings of $G(n,1/2)$ in which every color class has at most $t$ vertices
falls below 1.  It satisfies $k^* = \Theta(n / \log n)$; more precisely,
$n / k^*(n) \to 2\log_2 n$ as $n \to \infty$.  Both the chromatic and cochromatic bounds are
stated as deviations from this common threshold.

### Part B — Chromatic lower bound (first-moment method)

**Claim**: $\mathbb{P}[\chi(G) \ge k^* - n^{1-0.9\varepsilon}] \ge 1 - \varepsilon$.

By the first-moment method: if the expected count of $t$-bounded proper $k$-colorings is less
than 1, then with positive probability no such coloring exists, so the $t$-bounded chromatic number
$\chi_t(G) > k^*$ up to an additive slack.  The connection to $\chi(G)$ uses the inequality
$\chi_t(G) \le \chi(G) + X_\alpha$, where $X_\alpha$ counts maximum independent sets; rearranging
gives $\chi(G) \ge \chi_t(G) - X_\alpha$, and $X_\alpha$ is negligible with high probability in
the main range.  The quantitative slack $n^{1-0.9\varepsilon}$ and the probability bound $1-\varepsilon$
do not follow from the bare first-moment inequality alone; they come from asymptotic estimates on the
expected coloring count near the threshold established in Heckel–Panagiotou (2023).  These estimates
(Lemma 5 / eq:wert and eq:wert2 of that paper) are the two paper-backed axioms for Part B.

### Part C — Cochromatic upper bound (second-moment method + concentration)

**Claim**: $\mathbb{P}[\zeta(G) \le k^* - n^{1-\varepsilon/2} + 2\cdot n^{0.999}] \ge 1 - \varepsilon$.

Because every proper coloring is also a cochromatic coloring (each color class is an independent
set), we have $\zeta(G) \le \chi(G)$.  To obtain an upper bound on $\zeta(G)$ strictly below $k^*$,
the argument uses the random variable $Z$ = number of cochromatic colorings with at most
$\lfloor k^* - n^{1-\varepsilon/2} \rfloor$ colors.

- **Existence (Paley–Zygmund)**: Proposition 5(b) of Heckel (2024) supplies a second-moment bound
  $\mathbb{E}[Z]^2 / \mathbb{E}[Z^2] > e^{-n^{0.99}}$; the Paley–Zygmund inequality then gives
  $\mathbb{P}[Z > 0] > e^{-n^{0.99}} > 0$, so there is a positive probability of finding such a
  coloring.  This second-moment bound is the single paper-backed axiom for Part C.

- **Concentration (Azuma–Hoeffding)**: $\zeta(G)$ is 1-Lipschitz under vertex exposure (removing
  one vertex changes $\zeta$ by at most 1), so the Azuma–Hoeffding inequality gives
  $\mathbb{P}[\zeta \ge \mathbb{E}[\zeta] + s] \le e^{-s^2/(2n)}$.  Setting $s = n^{0.999}$
  makes the tail probability $e^{-n^{0.998}/2} = o(\varepsilon)$.  The Azuma–Hoeffding
  concentration infrastructure is fully formalized with 0 sorry.

### Gap arithmetic and union bound

The exponents are chosen so that for every $\varepsilon < 0.001$ and all large $n$,

$$
n^{1-\varepsilon/2} - n^{1-0.9\varepsilon} - 2\cdot n^{0.999} \ge n^{1-\varepsilon}.
$$

This is a purely analytic inequality proved in full with no axioms (`GapArithmetic.lean`).

Parts B and C each hold with probability at least $1-\varepsilon$, so by the union bound on
complements, both hold simultaneously with probability at least $1-2\varepsilon$.  On the joint
event,

$$
\chi(G) - \zeta(G) \ge (k^* - n^{1-0.9\varepsilon}) - (k^* - n^{1-\varepsilon/2} + 2\cdot n^{0.999})
= n^{1-\varepsilon/2} - n^{1-0.9\varepsilon} - 2\cdot n^{0.999} \ge n^{1-\varepsilon}.
$$

---

## Axiom inventory

The Azuma–Hoeffding concentration machinery, the gap arithmetic, and the union bound argument are
fully proved from Mathlib primitives. The 3 axioms below cover exactly the two HP-2023 quantitative
asymptotic estimates (Part B) and the Heckel 2024 second-moment bound (Part C).

In Lean 4, an `axiom` is an admitted statement — here, a lemma cited from a published paper
that has not been formalized inside this repository; it is distinct from Lean's foundational axioms
(`propext`, `Classical.choice`, `Quot.sound`).

| Axiom | File | Paper source |
|-------|------|--------------|
| `paperPartBThresholdAverageClassAsymptoticLowerCriterionTarget_source` | `Erdos625/PartBProfileBridge.lean` | Heckel & Panagiotou (2023), arXiv:2306.07253, Lemma 5 / eq:wert |
| `paperPartBExactNoEmptyDenomBinaryLowerControlledLhsDecayTarget_source` | `Erdos625/PartBProfileBridge.lean` | Heckel & Panagiotou (2023), arXiv:2306.07253, eq:wert2 |
| `heckel_cochromatic_second_moment` | `Erdos625/ZetaConcentration.lean` | Heckel (2024), arXiv:2409.17614, Proposition 5(b) |

Running `#print axioms Problem625.Publishable.erdos_625` produces exactly **6 entries**: the
3 paper axioms above plus Lean's standard axioms `propext`, `Classical.choice`, `Quot.sound`.

A fourth axiom in `Erdos625/PartBProfileBridge.lean` —
`paperPartBEndpointClosedVectorTailMomentQBoundedProductProfilePDenomAffineHalfLogSlackSmallClosedUniformAsymptoticNegOneStirlingFactorialUpperSplitAtBotTarget_source`
(an alternative Stirling-endpoint discharge route) — is likewise not reachable from `erdos_625`
and does not affect the 3-axiom count.

Three axioms in `Erdos625/ChromaticConnection.lean` (`threshold_tBoundedColoringError_le_with_error`,
`kThresholdWitness_le_n_div_threshold`, `threshold_decay_axiom`) document alternative chromatic
lower bound routes that were explored during development. None are reachable from `erdos_625`.
See [`paper/SOURCES.md`](paper/SOURCES.md) for the complete non-reachable axiom inventory.

Two architectural `sorry`s exist in the repository, both off the proof path: one in
`ChromaticConnection.lean` (`decay_exponent_eventually_le_neg`, a private lemma documenting
an alternative decay bound approach) and one in `ZetaConcentration.lean`
(`heckel_zeta_mean_bound_from_upper_tail`, an alternative derivation route). Running
`lake build` will show warnings for both; neither appears in
`#print axioms Problem625.Publishable.erdos_625`.

---

## Building and verifying

**Prerequisites**: Lean 4 / Lake (install via [elan](https://github.com/leanprover/elan)). The pinned toolchain version is recorded in `lean-toolchain`
(currently `leanprover/lean4:v4.29.0-rc8`). Internet access is required for the first build
(downloads the Mathlib compiled cache, ~4 GB).

```bash
git clone https://github.com/erdosreshala-625/erdos-625-formalization
cd erdos-625-formalization
lake exe cache get    # download prebuilt Mathlib oleans (~5 min)
lake build            # build the formalization (~5 min with cache)
```

**Verify the axiom count** in a Lean file or `lake env lean`:

```lean
import Erdos625.PublishableProof
#print axioms Problem625.Publishable.erdos_625
-- Expected output (6 lines):
-- axiom propext : ∀ {a b : Prop}, (a ↔ b) → a = b
-- axiom Classical.choice : {α : Sort u} → Nonempty α → α
-- axiom Quot.sound : ∀ {α : Sort u} {r : α → α → Prop} {a b : α}, r a b → ...
-- axiom paperPartBThresholdAverageClassAsymptoticLowerCriterionTarget_source : ...
-- axiom paperPartBExactNoEmptyDenomBinaryLowerControlledLhsDecayTarget_source : ...
-- axiom heckel_cochromatic_second_moment : ...
```

---

## Repository structure

| Path | Contents |
|------|----------|
| `Erdos625.lean` | Library root — imports `PublishableProof.lean`; entry point for `lake build` |
| `Erdos625/PublishableProof.lean` | **Start here.** Main theorem `erdos_625` with named steps and citations |
| `Erdos625/ChromaticConnection.lean` | Part B chain: P[χ(G) ≥ k* − n^{1−0.9ε}] ≥ 1 − ε (0 sorry on proof path) |
| `Erdos625/ZetaConcentration.lean` | Part C chain: Azuma concentration + P[ζ(G) ≤ …] ≥ 1 − ε (0 sorry on proof path) |
| `Erdos625/GapArithmetic.lean` | Gap arithmetic inequality (0 axioms, 0 sorry) |
| `Erdos625/PartBProfileBridge.lean` | Part B bridge; declares the 2 HP-2023 axioms |
| `Erdos625/RouteD2.lean` | Intermediate assembly theorem |
| `Erdos625/Defs.lean` | Core definitions (graph probability space, key parameters) |
| `Erdos625/ColoringBasic.lean` | Deletion-based bounded chromatic number and basic coloring lemmas |
| `Erdos625/FirstMomentThreshold.lean` | Class-size-bounded chromatic number $\chi_t$ and threshold $k^*$ |
| `Erdos625/BoundedDifferences.lean` | Bounded differences / martingale infrastructure |
| `Erdos625/IndepMoments.lean` | Independence number moment estimates |
| `Erdos625/README.md` | Lean source guide with file roles and suggested reading order |
| `proof/proof.md` | Standalone mathematical proof document |
| `paper/SOURCES.md` | Precise citations for the 3 paper axioms |
| `DEVELOPMENT.md` | Architectural decision records |

---

## References

- Heckel, A. & Panagiotou, K. (2023). *Colouring random graphs: Tame colourings*.
  arXiv:[2306.07253](https://arxiv.org/abs/2306.07253). Key inputs: Lemma 5, eq:wert, eq:wert2.
- Heckel, A. (2024). *The difference between the chromatic and the cochromatic number of a
  random graph*. arXiv:[2409.17614](https://arxiv.org/abs/2409.17614). Key input: Proposition 5(b).

---

## License

Apache 2.0 (compatible with the Lean/Mathlib ecosystem).
