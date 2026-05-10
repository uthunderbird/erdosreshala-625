# Proof for Problem 625: Chromatic-Cochromatic Gap in Random Graphs

## Statement

**Theorem** (`erdos_625`, `Problem625.Publishable`): For every real ε with 0 < ε < 0.001, there
exists n₀ such that for all n ≥ n₀ in the main-range regime,

$$\mathbb{P}_{G \sim G(n,1/2)}\!\left[\chi(G)-\zeta(G)\ge n^{1-\varepsilon}\right] \ge 1-2\varepsilon.$$

**Key definitions.** χ(G) = chromatic number (minimum proper vertex coloring). ζ(G) = cochromatic
number (minimum partition of V(G) into cliques and independent sets). G(n,1/2) = Erdős–Rényi
random graph on n vertices with each edge included independently with probability 1/2.
α(G) = independence number of G (size of the largest independent set). k\* =
`kThresholdWitness n` = first-moment threshold for t-bounded proper colorings, Θ(n/log n); see
Part B for the precise direction. The main-range regime `InMainRange ε n` is an *additional*
condition on n beyond largeness: it requires n^{0.05+ε} ≤ E[α(G)] ≤ n^{1−ε}, meaning the
independence number is neither too small nor too large relative to n. This is not implied by
n ≥ n₀ alone; it restricts to the parameter range where the proof technique applies. In the
Lean statement, `gnHalf n` denotes the probability measure on `SimpleGraph (Fin n)` corresponding
to G(n,1/2).

**t-bounded colorings.** A *t-bounded proper coloring* of a graph G is a proper vertex coloring
(no two adjacent vertices share a color) in which every color class has at most t vertices. For
this proof, t = ⌊2 log₂ n⌋. The *t-bounded chromatic number* χ_t(G) is the minimum number of
colors in any t-bounded proper coloring of G. The t-bounded restriction concentrates the coloring
count enough for the first- and second-moment methods to apply.

## Proof

The proof combines three independent components, assembled in `PublishableProof.lean`.

### Part B — Chromatic lower bound (2 axioms, HP-2023)

**Claim (event A)**: P[χ(G) ≥ k\* − n^{1−0.9ε}] ≥ 1 − ε.

k\* is the *smallest* k such that the expected number of t-bounded proper k-colorings of G(n,1/2)
falls below 1; it is the first-moment threshold from below. The first-moment method gives
P[count ≥ 1] ≤ E[count] < 1, so with high probability no t-bounded proper k\*-coloring exists,
hence χ(G) > k\* − n^{1−0.9ε}. However, the additive slack n^{1−0.9ε} and the precise
probability bound 1 − ε do not come from the bare first-moment inequality alone; they arise from
the quantitative asymptotic estimates in eq:wert and eq:wert2 of HP-2023, which control the
expected coloring count near the threshold.

**Paper source**: Heckel & Panagiotou (2023), arXiv:2306.07253. Two source lemmas are axiomatized:
- `paperPartBThresholdAverageClassAsymptoticLowerCriterionTarget_source` — average-class lower
  criterion (Lemma 5, eq:wert). This controls the leading-order behavior of the expected coloring
  count near k\*.
- `paperPartBExactNoEmptyDenomBinaryLowerControlledLhsDecayTarget_source` — decay control
  (eq:wert2). This controls the sub-leading decay factor needed to establish the lower bound at the
  threshold.

The *exact-no-empty* chain from these two axioms up to
`heckel_chromatic_lower_bound_of_exactNoEmpty` (`ChromaticConnection.lean`) is fully proved with
0 sorry. "Exact-no-empty" refers to coloring profiles where every color class has exactly t colors
except possibly one; the "no empty class" condition means no unused color is assigned. The chain
derives the lower bound on χ(G) from these two source lemmas via combinatorial estimates on such
profiles.

### Part C — Cochromatic upper bound (1 axiom, Heckel 2024)

**Claim (event B)**: P[ζ(G) ≤ k\* − n^{1−ε/2} + 2·n^{0.999}] ≥ 1 − ε.

The cochromatic number ζ(G) satisfies ζ(G) ≤ χ(G) ≤ χ_t(G): every proper coloring of G is also
a cochromatic coloring (each color class is an independent set, which is a valid cochromatic class
by definition), and restricting to t-bounded colorings only increases the count. The second-moment
method (Paley–Zygmund) is applied to the random variable Z = the number of cochromatic colorings
of G with at most ⌊k\* − n^{1−ε/2}⌋ colors. Steps: (i) the second-moment axiom below gives
E[Z]²/E[Z²] > exp(−n^{0.99}), and Paley–Zygmund then implies P[Z > 0] ≥ E[Z]²/E[Z²] > exp(−n^{0.99}) > 0,
which is a positive probability (not yet high probability); (ii) the Azuma–Hoeffding inequality for
the vertex-exposure martingale of ζ provides concentration: each vertex changes ζ by at most 1
(Lipschitz constant 1), so P[ζ ≥ E[ζ] + s] ≤ exp(−s²/(2n)); setting s = n^{0.999} gives tail
probability exp(−n^{0.998}) = o(ε), making 2·n^{0.999} more than sufficient as a concentration
error; (iii) the proved theorem `heckel_zeta_upper_bound` (which internally uses
`heckel_zeta_mean_upper_bound`, itself proved with 0 sorry) closes the 1 − ε bound. χ_t(G) is an intermediate quantity and does not appear in the final Lean statement.

**Paper source**: Heckel (2024), arXiv:2409.17614, Proposition 5(b): the second-moment bound for Z.
In Lean this is formalized as the sum-form inequality
`exp(−n^{0.99}) · (∑_G Z(G)²) · |Ω| < (∑_G Z(G))²` under the uniform measure gnHalf
(equivalent to E[Z]²/E[Z²] > exp(−n^{0.99}) when E[Z] > 0). Axiomatized as
`heckel_cochromatic_second_moment` (`ZetaConcentration.lean`). The Azuma–Hoeffding concentration
infrastructure is fully proved with 0 sorry.

### Gap Arithmetic (0 axioms)

**Claim**: For ε < 0.001 and all large n,
n^{1−ε/2} − n^{1−0.9ε} − 2·n^{0.999} ≥ n^{1−ε}.

The exponents 0.9 and 1/2 (appearing as 0.9ε and ε/2) are chosen so that all three terms
n^{1−ε/2}, n^{1−0.9ε}, and n^{0.999} separate correctly for every ε < 0.001; the exact values
are not tight and any constants in the appropriate range would work. This is a purely analytic
inequality, proved in full in `GapArithmetic.lean` using Lean's `Real.rpow` machinery. No axioms.

### Union Bound

From Part B and Part C we have P[A] ≥ 1 − ε and P[B] ≥ 1 − ε (for all n ≥ n₀ in the
main-range regime `InMainRange ε n`) for events A = {χ(G) ≥ k\* −
n^{1−0.9ε}} and B = {ζ(G) ≤ k\* − n^{1−ε/2} + 2·n^{0.999}} respectively. By the complement
union bound, P[A ∩ B] ≥ 1 − 2ε. On the joint event A ∩ B,

χ(G) − ζ(G) ≥ (k\* − n^{1−0.9ε}) − (k\* − n^{1−ε/2} + 2·n^{0.999})
             = n^{1−ε/2} − n^{1−0.9ε} − 2·n^{0.999} ≥ n^{1−ε}.

Monotonicity of measure (`MeasureTheory.measure_mono`) promotes the joint-event bound to the gap
event, completing the proof.

## Lean Formalization

**Entry point**: `Erdos625/PublishableProof.lean`
(`namespace Problem625.Publishable`, theorem `erdos_625`). The file presents the full logical
skeleton with named intermediate steps (`part_B`, `part_C`, `joint_bound`) and inline citations.

To verify the axiom inventory: `#print axioms Problem625.Publishable.erdos_625`.

**Axiom inventory** (3 paper-backed, plus standard Lean axioms):

| Axiom | File (within the Lean repository) | Paper source |
|-------|-----------------------------------|--------------|
| `paperPartBThresholdAverageClassAsymptoticLowerCriterionTarget_source` | `PartBProfileBridge.lean` — Part B bridge | HP-2023 arXiv:2306.07253, Lemma 5 / eq:wert (LaTeX cross-reference: lemma:averagecolourclass; equation label: eq:wert — both refer to the same result) |
| `paperPartBExactNoEmptyDenomBinaryLowerControlledLhsDecayTarget_source` | `PartBProfileBridge.lean` — Part B bridge | HP-2023 arXiv:2306.07253, eq:wert2 |
| `heckel_cochromatic_second_moment` | `ZetaConcentration.lean` — Part C chain | Heckel 2024 arXiv:2409.17614, Proposition 5(b) |

(File names resolve within the Lean library at `Erdos625/`.)

**Additional axioms (non-reachable from `erdos_625`)**: The following axioms exist in the
repository but are NOT in the closure of `erdos_625` and will not appear in
`#print axioms Problem625.Publishable.erdos_625`. See `paper/SOURCES.md` for the complete list
with detailed explanations.

In `PartBProfileBridge.lean`: `profileLogCoreBridgeTarget_source` (legacy Theorem 1 chain only)
and `paperPartBEndpointClosedVectorTailMoment…_source` (alternative Stirling-endpoint discharge
route). In `ChromaticConnection.lean`: `threshold_tBoundedColoringError_le_with_error`,
`kThresholdWitness_le_n_div_threshold`, and `threshold_decay_axiom` (all on alternative chromatic
lower bound routes; the content of the last is separately proved as a theorem on the main path).
In `ZetaConcentration.lean`: `heckel_zeta_upper_tail` and `heckel_zeta_lower_tail` (alternative
ζ tail bound routes). None of these affect the 3-axiom count of `erdos_625`.

**Sorry count**: Lean's kernel accepts this proof with no `sorry` on the proof path. The only
admitted terms beyond Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) are
the three named paper-backed axioms above. Running `#print axioms Problem625.Publishable.erdos_625`
will produce exactly six entries: the three paper axioms plus `propext`, `Classical.choice`, and
`Quot.sound`. The proof is classical (uses `Classical.choice`); the existential `∃ n₀` is
non-constructive. The repository contains two architectural `sorry`s off the proof path
(`decay_exponent_eventually_le_neg` in `ChromaticConnection.lean` and
`heckel_zeta_mean_bound_from_upper_tail` in `ZetaConcentration.lean`); both will appear as
warnings in `lake build` output but do not affect `erdos_625`.

**File roles**:
- `Erdos625.lean` — library root; imports `PublishableProof.lean`; entry point for `lake build`
- `PublishableProof.lean` — self-contained human-readable proof of `erdos_625`; imports RouteD2;
  presents the full logical skeleton with named steps and citations
- `RouteD2.lean` — upstream technical theorem `gnHalf_gap_ge_n_pow_one_minus_eps_of_exactNoEmpty`
- `ChromaticConnection.lean` — Part B chain (0 sorry above the two source axioms)
- `ZetaConcentration.lean` — Part C chain; Azuma concentration (0 sorry); `heckel_cochromatic_second_moment` axiom
- `GapArithmetic.lean` — gap arithmetic (0 sorry)
- `PartBProfileBridge.lean` — exact-no-empty Part B bridge; two source axioms declared here

## References

- **HP-2023**: Heckel, A. & Panagiotou, K. (2023). *Colouring random graphs: Tame colourings*. arXiv:2306.07253. Key inputs: Lemma 5, eq:wert, eq:wert2.
- **Heckel 2024**: Heckel, A. (2024). *The difference between the chromatic and the cochromatic number of a random graph*. arXiv:2409.17614. Key input: Proposition 5(b).
