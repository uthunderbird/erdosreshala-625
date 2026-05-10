# Erdős Problem 625 — Lean 4 Formalization

**Theorem**: In G(n, 1/2), for every 0 < ε < 0.001, there exists n₀ such that for all n ≥ n₀
in the main-range regime, with probability at least 1 − 2ε,

$$\chi(G) - \zeta(G) \ge n^{1-\varepsilon}$$

where χ(G) is the chromatic number and ζ(G) is the cochromatic number.

**Proof status**: Complete. **3 paper-backed axioms, 0 sorry.**
Full mathematical argument: [`proof/proof.md`](proof/proof.md).

## Axiom Inventory

| Axiom | File | Paper source |
|-------|------|--------------|
| `paperPartBThresholdAverageClassAsymptoticLowerCriterionTarget_source` | `Erdos625/PartBProfileBridge.lean` | Heckel & Panagiotou (2023) [arXiv:2306.07253](https://arxiv.org/abs/2306.07253), Lemma 5 / eq:wert |
| `paperPartBExactNoEmptyDenomBinaryLowerControlledLhsDecayTarget_source` | `Erdos625/PartBProfileBridge.lean` | Heckel & Panagiotou (2023) [arXiv:2306.07253](https://arxiv.org/abs/2306.07253), eq:wert2 |
| `heckel_cochromatic_second_moment` | `Erdos625/ZetaConcentration.lean` | Heckel (2024) [arXiv:2409.17614](https://arxiv.org/abs/2409.17614), Proposition 5(b) |

Running `#print axioms Problem625.Publishable.erdos_625` produces exactly **6 entries**: the
3 paper axioms above plus Lean's standard axioms `propext`, `Classical.choice`, `Quot.sound`.

## Building and Verifying

**Prerequisites**: Lean 4 / Lake (`leanprover/lean4:v4.29.0-rc8`). Internet access for first
build (downloads ~4 GB Mathlib olean cache).

```bash
git clone https://github.com/[user]/erdos-625-formalization
cd erdos-625-formalization
lake exe cache get    # download prebuilt Mathlib oleans (essential; ~5 min)
lake build            # build the formalization (~5 min with cache)
```

**Verify axiom count** (in any Lean file importing this library):
```lean
import Erdos625.PublishableProof
#print axioms Problem625.Publishable.erdos_625
-- Expected: 6 lines (3 paper axioms + propext + Classical.choice + Quot.sound)
```

## Repository Structure

- [`proof/proof.md`](proof/proof.md) — standalone mathematical proof document (148 lines)
- [`Erdos625/`](Erdos625/) — Lean 4 source; see [`Erdos625/README.md`](Erdos625/README.md) for a guided tour
- [`paper/SOURCES.md`](paper/SOURCES.md) — precise citations for the 3 paper axioms
- [`DEVELOPMENT.md`](DEVELOPMENT.md) — architectural decision records

## References

- Heckel, A. & Panagiotou, K. (2023). *Colouring random graphs: Tame colourings*. [arXiv:2306.07253](https://arxiv.org/abs/2306.07253)
- Heckel, A. (2024). *The difference between the chromatic and the cochromatic number of a random graph*. [arXiv:2409.17614](https://arxiv.org/abs/2409.17614)

## License

Apache 2.0 (compatible with the Lean/Mathlib ecosystem).
