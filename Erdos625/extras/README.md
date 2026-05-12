# Extras

This directory is currently empty. It is reserved for supplementary
Lean files related to the formalization of Erdős Problem 625 that are
**not** on the proof path of any of the four publishable theorems
(`erdos_625`, `erdos_625_97`, `erdos_625_full`, `erdos_625_full_clean`)
but may be of interest to readers reproducing or extending the work.

No files are currently shipped here. Candidates for future inclusion:

- `SharpProfileBound.lean` — a Cauchy–Schwarz approach to discharging
  `paperPartBThresholdAverageClassAsymptoticLowerCriterionTarget_source`
  (axiom #1 of the legacy `erdos_625` chain, HP-2023 Lemma 5). This was
  developed during the formalization but is not used in the final
  proof. It is a proof-engineering artefact showing how that axiom
  might be discharged in future work; not required for any current
  theorem.
- A Lean encoding of the `lemma_7_10_ext` numerical certificate (see
  `../../proof/red-team/lemma-7-10-ext-disclosure-2026-05-11.md` and
  `../../ROADMAP.md` §N2) — would discharge the hybrid status of
  axiom A1.

Until one of these lands, this directory is intentionally empty.
