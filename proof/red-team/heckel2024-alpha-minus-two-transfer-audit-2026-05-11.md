# Heckel 2024 Prop 5(b) — (α−2)-Adaptation Transfer Audit

**Date**: 2026-05-11
**Purpose**: close red-team finding P1-B from `red-team-erdos-625-full-2026-05-11.md`
**Status**: transfer verified at proof-structure level; in-repository, not submitted for peer review
**Target axiom**: `Problem625.zeta_alphaMinusTwo_upper_bound_whp` in
`Erdosreshala/Problem625/CrossingPartB.lean`

## What Heckel 2024 literally states

Heckel 2024 (arXiv:2409.17614) Proposition main (= our "Prop 5(b)") is
stated and proved for the **(α−1)-bounded** case only. Two explicit
restrictions in the paper:

- §3 (Theorem statement / structure), line 341:
  > "We will consider (α−1)-bounded profiles for most of the paper."
- §5.1 (Tame profile definition), line 529:
  > "We restrict the definition [of tame profile] to (α−1)-bounded profiles
  > here, as this is all that we need in this paper."

So Heckel 2024 does **not** prove the (α−2)-version of Prop 5(b) directly.

## Why the transfer to α−2 nevertheless works

The proof of Heckel 2024 Prop 5(b) is **not specific to α−1**; it is a
black-box application of HP-2023 second-moment lemmas to the cochromatic
profile, plus a Paley-Zygmund step. Three pieces of evidence:

### 1. Heckel 2024 §5 itself states the transfer is a black-box import from HP-2023

Line 502 (Heckel 2024):
> "We will use the techniques developed in [heckel2023colouring] to bound
> the second moment, translating the results via the following
> correspondence."

The correspondence in question (Prop:probabilities, eq:firstmomentcocol,
eq:Zfirstmomentold) transforms a-bounded chromatic profiles to a-bounded
cochromatic profiles without any restriction to a = α−1.

### 2. The three second-moment lemmas (HP-2023 6.3/6.4/6.5) hold for general a-bounded profiles

Heckel 2024 §5.4 (line 731):
> "Using this, Proposition prop:probabilities and eq:firstmomentcocol,
> eq:Zfirstmomentold, eq:Zfirstmoment, we can directly transfer
> Lemmas lemmascrambled and lemmamiddle to our setting."

These transfers are at the level of **general a-bounded profile**; the
α−1 restriction enters only at the application step where Heckel 2024
picks the specific k*-profile.

### 3. The only μ-condition in Heckel 2024 §6 (the application step) is on μ_α

Heckel 2024 line 824:
> "Now set Z = Z_{k*}^co. By the above, and since we assumed μ_α ≥
> n^{0.05+ε}, we may apply the three second moment lemmas
> (Lemmas lemmascrambledco–lemmasimilarco) ..."

For the (α−2)-adaptation, the corresponding condition is on μ_{α−2}, and
the relevant inequality is `μ_{α−2} ≥ n^{1.05}` — this is the
level-shift of Heckel~2024's `n^{0.05+ε}` tameness condition at α−1
(Lemma 7.20 condition (d) lifted from α−1 to α−2), and it is the
*binding* lower bound for the (α−2) transfer. It is distinct from, and
strictly weaker than, the HP-2023 §8 *application range*
`[n^{1.1}, n^{2.9}]` under which Lemma 8.1 itself is stated; both
thresholds are cleared with substantial headroom by the structural
margin (see below). This is satisfied for every
deep-crossing n by the standing inequality from HP-2023 eq:mualpha-2:

  μ_{α−2} = Θ(n² / log²n · μ_α).

In the deep crossing μ_α ↘ 1 ⇒ μ_{α−2} ≥ Θ(n² / log²n) ≈ n^{1.6} for
n ≥ 100. Numerically confirmed in
`r2b-step1-results-2026-05-11.md`: min margin (x_{α−2} − 1.05) = 0.483
over n ∈ [100, 10⁶], slope 1.68–1.80 at n ∈ {10⁷, …, 10¹²}.

### 4. HP-2023 §8 itself uses this exact transfer pattern at both α−1 and α−2

HP-2023 (TameColourings.tex) line 2579, Lemma 8.1:
> "Let p=1/2, and a=a(n) ∈ {α(n)−2, α(n)−1}. Then, whp,
> χ_a(G_{n,1/2}) ≥ k_a − 1."

That is, **HP-2023 itself uses the first-moment lemma at both levels**,
and the proof (line 2588) calls the same supporting lemmas
(`lemma:onemorecolour`, `lemma:averagecolourclass`,
`lemma:improvedapproximation`) at both α−1 and α−2. So the (α−2)
chromatic-side step is **already** literally in print at the chromatic
level. The cochromatic-side step at α−2 is the symmetric ζ-version,
established via the same Prop:probabilities correspondence (line 522
"we want to apply the second moment method to a k* which is smaller than
the typical value of the chromatic number") that Heckel 2024 uses to
lift the chromatic side to the cochromatic side, but now applied at α−2
instead of α−1.

## What the transfer does NOT prove

- It does not give an **explicit citation** in any peer-reviewed paper of
  the literal statement "Heckel 2024 Prop 5(b) holds at (α−2)-bounded
  level". The closest published facts are:
  - HP-2023 Lemma 8.1 at level α−2 (chromatic side, literal).
  - Heckel 2024 Prop 5(b) at level α−1 (cochromatic side, literal).
  - The proof technique transfers either side ↔ α−2 ↔ α−1 ↔ either side.
- The (α−2)-bounded cochromatic profile k* must be specified
  analogously to Heckel 2024 line 463
  (k* = k_{α−1} − n^{1−ε/2}); the corresponding (α−2)-version is
  k*_{α−2} = k_{α−2} − n^{1−ε/2}. This is not a free parameter — its
  existence with the required tameness is exactly what the
  (α−2)-adaptation of Heckel 2024 Lemma 5.6 (`lemma:kstartame`) would
  prove.

## Verdict for red-team P1-B

**Bounded concern** (per red-team typing). The axiom
`zeta_alphaMinusTwo_upper_bound_whp` is:
- mathematically a natural symmetric extrapolation of a published result;
- proof-technique-wise a black-box application of HP-2023
  second-moment machinery, which is itself stated for general a-bounded
  profiles;
- numerically vindicated by R2B Step 1 (μ_{α−2} ≫ n^{1.05} for all
  crossing n);
- structurally analogous to HP-2023 Lemma 8.1 at α−2, which IS literally
  in print.

It is **not** a literal one-citation paper-backed axiom.

## Honest disclosure for any preprint

> The proof of `erdos_625_full` invokes a paper-backed axiom
> `zeta_alphaMinusTwo_upper_bound_whp` adapting Heckel 2024 Proposition
> main (a.k.a. "Prop 5(b)") from the (α−1)-bounded cochromatic case
> (literally proved in Heckel 2024 §6) to the (α−2)-bounded cochromatic
> case (not literally proved in any peer-reviewed paper). The transfer
> uses (i) HP-2023's second-moment lemmas which are stated for general
> a-bounded profiles, (ii) Heckel 2024's chromatic-to-cochromatic
> correspondence (Prop:probabilities), and (iii) the standing deep-crossing
> inequality μ_{α−2} ≫ n^{1.05} which holds for every crossing n
> (numerically verified for n ∈ [100, 10⁶], asymptotically by HP-2023
> eq:mualpha-2). The pattern is structurally analogous to HP-2023 Lemma
> 8.1 applied at α−2 on the chromatic side (which IS literally proved).
> Formal peer review of the (α−2)-version is open work.

## Optional follow-up (NOT done in this audit)

- Email Heckel/Panagiotou for explicit confirmation that Heckel 2024
  §6–7 proof structure transfers verbatim to α−2.
- Write the (α−2)-version of Heckel 2024 Lemma 5.6 (`kstartame`) as a
  standalone preprint section.
- Either of these would upgrade P1-B from "bounded concern" to "closed".

---

## Provenance

- **Generated**: 2026-05-11 / 2026-05-12 development window.
- **Worker model**: `claude-opus-4-7[1m]` (Claude Opus 4.7, 1M-context variant).
- **Operator orchestrator**: `operator` (https://github.com/uthunderbird/vibechord); codex-brain adapter ran `gpt-5.3-codex-spark` at `effort=low`.
- **Same-model caveat**: this artefact was produced by the same LLM-agent pipeline that produced the proof being critiqued; it is an **internal adversarial audit**, not a third-party review. LLM-generated proofs may exhibit plausibility-driven failure modes that survive same-model critique because the proof author and the critic share training-data blind spots. See `../../README.md` Provenance and `../../DEVELOPMENT.md` ADR-10 / ADR-11 / ADR-12 for the full methodology disclosure. External verification by an unrelated reader, a different model, or a human mathematician is encouraged.
- **Footer added**: round-2 publish-readiness repair, 2026-05-12 (P1-7).
