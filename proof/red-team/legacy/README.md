# Legacy red-team artefacts

These red-team passes (2026-05-10) audited the **legacy** `erdos_625`
formalization (95% n coverage, `InMainRange` hypothesis), before the
flagship was upgraded to `erdos_625_full_clean` (100% n, 4 paper
axioms instead of 3).

They are retained for historical record but **do not describe the
current state** of the package. For the audits of the current
flagship `erdos_625_full_clean`, see the files one directory up
(`proof/red-team/red-team-erdos-625-full-2026-05-11.md` and the
five passes that followed).

---

## Provenance

- **Generated**: 2026-05-11 / 2026-05-12 development window.
- **Worker model**: `claude-opus-4-7[1m]` (Claude Opus 4.7, 1M-context variant).
- **Operator orchestrator**: `operator` (https://github.com/uthunderbird/vibechord); codex-brain adapter ran `gpt-5.3-codex-spark` at `effort=low`.
- **Same-model caveat**: this artefact was produced by the same LLM-agent pipeline that produced the proof being critiqued; it is an **internal adversarial audit**, not a third-party review. LLM-generated proofs may exhibit plausibility-driven failure modes that survive same-model critique because the proof author and the critic share training-data blind spots. See `../../README.md` Provenance and `../../DEVELOPMENT.md` ADR-10 / ADR-11 / ADR-12 for the full methodology disclosure. External verification by an unrelated reader, a different model, or a human mathematician is encouraged.
- **Footer added**: round-2 publish-readiness repair, 2026-05-12 (P1-7).
