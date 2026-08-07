# Phase 2 charter — equisort: the parametric encapsulate arc

Status: RATIFIED at goal-set (user, 2026-08-07). Branch:
`mdd/phase2-equisort` (off main b4d4e7c). Parent plan:
`docs/plans/2026-08-06_capstone-demo-arc.md` (Phase 2); design input:
`docs/notes/2026-08-02_r6-encapsulate-design.md`.

## Goal

Replay the equisort book's 14 red rows — which ARE the abstract
sorting-uniqueness theorem (`STRONG-SSORTFN1-IS-SSORTFN2` /
`WEAK-SORTFN1-IS-SORTFN2` and their supporting rows over the
constrained `sortfn1/sortfn2/ssortfn1/ssortfn2`) — via PARAMETRIC
encapsulate machinery, plus `cov-encapsulate`'s 2 rows. This is the
capstone demo's load-bearing phase: Phase 3 (R7b functional
instantiation) carries these theorems onto the concrete sorts.

## Binding design constraints

- **Constrained fns are WORLD PARAMETERS, never witness bodies** —
  BUG-019 doctrine: `Development.toWorld` excludes `.witnessDefun`
  (explicit arm); the replayed statements must quantify over all
  implementations satisfying the emitted `:CONSTRAINTS`, with witness
  material used for NOTHING but ACL2's own conservativity.
- **L3 world-parametricity** (CLAUDE.md invariant) — statements over an
  arbitrary `w : World` extended by the constrained signature; no
  concrete-world constants inside the fragment.
- **Consume the emitted surfaces built for this**: `encapsulateBegin/
  End` brackets, `(:CONSTRAINTS …)` events, `Development.scopes` (the
  structured scope surface, pinned in Tests/SortingPins), and the
  `:LOCAL-WITNESS` tagging — all landed and inert-until-now.
- All standing rules: replay-vs-infra test, carve-out drift test,
  emitted-data gating, two-tier gates (full claim-gate at phase exit +
  golden re-pins), goldens reviewed row-by-row, size ratchet.

## Exit criterion

`sorting/equisort` 14/14 + `cov-encapsulate` 2/2 replayed with
world-parametric statements (L3 checked), gate TRUE_EXIT=0 — or every
residual row classified against a NAMED frontier with its emission or
design dependency recorded.

## Escape hatch (agent-declarable, any reason; particularly)

Stop and report if: (a) a step needs a user decision, MDD ratification,
or merge/fork sign-off; (b) the honest fix is a NEW emission (batch it,
don't reconstruct); (c) the parametric-statement design demands a
change to the ratified statement-derivation path or trusted core
(TCB-adjacent — always a user decision); (d) signs of churn or
per-case accretion (the drift tests override completion pressure);
(e) soundness or correctness concerns of any kind.
