# Sorting-absolute arc — consolidated audit record (2026-08-02)

The arc (`mdd/sorting-absolute`, opened at main 557c37b, charter
`docs/plans/2026-08-01_sorting-absolute-arc.md`) ran six sub-arc audit
rounds plus a two-reviewer pre-merge audit. The per-round reports lived
in session transcripts only (pre-merge outside audit F14 flagged the
traceability gap); this file is the committed record, reconstructed
from the session. Each round: adversarial Opus reviewer(s), primary
sources, findings tagged VERIFIED/SUSPECTED, independent verification,
fixes applied on the sub-arc branch before fold-back.

## Round inventory

| sub-arc | fix commit | reviewers | verdict | tamper probe |
|---|---|---|---|---|
| exec-gen (1b) | 5a25e9e | 1 Opus | fold-back-with-fixes | registration duplicate guard |
| cross-world (2a) | c3f881d | 1 Opus | fold-back-with-fixes | world-soundness probes |
| linear-verdicts (2b) | 633b342 | 2 Opus | fold-back-with-fixes | max-term dedup (F1 experimentally refuted a wrong claim) |
| dp-premises (2c) | 1afd7a5 | 2 Opus (soundness + mechanism) | both fold-back-with-fixes | equivrefl guard drop → died at Meta.check (fail-loud) |
| bsort-recon (2e) | 8c3f691 | 1 Opus | fold-back-with-fixes | wrong attachment direction → ran GREEN (found the F2 coverage gap; closed by the p8 book) |
| cross-rules (P3) | a7e9469 | 2 Opus (soundness + mirror criterion) | both fold-back-with-fixes | corrupted cross-rule content → hypothesis returned to the type (fail-closed, channel live) |

## Highest-value findings per round (the ones that changed code)

- **dp-premises**: soundness F1 — the rule-content premise pass was
  gated on shape only; fixed with the tau Signature Form 1 gate
  (`tauSigForm1`), leaf-class gating left as an open ratification
  sub-question (now covered by the 2026-08-02 carve-out ratification +
  drift test). Mechanism F1 — the `trueListp` bridge is a growing
  rewrite; the suggested shrinking reorientation proved UNBUILDABLE
  (the leaf simp set's own `cdr` unfold destroys the pattern — caught
  by the focused run), so the hazard is documented and the split path
  heartbeat-bounded instead. Mechanism F3/F4 — the substN scaffold's
  three inline copies extracted to `mkSubstNBridge` with uniform
  σ-pinning.
- **bsort-recon**: the attachment-direction tamper ran the whole suite
  green — zero coverage for the new recon semantics; closed by
  `p8-clausify-detail` (synthetic book through real ACL2, pinned at the
  never-ignore frontier). F5 — two never-ignore bypasses closed
  (`bridgeClausifyMulti` negExpands hard-fail; `isNoopClausify`
  detail-emptiness, REFINED after the blanket variant regressed 34
  rows). F10 — BSORT-IS-ISORT re-diagnosed as R7-gated, not
  recon-gated.
- **cross-rules**: criterion F1 — the golden flipped between
  elaborations (2-2-3 conds over 3 forced runs); root-caused to dep
  re-replays racing the per-theorem heartbeat budget over the
  O(corpus) telescope; fixed with per-discharge budget windows.
  Soundness F3 — `combineRules` order inverted vs the reverse
  discharge pass's topological premise; fixed (cross entries first).
  Both capstone drivers added to the build-failing axiom gate.
  The mirror-criterion reviewer REFUTED the PERM/`List.isPerm`
  duplicate-semantics divergence question (same first-occurrence-erase
  algorithm, `permExec_enc` kernel-checked) and verified the replayed
  statement is load-bearing (no ornamental import, no content
  smuggling in the decode lemmas).

## Increments NOT separately audited (pre-merge outside audit F15)

1a (shared channel builder, 5e01361), 1c (298492a), 1d (89e64ea),
the LEN measure machinery (007fca7), `dischargeEquivReflHyp` (76cecfd).
Each landed with focused verification (build + sweep diff review) but
no adversarial round of its own; the pre-merge integration-seams
reviewer's scope covered the LEN/equivrefl surfaces after the fact.

## Pre-merge audit (2026-08-02)

Two Opus reviewers on the un-reviewed surface:
- OUTSIDE (charter conformance + record honesty): verdict
  MERGE-WITH-FIXES, all fixes record-only. Key corrections adopted:
  the close-out's "everything remaining is ratification-gated" framing
  replaced with plain numbers (see TODO); R6 is unbuilt design work,
  not ratification-gated; three native-worthy convert-perm mirrors
  carried as explicit debt; pins made zero progress this arc; the
  `derive_exec%` hand-transcription caveat surfaced in TODO. Credits:
  all sampled sweep-header/commit claims reproduced; 9/9 sampled audit
  fixes present in code; the capstone verified non-ornamental.
- INTEGRATION-SEAMS (fresh ground truth + cross-sub-arc seams):
  verdict MERGE-WITH-FIXES, all fixes cheap records (applied). Ground
  truth: full `just ci` green (all 12 gates); the axiom gate
  mechanically complete (40/40 natives); TamperTests live (4 tampers
  rejecting — scoped to perm-transitive only, arc additions untested:
  next-arc item); GOLDEN DETERMINISTIC across two forced
  re-elaborations (sha256-identical to the committed golden — the
  per-discharge budget fix held). Seams: the capstone equivrefl path
  verified LIVE and fail-closed both directions (deps present →
  discharged, absent → kept cond, byte-identical to golden); the
  cross-book offers stated at the CONSUMER's world (the honesty
  argument survives the widening); registry misses rethrow loudly
  (no silent keep); heartbeat nesting semantics verified (outer bound
  still counts discharge work; ≥6× measured headroom; three
  tryCatchRuntimeEx sites degrade resource trips to weaker HONEST
  results — reproducibility note, not soundness). Findings adopted:
  the corpus-order/include-graph mismatch + recon-test contamination
  recorded at the corpus site (reorder rides the provenance gate);
  the dp-premise pass's post-audit O(corpus) input noted in its
  design record; the SortingPins crossRules asymmetry documented;
  termination-row counting noted.

## Standing constraints from the arc's ratifications (MDD 2026-08-02)

R7 option (a)/(a1); the carve-out drift test ("per-case custom proofs
or checkers = no longer mirroring ACL2 — custom search replacing it");
BUG-027 narrow-via-emission; BNEXT-SIZE via admission-waterfall replay;
count rows measure-absorbed (`.replayedOnly`).
