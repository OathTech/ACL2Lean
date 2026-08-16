# R-arcs roadmap — audit synthesis + rulings (2026-08-13)

Synthesis of the three 2026-08-13 audits (persisted verbatim in
`docs/audits/2026-08-13_overspecialization-audit.md`,
`…_fork-emission-audit.md`, `…_documentation-audit.md`), ruled by Mike
2026-08-13. Basis: main @ 4a600c8 (Basics close-out merged; three
mirrors trio-clean; sorries 6). Subordinate to the master plan
(`docs/plans/2026-08-12_master-plan.md`) — this sequences its Phase
A4/C work plus the audit remediation.

> **STATUS (added 2026-08-16 by the post-audit repair batch, A3-T2-1).**
> R0/R1/R2/R3 are DONE and R4 is through wave 1; **R5 is the only arc
> not started**. The basis line above ("sorries 6") is the 2026-08-13
> basis and is now historical — the repository has been at **zero
> `sorry`/`sorryAx`** since 2026-08-15. Per-arc statuses inline below.

## The five rulings (Mike, 2026-08-13 — verbatim where quoted)

1. **Ladder/transport widening (F2/F4) — widening is fine.** "This
   doesn't seem important for trust, the trust is inherited from the
   kernel. There's a *design quality* objective which is to replay
   ACL2 proofs. The cheating that's possible here is that we
   accidentally prove something using Lean rather than ACL2. That's
   annoying but not a catastrophic failure. So widening seems fine."
   Consequence: the closed rung ladder is a design-quality speedbump
   (deterrent standard), not a trust gate — widen it (core-logic rung
   class, Iff rungs, transport instance threading) as normal
   engineering, expectations-level discipline, no admission ceremony.
2. **GAP-2 design: D-A** (recognizer-tuples + ts-algebra — reflect
   ACL2's own type-set reasoning): "yes, we should reflect ACL2 when
   we can do so." (D-B, a Lean-side re-derivation, is rejected.)
3. **Verdict-only discharge: absolutely forbidden.** "The only root of
   trust that's allowed is the lean kernel. Trusting ACL2 is
   absolutely forbidden in all circumstances no exceptions (and if any
   cases have crept in via other 'rulings', those are BUGS and you
   should highlight them immediately)." Creep scan run same day:
   CLEAN — no case found where a verdict substitutes for a kernel
   proof (DP carve-out: omega proves the obligations; D5/gz: proven
   lemmas; `:LEAVES`/ts-masks: admissibility routing only). The one
   boundary object: FORBIDDEN-DEBT sorries — visible assumptions,
   sanctioned buildout-only; **the win state is ZERO sorryAx anywhere**
   (Mike, same day).
4. **Governing plan = the master plan.** `2026-06-10_generality-design.md`
   is relabeled ARCHITECTURE REFERENCE (L1–L3 invariants binding;
   status/sequencing superseded).
5. **TODO restructure approved** (live backlog + archived log split;
   executed in R5).

## Arc sequence

- **R0 — records & hour-scale fixes** — **DONE** (2026-08-13,
  `mdd/r0-records` @ f6627a3; full claim-gate TRUE_EXIT=0, artifact
  `.gate-runs/f6627a3-20260813T220936Z.log`; F19 landed golden
  byte-unchanged; two audit findings refuted in execution — see the
  corrections appendix on the documentation audit).
  Tier-1 doc fixes (AGENTS.md rewrite — it authorized `sorry`; the
  14→13 Props count ×5; README product layer + status pointers;
  CLAUDE.md dead refs + the verdict/sorryAx fidelity line + the
  vocabulary practice; governing-plan relabels; rollback/closure
  markers), stale-label fixes (G5/rev rows are GREEN unconditional —
  labels were ~2 months stale; TODO's refuted ACL2-COUNT diagnosis),
  and three code fixes: F19 (`endpDualOf` missing ATOM leg — live
  clone-divergence bug, Totality.lean), F5 (false frontier messages in
  `mirror_iso%`/`mirror_transport%`), F17 (Lifting.lean promotion
  header overclaims consumers).
- **R1 — Basics 6/6 + generator widening** — **DONE** (2026-08-14,
  R1 final exit A–E at `15b016d`; full claim-gate TRUE_EXIT=0 on
  `a85edd2`). The rev/appNil decode kit
  (rows already green unconditional; mirror-side lift only) → three
  more mirrors (app_nil, rev_app, rev_rev). F1: `mirror_iso%`
  per-argument readings (port SimGen's raw/list table up — blocks
  `insertOrd` today). F3: transport typeclass threading + the
  `TotalOrder SExpr`-restriction instance route.
- **R2 — the fork round-trip** — **DONE** (2026-08-14, `e5d3fa1`;
  submodule @ `f86e56698f`, recapture 91/91). (One batch, commit-fork →
  build → recapture-all.) GAP-1 context-refined `:LEAVES` (prototype WORKS
  in-image: ~15 lines mirroring `type-set-rec`, acl2/defuns.lisp:12022
  + ld.lisp:5668 caller); GAP-2 per-leaf subterm verdicts (same
  collector; primitives store no TPs); item 3 `:ALL-TPS` (ACL2 stores
  the strong TRUE-LISTP-APPEND rule at axioms.lisp:3326; the fork
  discards it at ld.lisp:5601); parser at ProofLog.lean:1134.
  Consumers unblocked by ruling 2 (D-A ts-algebra).
- **R3 — unified measure/arity table** — **DONE** (2026-08-15, landed
  as T1+2 sprint phase 2, `b3f6174`). (F6+F7+F8 + ExecGen M2
  unification) = the master plan's B2; retired the REQUIRED-debt
  measure gate. (The "blocks 100% of `total:` debt today" reading is
  historical: `total:` row conditions are now **0**.)
- **R4 — sorting mirrors** (the 13 Props of `Mirrors/Sorting.lean`):
  order kit + widened ladder (ruling 1) + waves. **Wave 0 DONE**
  (`fc06b33`), **wave 1 DONE** (`42d4d29`, 8 live squares); **wave 2
  OPEN** — the rulings batch (W7/W9/enum registry/OrderedEmbed
  review), squares en masse, the first sorting transports, the
  meta-theorems. The old driver-side blocker — QSORT's non-liftable
  measured self-call arm (recorded here as `Provers.lean:847-848`, a
  dead ref since the P5b split; the arm now lives in
  `Replay/Driver/TpProver.lean`) — is **CLOSED**: P5b's opaque
  measured-actual route reads the decrease off QSORT's own replayed
  admission.
- **R5 — release normalization** — **OPEN** (the one genuinely
  unstarted arc): TODO restructure (ruling 5), `docs/STATUS.md`, the
  docs index, CLAUDE.md status rewrite, the ARC LOG convention.

Standing side items (scout-first, not yet slotted): the relieve-hyp
gap (own scout before batching). ~~the remaining six FORBIDDEN-DEBT
sorries~~ — **retired: the count is ZERO as of 2026-08-15** (P1/R3/
P3b/P3c; see `TODO.md`'s debt registry header).

## Escape hatch (goal-design rule)

Any R-arc stops and reports early when its remaining work all gates on
a user ruling, a fork round-trip it cannot run, or a ratified design
boundary — grinding on touchable-but-out-of-scope work is the named
failure mode.

## Sequence refinement (2026-08-14, post-R1 — the sorting-book quest)

Mike: the aim is closing out the sorting book, no qualifications;
Tier 1 (+ the Tier-2 debt, which IS the qualifications) is home.
Structural facts driving the order: SQUARES are replay-independent;
TRANSPORTS inherit row qualifications (never lift a conditional row);
G1 is the only frontier both novel and critical-path (convert-perm →
equisort → the last 5 Props).

Wave 0 (running) → **R2** fork batch (longest latency first; fold in
the recognizer-under-IF trio + CLASSIFY-POS for one recapture) with
the **G1 design scout in parallel** (read-only de-risking; ruling
before R2 exits) → **R3** measure table (corpus unconditional except
convert-perm chain) → **R4 wave 1** squares en masse + first
transports (order-embedding ruling — the R1-C restriction lemma is
intEmbed's witness — + instance threading vs the first real
transport; exit: first sorting mirrors) → **G1 implementation** (the
perm lane; retires dis_convert_perm) → **R4 wave 2** qsort (+ the
driver self-call arm), bsort, then the meta-theorems needing G1
(exit: 13/13) → **R5** close-out (pre-approved exit audit, STATUS,
the scaffolding-decay story). Estimate at current velocity: ~7-8
days; G1 is the variance driver.
