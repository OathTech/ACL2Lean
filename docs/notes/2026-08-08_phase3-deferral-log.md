# Phase 3 deferral log (running, append-only)

The binding mechanism of the Phase 3 charter
(`docs/plans/2026-08-08_phase3-r7b-charter.md`): any item whose honest
resolution needs a user decision, a fork-emission change, a TCB /
statement-derivation change, a ratified-boundary amendment, or a
merge/push is DEFERRED here — a dated entry (what / why deferred /
what it would unblock) COVERS the item. A deferral is a success
outcome, equal in standing to a green row.

Format:

    ## D<N> — <short title> (YYYY-MM-DD)
    - What: …
    - Why deferred: <the decision/change it needs, and whose it is>
    - Unblocks: <rows/items that become addressable once resolved>

---

## D1 — full non-vacuity of the capstone telescopes (2026-08-08)

- What: `weak/strongSsortfn1IsSsortfn2AtCanonical` landed as PARTIAL
  witnesses — every no-shadow/totality/TP premise kernel-discharged
  (41/49 weak, 13/21 strong; PCE totality via `dis_pce_total`,
  HOW-MANY's TP via `dis_how_many_tp` through the new generic `totals`
  registered-discharger route); the 6 constraint `rule:` premises +
  `rule:CONVERT-PERM-TO-HOW-MANY` + `use:ORDERED-PERMS` remain KEPT
  hypotheses.
- Why deferred (the residual's chain): (i) the constraint rows' own
  conds are witness TPs (`tp:SORTFN1-INSERT` class) that `proveTp`
  frontiers on (return-path CONS) — ADDRESSABLE in-scope by `dis_*`
  hand lemmas (queued as item 1b, NOT a user decision); (ii)
  `rule:CONVERT-PERM-TO-HOW-MANY`'s chain runs through
  PCE-IS-COUNTEREXAMPLE's recognizer frontier (machinery/emission
  class) and PERM-TLFIX's rung-3 R-lane build — the R-lane is a
  PRE-RATIFIED USER CHECKPOINT (equiv-lane design), so that leg is
  deferred to Mike regardless of other progress.
- Unblocks: unconditional AtCanonical constants (the full O6 closure);
  also narrows the sorts-equivalent capstones' eventual cond sets.

## D2 — item 2 residual: the usefi discharge's in-sweep enablement (2026-08-08, EARLY-EXIT residual)

- What: the R7b usefi: discharge composition is COMPLETE and COMMITTED
  (the full semantic layer A/B′/B″/lifts/transports — all kernel-checked,
  zero sorries — plus `mkUseFiDischarger` with both premise-bridging
  classes, wired through runBook and the coverage harness) but DISABLED:
  in-sweep runs SIGABRT on proof-term depth. Three remediations landed
  (kernel-route decides — fixed the first crash class; the D1-pattern
  constant declaration with consumer-fvar abstraction; hint-only gates
  with constructed types) without clearing the in-sweep crash. The
  isolation probe (.tmp/pinscratch/usefi_probe.lean) runs the whole
  composition up to the consumer-discharge step (which needs the real
  sweep telescope).
- Why residual: NOT decision-blocked — an in-scope debugging campaign
  (symbolized stack traces, bisecting which Expr walk overflows,
  possibly chunking the parametric rebuild into its own pre-declared
  constant) that this session could no longer execute reliably
  (three consecutive fix cycles at ~10 min build each without landing).
- Unblocks: MSORT-IS-ISORT/QSORT-IS-ISORT usefi: conds flip to
  discharged (queue items 3/4's full closure).

## D3 — item 5: BSORT-IS-ISORT's useHint+clausify composition (2026-08-08, EARLY-EXIT residual)

- What: the composition (constraint chain on CONSTRAINT-CL, clausify
  the residual, tau leaf, FI hypothesis peel) in Core's clausify
  branch — sized in TODO with its emission read-out.
- Why residual: in-scope engineering, ceiling ASSUMED ◌ regardless
  until the bsort book's Phase-1 frontier family lands (that leg IS
  emission-adjacent — partially deferral class (b)).
- Unblocks: BSORT-IS-ISORT from FAIL to ◌ (never ✓ without the bsort
  frontiers).

## D4 — item 6: touched-if-relevant Phase 2 audit deferrals (2026-08-08, EARLY-EXIT residual)

- What: gz agreement-lemma ci check; scope-in-force refinement.
- Why residual: untouched — the phase's work never reached them
  (charter: "cover or defer IF touched"; they were not touched).
- Unblocks: hardening only; nothing gates on them.

