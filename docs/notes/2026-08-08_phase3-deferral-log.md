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
