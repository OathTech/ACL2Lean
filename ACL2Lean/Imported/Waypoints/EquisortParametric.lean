import ACL2Lean.Imported.Waypoints.Macro
import ACL2Lean.Imported.Waypoints.PermBook
import ACL2Lean.Imported.Waypoints.ConvertPerm
import ACL2Lean.Imported.Waypoints.OrderedPerms
import ACL2Lean.DevLoad
import ACL2Lean.Imported.EquisortWitness

namespace ACL2.Imported.Waypoints

open ACL2 ACL2.Replay ACL2.Replay.Driver Lean Lean.Meta Lean.Elab

/-! ## The equisort capstones — PARAMETRIC constants (Phase 2 item c)

The two abstract-uniqueness theorems (`WEAK-SORTFN1-IS-SORTFN2`,
`STRONG-SSORTFN1-IS-SSORTFN2`) are proved by ACL2 in the CONSTRAINED
theory — the encapsulate's witnesses were local and gone.  Their
first-class artifact is therefore the L3 world-parametric form (the R6
catalog doctrine, `docs/notes/2026-08-02_r6-encapsulate-design.md`): the
SAME recorded trees replayed over an ABSTRACT `w : World`, with the
signature fns (`SORTFN1`/`SORTFN2`, `SSORTFN1`/`SSORTFN2`) unpinned and
the scope's constraint theorems as explicit premises.  A witness body
appearing anywhere in these statements would be the banned masquerade
(the waypoint criterion); an unfold demand on a sig fn inside the replay
hard-fails (the witness-dereference guard).  Phase 3 (R7b) instantiates
these constants at concrete worlds. -/

private def equisortLog : String :=
  include_str "../../../acl2_samples/sorting/equisort.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def equisortDev : Development :=
  load_development% equisortLog

set_option maxHeartbeats 3200000 in
/-- WEAK: `∀ env w`, given the kept premise telescope — 34 builtin
    no-shadow facts, totality of the pre-scope fns and of
    `SORTFN1`/`SORTFN2`, `tp:HOW-MANY`, the six scope-1 constraints in
    STORED-RULE form (e.g. `(EQUAL (ORDEREDP (SORTFN1 X)) 'T)` — see
    `parametric_replayed%`'s doc for why that is stronger than the bare
    constraint over an abstract w), `rule:CONVERT-PERM-TO-HOW-MANY`, and
    `use:ORDERED-PERMS` — then
    `EvTrue w env (IMPLIES (TRUE-LISTP X) (EQUAL (SORTFN1 X) (SORTFN2 X)))`.
    NOTHING is definition-pinned (the tree never unfolds a defun) and no
    witness vocabulary appears (pinned by Tests/ParametricPins.lean).
    NON-VACUITY (kernel-checked satisfiability of the telescope) is the
    Phase 3 (R7b) instantiation at a concrete world — deliberately NOT
    claimed here (audit 2026-08-08 outside F6). -/
def weakSortfn1IsSortfn2Parametric := parametric_replayed% equisortDev
  "weak-sortfn1-is-sortfn2" deps [permDev, convertPermDev, orderedPermsDev]

set_option maxHeartbeats 3200000 in
/-- STRONG: the unconditional variant over the strongly-constrained scope
    — same telescope shape (4 no-shadows, sig totality, the six scope-2
    constraints in stored-rule form, `use:ORDERED-PERMS`), conclusion
    `EvTrue w env (EQUAL (SSORTFN1 X) (SSORTFN2 X))`. Same non-vacuity
    deferral as WEAK. -/
def strongSsortfn1IsSsortfn2Parametric := parametric_replayed% equisortDev
  "strong-ssortfn1-is-ssortfn2" deps [permDev, convertPermDev, orderedPermsDev]

/-! ## The canonical-world instantiations (Phase 3 queue item 1 — the
non-vacuity witnesses; FULLY BACKED as of 2026-08-13)

Applying each parametric constant at the equisort canonical world with
all but TWO premises discharged kernel-checked: the no-shadows by
decide, the totality/TP premises by the admission-justification provers
+ the registered witness kits, and ALL SIX constraint `rule:` premises
per constant by re-replaying their recorded pass-1 trees (the R6
conservativity content). KEPT (honest hypotheses of the declared
constants — full telescope satisfiability is therefore NOT yet
established): `hrule_CONVERT-PERM-TO-HOW-MANY` (the PCE-chain/R-lane
deferral) and `husethm_ORDERED-PERMS` (its dep tree's tau dp-facts) —
see the deferral log's D1 close-out update. This remains the first
exercise of the R7b "apply at a model" move the sorts-equivalent
capstones need.

MILESTONE (2026-08-13, the TP-replay arc's ATOM-leg increment): both
witnesses are now FULLY BACKED — every discharged premise arrives by
replay, with NO sorry-backed discharger anywhere underneath. The
`totals [ACL2.Worlds.Sorting.dis_pce_total]` clauses are GONE (the
clause is optional, and its list is now empty): `dis_pce_total` was the
last FORBIDDEN-DEBT discharger these constants consumed, and it was
deleted when the ATOM leg let PCE's admission replay. The two KEPT
hypotheses above are unchanged — they are honest premises of the
declared constants, not debt. -/

derive_world equisortWaypointsWorld from equisortDev

set_option maxHeartbeats 12000000 in
/-- WEAK at the canonical world — every premise discharged except the
    two KEPT hypotheses named in the section header. -/
def weakSortfn1IsSortfn2AtCanonical := instantiate_parametric%
  weakSortfn1IsSortfn2Parametric equisortDev equisortWaypointsWorld
  "weak-sortfn1-is-sortfn2" deps [permDev, convertPermDev, orderedPermsDev]

/-! The AtCanonical witnesses are TRIO-CLEAN as of 2026-08-13 — the
non-vacuity witnesses these constants carry are now FULLY BACKED by
replay, with no FORBIDDEN-DEBT anywhere underneath.

THE ROUTE HERE (the record of how the debt drained, one shape per
increment — every one of them a DELETION plus a replay route, never a
Lean re-proof): the pair was SORRY-BACKED from the thin-Lean purge
(2026-08-11, audit fix F1), when its `totals [...]` dischargers were
FORBIDDEN-DEBT sorries. TP-replay arc increment 1 (2026-08-12) removed
`dis_how_many_tp` (`tp:HOW-MANY` by the BINARY-+ return path);
increment 2 removed `dis_sortfn1_insert_tp` / `dis_ssortfn1_insert_tp`
(the CONS return-path shape); increment 3 (2026-08-13) removed
`dis_sortfn1_tp` / `dis_ssortfn1_tp` (the CALLEE-TP shape), leaving
exactly one — `dis_pce_total`, PERM-COUNTER-EXAMPLE's admission
totality. The ATOM-leg increment (2026-08-13) removed that one too:
PCE's emitted termination clause rules on `(ATOM X)`, which the
branch-fact coverage rule now reads as `(not (consp X))`, so the
admission replays and the whole `totals` clause disappears.

The Parametric constants above stay trio-clean as ever (the
first-class artifacts, per the catalog's equisort entries). All four
axiom sets are gated by the CATALOG AXIOM GATE
(`Waypoints/Catalog.lean` — one home for axiom facts; the local
`#guard_msgs` receipts were retired there by the gate-cruft review,
2026-08-11 R5). That gate did its job here: it REQUIRED `sorryAx` on
this pair, so the moment the last debt retired the build FAILED and
forced this promotion review — the promotion-forcing design working
exactly as intended. Both constants have now moved to the gate's
trio-clean list. -/

set_option maxHeartbeats 12000000 in
/-- STRONG at the canonical world — every premise discharged except the
    two KEPT hypotheses named in the section header. -/
def strongSsortfn1IsSsortfn2AtCanonical := instantiate_parametric%
  strongSsortfn1IsSsortfn2Parametric equisortDev equisortWaypointsWorld
  "strong-ssortfn1-is-ssortfn2" deps [permDev, convertPermDev, orderedPermsDev]

end ACL2.Imported.Waypoints
