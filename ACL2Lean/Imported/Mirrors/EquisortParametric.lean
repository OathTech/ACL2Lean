import ACL2Lean.Imported.Mirrors.Macro
import ACL2Lean.Imported.Mirrors.PermBook
import ACL2Lean.Imported.Mirrors.ConvertPerm
import ACL2Lean.Imported.Mirrors.OrderedPerms
import ACL2Lean.DevLoad

namespace ACL2.Imported.Mirrors

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
(the mirror criterion); an unfold demand on a sig fn inside the replay
hard-fails (the witness-dereference guard).  Phase 3 (R7b) instantiates
these constants at concrete worlds. -/

private def equisortLog : String :=
  include_str "../../../acl2_samples/sorting/equisort.proof-log"

/-- The parsed development — the ONLY input is the log. -/
def equisortDev : Development :=
  load_development% equisortLog

set_option maxHeartbeats 3200000 in
/-- WEAK: any `w` in which the pre-scope world is pinned and the scope's
    constraints hold satisfies `(IMPLIES (TRUE-LISTP X) (EQUAL (SORTFN1 X)
    (SORTFN2 X)))` — the recorded tree, replayed over abstract `w`. -/
def weakSortfn1IsSortfn2Parametric := parametric_replayed% equisortDev
  "weak-sortfn1-is-sortfn2" deps [permDev, convertPermDev, orderedPermsDev]

#print axioms weakSortfn1IsSortfn2Parametric

set_option maxHeartbeats 3200000 in
/-- STRONG: the unconditional variant over the strongly-constrained scope
    (`(EQUAL (SSORTFN1 X) (SSORTFN2 X))`), same abstraction. -/
def strongSsortfn1IsSsortfn2Parametric := parametric_replayed% equisortDev
  "strong-ssortfn1-is-ssortfn2" deps [permDev, convertPermDev, orderedPermsDev]

#print axioms strongSsortfn1IsSsortfn2Parametric

end ACL2.Imported.Mirrors
