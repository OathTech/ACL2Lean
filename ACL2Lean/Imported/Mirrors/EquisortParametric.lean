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

#print axioms weakSortfn1IsSortfn2Parametric

set_option maxHeartbeats 3200000 in
/-- STRONG: the unconditional variant over the strongly-constrained scope
    — same telescope shape (4 no-shadows, sig totality, the six scope-2
    constraints in stored-rule form, `use:ORDERED-PERMS`), conclusion
    `EvTrue w env (EQUAL (SSORTFN1 X) (SSORTFN2 X))`. Same non-vacuity
    deferral as WEAK. -/
def strongSsortfn1IsSsortfn2Parametric := parametric_replayed% equisortDev
  "strong-ssortfn1-is-ssortfn2" deps [permDev, convertPermDev, orderedPermsDev]

#print axioms strongSsortfn1IsSsortfn2Parametric

/-! ## The canonical-world instantiations (Phase 3 queue item 1 — the
non-vacuity witnesses, audit 2026-08-08 outside F6)

Applying each parametric constant at the equisort canonical world with
EVERY premise discharged kernel-checked: the no-shadows by decide, the
totality/TP premises by the admission-justification provers, the six
constraint premises by re-replaying their recorded pass-1 trees (the R6
conservativity content), and `use:ORDERED-PERMS` by its recorded tree.
This is simultaneously (a) the proof that the parametric telescopes are
SATISFIABLE (the constants are not vacuous conditionals) and (b) the
first exercise of the R7b "apply at a model" move the sorts-equivalent
capstones need. -/

derive_world equisortMirrorsWorld from equisortDev

set_option maxHeartbeats 12000000 in
/-- WEAK at the canonical world — every premise discharged. -/
def weakSortfn1IsSortfn2AtCanonical := instantiate_parametric%
  weakSortfn1IsSortfn2Parametric equisortDev equisortMirrorsWorld
  "weak-sortfn1-is-sortfn2" deps [permDev, convertPermDev, orderedPermsDev]
  totals [ACL2.Worlds.Sorting.dis_pce_total, ACL2.Worlds.Sorting.dis_how_many_tp]

#print axioms weakSortfn1IsSortfn2AtCanonical

set_option maxHeartbeats 12000000 in
/-- STRONG at the canonical world — every premise discharged. -/
def strongSsortfn1IsSsortfn2AtCanonical := instantiate_parametric%
  strongSsortfn1IsSsortfn2Parametric equisortDev equisortMirrorsWorld
  "strong-ssortfn1-is-ssortfn2" deps [permDev, convertPermDev, orderedPermsDev]
  totals [ACL2.Worlds.Sorting.dis_pce_total, ACL2.Worlds.Sorting.dis_how_many_tp]

#print axioms strongSsortfn1IsSsortfn2AtCanonical

end ACL2.Imported.Mirrors
