/-
  ROLE (two-category ruling, 2026-08-12): REGRESSION CANARIES for the
  metric layer, not trust anchors — they detect silent statement-content
  drift the golden (status-only) cannot see. See Tests/SortingPins.lean's
  header for the full relabeling.

  ENDGAME-ARC statement pins (charter item 5): the bsort greens the
  restructure arc landed (HOW-MANY-SMALLER-BNEXT, HOW-MANY-BAD-PAIRS-BNEXT,
  ORDEREDP/TRUE-LISTP/HOW-MANY-BSORT), the endgame greens
  (ORDEREDP-WHEN-BNEXT-CONSTANT, BSORT-IS-ISORT), each pinned against the
  SWEEP'S OWN registered replayed constant (importing the coverage modules
  — no duplicate replay, so pins and sweep CANNOT drift; the F3
  golden-prefix cross-check is inherited from the coverage gate itself).
  Statements hand-transcribed from `acl2/books/sorting/bsort.lisp` and
  `sorts-equivalent.lisp`; hypothesis shapes from Tests/SortingPins'
  shared vocabulary (de-privatized for this module).
-/
import Tests.SortingPins
import Tests.Coverage.BSbsort
import Tests.Coverage.BSconvertPermToHowMany
import Tests.Coverage.BSsortsEquivalent

namespace ACL2.Tests.SortingPinsEndgame

open ACL2 ACL2.Replay ACL2.Tests.SortingPins

/-- `linear:<rune>` — the emitted ground-zero :LINEAR rule snapshot's
    content (`mkLinearHypType`'s exact shape): `∀ env', EvTrue hyp →
    EvTrue concl` over the recorded hyps/concl verbatim. The endgame
    arc's "linear-hyp pin helper". -/
def linearHyp1 (w : World) (hyp concl : SExpr) : Prop :=
  ∀ env' : Env, EvTrue w env' hyp → EvTrue w env' concl

/-- The linear:HOW-MANY-BAD-PAIRS-BNEXT snapshot, verbatim
    (`(:GROUND-ZERO-LINEAR-RULES …)` in the bsort/sorts-equivalent logs):
    hyp `(NOT (EQUAL X (BNEXT X)))`, concl
    `(< (BNEXT-SIZE (BNEXT X)) (BNEXT-SIZE X))`. -/
def linearHMBPB (w : World) : Prop :=
  linearHyp1 w
    (ap1 "NOT" (ap2 "EQUAL" (sym "X") (ap1 "BNEXT" (sym "X"))))
    (ap2 "<" (ap1 "BNEXT-SIZE" (ap1 "BNEXT" (sym "X")))
      (ap1 "BNEXT-SIZE" (sym "X")))

/-- The bsort sweep world (same log as the coverage run — the registered
    constants' world expression is defeq to this). -/
private def bsortLog : String :=
  include_str "../acl2_samples/sorting/bsort.proof-log"
def bsortSweepDev : Development := load_development% bsortLog
derive_world bsortSweepWorld from bsortSweepDev

private def sortsEqLog : String :=
  include_str "../acl2_samples/sorting/sorts-equivalent.proof-log"
def sortsEqSweepDev : Development := load_development% sortsEqLog
derive_world sortsEqSweepWorld from sortsEqSweepDev

/-! ## bsort book (acl2/books/sorting/bsort.lisp) -/

/-- PIN `HOW-MANY-SMALLER-BNEXT` (bsort.lisp:28): the replayed statement of
      `(equal (how-many-smaller e (bnext x)) (how-many-smaller e x))`
    conditional on bnext totality and how-many-smaller's emitted
    non-negative-integer TP corollary (source-true: it counts). -/
example :
    ∀ (env : Env),
      totalHyp1 bsortSweepWorld "BNEXT" →
      -- (tp:HOW-MANY-SMALLER RETIRED 2026-08-12 — the TP prover's
      -- return-path arm discharges it from ACL2's emitted corollary
      -- + `:LEAVES`; the hypothesis left the telescope. INTENTIONAL.)
      EvTrue bsortSweepWorld env
        (ap2 "EQUAL"
          (ap2 "HOW-MANY-SMALLER" (sym "E") (ap1 "BNEXT" (sym "X")))
          (ap2 "HOW-MANY-SMALLER" (sym "E") (sym "X"))) :=
  ReplayedStatements.replayed_sorting_bsort_HOW_MANY_SMALLER_BNEXT

#print axioms ReplayedStatements.replayed_sorting_bsort_HOW_MANY_SMALLER_BNEXT

/-- PIN `HOW-MANY-BAD-PAIRS-BNEXT` (bsort.lisp:45): the replayed statement of
      `(implies (not (equal x (bnext x)))
                (< (bnext-size (bnext x)) (bnext-size x)))`
    conditional on bnext totality and the emitted non-negative-integer TP
    corollaries of how-many-smaller and bnext-size (source-true: both
    count). -/
example :
    ∀ (env : Env),
      totalHyp1 bsortSweepWorld "BNEXT" →
      -- (tp:HOW-MANY-SMALLER RETIRED 2026-08-12 — the TP prover's
      -- return-path arm discharges it from ACL2's emitted corollary
      -- + `:LEAVES`; the hypothesis left the telescope. INTENTIONAL.)
      tpNonnegInt1 bsortSweepWorld "BNEXT-SIZE" →
      EvTrue bsortSweepWorld env
        (ap2 "IMPLIES"
          (ap1 "NOT" (ap2 "EQUAL" (sym "X") (ap1 "BNEXT" (sym "X"))))
          (ap2 "<" (ap1 "BNEXT-SIZE" (ap1 "BNEXT" (sym "X")))
            (ap1 "BNEXT-SIZE" (sym "X")))) :=
  ReplayedStatements.replayed_sorting_bsort_HOW_MANY_BAD_PAIRS_BNEXT

#print axioms ReplayedStatements.replayed_sorting_bsort_HOW_MANY_BAD_PAIRS_BNEXT

/-- PIN `ORDEREDP-WHEN-BNEXT-CONSTANT` (bsort.lisp:57, the endgame arc's
    2e row): the replayed statement of
      `(implies (equal (bnext x) x) (orderedp x))`
    conditional on bnext totality only. -/
example :
    ∀ (env : Env),
      totalHyp1 bsortSweepWorld "BNEXT" →
      EvTrue bsortSweepWorld env
        (ap2 "IMPLIES"
          (ap2 "EQUAL" (ap1 "BNEXT" (sym "X")) (sym "X"))
          (ap1 "ORDEREDP" (sym "X"))) :=
  ReplayedStatements.replayed_sorting_bsort_ORDEREDP_WHEN_BNEXT_CONSTANT

#print axioms
  ReplayedStatements.replayed_sorting_bsort_ORDEREDP_WHEN_BNEXT_CONSTANT

/-- PIN `ORDEREDP-BSORT` (bsort.lisp:61): the replayed statement of
      `(orderedp (bsort x))`
    conditional on the totalities the μ-route rides (bnext, bsort, o<,
    o-p), bnext-size's TP corollary, and the
    linear:HOW-MANY-BAD-PAIRS-BNEXT snapshot content (bsort's admitted
    measure decrease). -/
example :
    ∀ (env : Env),
      totalHyp1 bsortSweepWorld "BNEXT" →
      totalHyp1 bsortSweepWorld "BSORT" →
      totalHyp2 bsortSweepWorld "O<" →
      totalHyp1 bsortSweepWorld "O-P" →
      tpNonnegInt1 bsortSweepWorld "BNEXT-SIZE" →
      linearHMBPB bsortSweepWorld →
      EvTrue bsortSweepWorld env (ap1 "ORDEREDP" (ap1 "BSORT" (sym "X"))) :=
  ReplayedStatements.replayed_sorting_bsort_ORDEREDP_BSORT

#print axioms ReplayedStatements.replayed_sorting_bsort_ORDEREDP_BSORT

/-- PIN `TRUE-LISTP-BSORT` (bsort.lisp:68): the replayed statement of
      `(implies (true-listp x) (true-listp (bsort x)))`
    under the same μ-route hypothesis set as ORDEREDP-BSORT. -/
example :
    ∀ (env : Env),
      totalHyp1 bsortSweepWorld "BNEXT" →
      totalHyp1 bsortSweepWorld "BSORT" →
      totalHyp2 bsortSweepWorld "O<" →
      totalHyp1 bsortSweepWorld "O-P" →
      tpNonnegInt1 bsortSweepWorld "BNEXT-SIZE" →
      linearHMBPB bsortSweepWorld →
      EvTrue bsortSweepWorld env
        (ap2 "IMPLIES" (ap1 "TRUE-LISTP" (sym "X"))
          (ap1 "TRUE-LISTP" (ap1 "BSORT" (sym "X")))) :=
  ReplayedStatements.replayed_sorting_bsort_TRUE_LISTP_BSORT

#print axioms ReplayedStatements.replayed_sorting_bsort_TRUE_LISTP_BSORT

/-- PIN `HOW-MANY-BSORT` (bsort.lisp:76): the replayed statement of
      `(equal (how-many e (bsort x)) (how-many e x))`
    under the μ-route set + how-many's TP corollary + the linear
    snapshot — exactly the golden row's seven conds (the cited
    NOT-MEMB-IMPLIES-HOW-MANY-IS-0 rule discharges cross-book in the
    sweep itself, so it appears in neither the row nor this pin; an
    earlier docstring here claimed the label showed it — false against
    the golden, corrected in the exit-audit fix round). -/
example :
    ∀ (env : Env),
      totalHyp1 bsortSweepWorld "BNEXT" →
      totalHyp1 bsortSweepWorld "BSORT" →
      totalHyp2 bsortSweepWorld "O<" →
      totalHyp1 bsortSweepWorld "O-P" →
      -- (tp:HOW-MANY RETIRED 2026-08-12 — same TP-replay route.)
      tpNonnegInt1 bsortSweepWorld "BNEXT-SIZE" →
      linearHMBPB bsortSweepWorld →
      EvTrue bsortSweepWorld env
        (ap2 "EQUAL"
          (ap2 "HOW-MANY" (sym "E") (ap1 "BSORT" (sym "X")))
          (ap2 "HOW-MANY" (sym "E") (sym "X"))) :=
  ReplayedStatements.replayed_sorting_bsort_HOW_MANY_BSORT

#print axioms ReplayedStatements.replayed_sorting_bsort_HOW_MANY_BSORT

/-! ## convert-perm-to-how-many book -/

private def convertPermSweepLog : String :=
  include_str "../acl2_samples/sorting/convert-perm-to-how-many.proof-log"
def convertPermSweepDev : Development := load_development% convertPermSweepLog
derive_world convertPermSweepWorld from convertPermSweepDev

/-- PIN `HOW-MANY-RM-GENERAL` (convert-perm-to-how-many.lisp:50, the
    endgame arc's tau-slice row — exit-audit fix round: the arc's plan
    covered it but the first pin wave skipped it; the outside reviewer
    hand-verified this exact shape): the replayed statement of
      `(equal (how-many a (rm b x))
              (if (and (equal a b) (memb a x))
                  (1- (how-many a x))
                (how-many a x)))`
    under ACL2's translation (`and` → nested IF, `1-` → `(binary-+ -1 ·)`),
    conditional on how-many's non-negative-integer TP corollary only. -/
example :
    ∀ (env : Env),
      -- (tp:HOW-MANY RETIRED 2026-08-12 — same TP-replay route.)
      EvTrue convertPermSweepWorld env
        (ap2 "EQUAL"
          (ap2 "HOW-MANY" (sym "A") (ap2 "RM" (sym "B") (sym "X")))
          (ap3 "IF"
            (ap3 "IF" (ap2 "EQUAL" (sym "A") (sym "B"))
              (ap2 "MEMB" (sym "A") (sym "X")) (qt .nil))
            (ap2 "BINARY-+" (qt (.atom (.number (.int (-1)))))
              (ap2 "HOW-MANY" (sym "A") (sym "X")))
            (ap2 "HOW-MANY" (sym "A") (sym "X")))) :=
  ReplayedStatements.replayed_sorting_convert_perm_to_how_many_HOW_MANY_RM_GENERAL

#print axioms
  ReplayedStatements.replayed_sorting_convert_perm_to_how_many_HOW_MANY_RM_GENERAL

/-! ## sorts-equivalent book (acl2/books/sorting/sorts-equivalent.lisp) -/

/-! ## BSORT-IS-ISORT pin RETIRED (thin-Lean purge, 2026-08-11)

The row regressed to ASSUMED (offer route) when the usefi pre-pass lost
its forbidden Lean-side dischargers; its sweep constant is not
registered. The 15-hypothesis pin text is in git history and RETURNS
verbatim when the REQUIRED-class debt (admission coverage) and the
TP-replay discharge re-green the row. -/

end ACL2.Tests.SortingPinsEndgame
