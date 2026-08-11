/-
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

/-- PIN `HOW-MANY-SMALLER-BNEXT` (bsort.lisp:28): the mirror of
      `(equal (how-many-smaller e (bnext x)) (how-many-smaller e x))`
    conditional on bnext totality and how-many-smaller's emitted
    non-negative-integer TP corollary (source-true: it counts). -/
example :
    ∀ (env : Env),
      totalHyp1 bsortSweepWorld "BNEXT" →
      tpNonnegInt2 bsortSweepWorld "HOW-MANY-SMALLER" →
      EvTrue bsortSweepWorld env
        (ap2 "EQUAL"
          (ap2 "HOW-MANY-SMALLER" (sym "E") (ap1 "BNEXT" (sym "X")))
          (ap2 "HOW-MANY-SMALLER" (sym "E") (sym "X"))) :=
  ReplayedStatements.replayed_sorting_bsort_HOW_MANY_SMALLER_BNEXT

#print axioms ReplayedStatements.replayed_sorting_bsort_HOW_MANY_SMALLER_BNEXT

/-- PIN `HOW-MANY-BAD-PAIRS-BNEXT` (bsort.lisp:45): the mirror of
      `(implies (not (equal x (bnext x)))
                (< (bnext-size (bnext x)) (bnext-size x)))`
    conditional on bnext totality and the emitted non-negative-integer TP
    corollaries of how-many-smaller and bnext-size (source-true: both
    count). -/
example :
    ∀ (env : Env),
      totalHyp1 bsortSweepWorld "BNEXT" →
      tpNonnegInt2 bsortSweepWorld "HOW-MANY-SMALLER" →
      tpNonnegInt1 bsortSweepWorld "BNEXT-SIZE" →
      EvTrue bsortSweepWorld env
        (ap2 "IMPLIES"
          (ap1 "NOT" (ap2 "EQUAL" (sym "X") (ap1 "BNEXT" (sym "X"))))
          (ap2 "<" (ap1 "BNEXT-SIZE" (ap1 "BNEXT" (sym "X")))
            (ap1 "BNEXT-SIZE" (sym "X")))) :=
  ReplayedStatements.replayed_sorting_bsort_HOW_MANY_BAD_PAIRS_BNEXT

#print axioms ReplayedStatements.replayed_sorting_bsort_HOW_MANY_BAD_PAIRS_BNEXT

/-- PIN `ORDEREDP-WHEN-BNEXT-CONSTANT` (bsort.lisp:57, the endgame arc's
    2e row): the mirror of
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

/-- PIN `ORDEREDP-BSORT` (bsort.lisp:61): the mirror of
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

/-- PIN `TRUE-LISTP-BSORT` (bsort.lisp:68): the mirror of
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

/-- PIN `HOW-MANY-BSORT` (bsort.lisp:76): the mirror of
      `(equal (how-many e (bsort x)) (how-many e x))`
    under the μ-route set + how-many's TP corollary + the linear
    snapshot. The row LABEL shows rule:NOT-MEMB-IMPLIES-HOW-MANY-IS-0,
    but in the registered constant that hypothesis is DISCHARGED
    cross-book (the convert-perm dependency trees in the sweep's bsort
    surface), so the pinned statement is the STRONGER 7-hypothesis
    form. -/
example :
    ∀ (env : Env),
      totalHyp1 bsortSweepWorld "BNEXT" →
      totalHyp1 bsortSweepWorld "BSORT" →
      totalHyp2 bsortSweepWorld "O<" →
      totalHyp1 bsortSweepWorld "O-P" →
      tpNonnegInt2 bsortSweepWorld "HOW-MANY" →
      tpNonnegInt1 bsortSweepWorld "BNEXT-SIZE" →
      linearHMBPB bsortSweepWorld →
      EvTrue bsortSweepWorld env
        (ap2 "EQUAL"
          (ap2 "HOW-MANY" (sym "E") (ap1 "BSORT" (sym "X")))
          (ap2 "HOW-MANY" (sym "E") (sym "X"))) :=
  ReplayedStatements.replayed_sorting_bsort_HOW_MANY_BSORT

#print axioms ReplayedStatements.replayed_sorting_bsort_HOW_MANY_BSORT

/-! ## sorts-equivalent book (acl2/books/sorting/sorts-equivalent.lisp) -/

/-- PIN `BSORT-IS-ISORT` (sorts-equivalent.lisp:24, the endgame arc's W3
    one-hyp row — the functional-instance usefi now DISCHARGED): the
    mirror of
      `(implies (true-listp x) (equal (bsort x) (isort x)))`
    conditional on the sweep row's honest premise set — totalities,
    the TP corollaries of how-many/insert/bnext-size, the cited rules'
    content (each transcribed verbatim from its book's emitted spec),
    and the linear snapshot. -/
example :
    ∀ (env : Env),
      totalHyp1 sortsEqSweepWorld "BNEXT" →
      totalHyp1 sortsEqSweepWorld "BSORT" →
      totalHyp2 sortsEqSweepWorld "O<" →
      totalHyp1 sortsEqSweepWorld "O-P" →
      tpNonnegInt2 sortsEqSweepWorld "HOW-MANY" →
      tpPred2 sortsEqSweepWorld "INSERT" Logic.consp →
      tpNonnegInt1 sortsEqSweepWorld "BNEXT-SIZE" →
      -- true-listp-rm (ordered-perms' emitted spec):
      --   (implies (true-listp a) (equal (true-listp (rm e a)) 't))
      ruleEqHyp1 sortsEqSweepWorld
        (ap1 "TRUE-LISTP" (sym "A"))
        (ap1 "TRUE-LISTP" (ap2 "RM" (sym "E") (sym "A")))
        (qt (sym "T")) →
      -- convert-perm-to-how-many:
      ruleEqHyp sortsEqSweepWorld
        (ap2 "PERM" (sym "X") (sym "Y"))
        (ap2 "EQUAL"
          (ap2 "HOW-MANY"
            (ap2 "PERM-COUNTER-EXAMPLE" (sym "X") (sym "Y")) (sym "X"))
          (ap2 "HOW-MANY"
            (ap2 "PERM-COUNTER-EXAMPLE" (sym "X") (sym "Y")) (sym "Y"))) →
      -- orderedp-isort:
      ruleEqHyp sortsEqSweepWorld
        (ap1 "ORDEREDP" (ap1 "ISORT" (sym "X"))) (qt (sym "T")) →
      -- orderedp-bsort:
      ruleEqHyp sortsEqSweepWorld
        (ap1 "ORDEREDP" (ap1 "BSORT" (sym "X"))) (qt (sym "T")) →
      -- true-listp-bnext:
      ruleEqHyp1 sortsEqSweepWorld
        (ap1 "TRUE-LISTP" (sym "X"))
        (ap1 "TRUE-LISTP" (ap1 "BNEXT" (sym "X"))) (qt (sym "T")) →
      -- true-listp-bsort:
      ruleEqHyp1 sortsEqSweepWorld
        (ap1 "TRUE-LISTP" (sym "X"))
        (ap1 "TRUE-LISTP" (ap1 "BSORT" (sym "X"))) (qt (sym "T")) →
      -- how-many-bsort:
      ruleEqHyp sortsEqSweepWorld
        (ap2 "HOW-MANY" (sym "E") (ap1 "BSORT" (sym "X")))
        (ap2 "HOW-MANY" (sym "E") (sym "X")) →
      linearHMBPB sortsEqSweepWorld →
      EvTrue sortsEqSweepWorld env
        (ap2 "IMPLIES" (ap1 "TRUE-LISTP" (sym "X"))
          (ap2 "EQUAL" (ap1 "BSORT" (sym "X")) (ap1 "ISORT" (sym "X")))) :=
  ReplayedStatements.replayed_sorting_sorts_equivalent_BSORT_IS_ISORT

#print axioms ReplayedStatements.replayed_sorting_sorts_equivalent_BSORT_IS_ISORT

end ACL2.Tests.SortingPinsEndgame
