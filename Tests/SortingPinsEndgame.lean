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
      -- (total:BNEXT RETIRED 2026-08-14 — the R3 unified
      -- measure/arity table: BNEXT's emitted `:MEASURE (LEN X)` is a
      -- registered ROW, so its totality REPLAYS from the emitted
      -- decrease clauses and the hypothesis left the telescope.
      -- INTENTIONAL; diagnosed against the golden.)
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
    conditional on bnext totality only. -/
example :
    ∀ (env : Env),
      -- (total:BNEXT RETIRED 2026-08-14 — the R3 unified
      -- measure/arity table: BNEXT's emitted `:MEASURE (LEN X)` is a
      -- registered ROW, so its totality REPLAYS from the emitted
      -- decrease clauses and the hypothesis left the telescope.
      -- INTENTIONAL; diagnosed against the golden.)
      -- (tp:HOW-MANY-SMALLER RETIRED 2026-08-12 — the TP prover's
      -- return-path arm discharges it from ACL2's emitted corollary
      -- + `:LEAVES`; the hypothesis left the telescope. INTENTIONAL.)
      -- (tp:BNEXT-SIZE RETIRED 2026-08-13 — TP-replay arc increment 3,
      -- the CALLEE-TP return path: BNEXT-SIZE's single non-`'0` emitted
      -- leaf is a BINARY-+ whose first summand is a HOW-MANY-SMALLER
      -- CALL, and that callee's OWN emitted non-negative-integer
      -- corollary supplies it. INTENTIONAL — diagnosed against the
      -- golden row-by-row, not a silent drift.)
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
      -- (total:BNEXT RETIRED 2026-08-14 — the R3 unified
      -- measure/arity table: BNEXT's emitted `:MEASURE (LEN X)` is a
      -- registered ROW, so its totality REPLAYS from the emitted
      -- decrease clauses and the hypothesis left the telescope.
      -- INTENTIONAL; diagnosed against the golden.)
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
    o-p) and the linear:HOW-MANY-BAD-PAIRS-BNEXT snapshot content
    (bsort's admitted measure decrease). -/
example :
    ∀ (env : Env),
      -- (total:BNEXT RETIRED 2026-08-14 — the R3 unified
      -- measure/arity table: BNEXT's emitted `:MEASURE (LEN X)` is a
      -- registered ROW, so its totality REPLAYS from the emitted
      -- decrease clauses and the hypothesis left the telescope.
      -- INTENTIONAL; diagnosed against the golden.)
      -- (total:BSORT RETIRED 2026-08-15 — T1+2 sprint phase 3a: BSORT's
      -- RECORDED admission replay now reaches its decrease. Its emitted
      -- ruler is (EQUAL (BNEXT X) X), an OPAQUE test whose value and
      -- convergence the body walk's if-split had already bound and then
      -- discarded; carrying that pair in the walk's branch facts lets the
      -- ruler peel consume it, so total:BSORT REPLAYS from the emitted
      -- admission data and the hypothesis left the telescope.
      -- INTENTIONAL; diagnosed against the golden.)
      -- (total:O< / total:O-P RETIRED 2026-08-15 — T1+2 sprint P3b: the
      -- ORDINAL registry row (Replay/OrdinalSim) + the O-FINP recognizer
      -- duality + the world-read EQUAL-alias normalization of ACL2's
      -- recomputed ground-zero rulers discharge both admissions from
      -- their OWN emitted :TERMINATION-CLAUSES, so the hypotheses left
      -- the telescope and the pinned types drop them. INTENTIONAL;
      -- diagnosed against the golden.)
      -- (tp:BNEXT-SIZE RETIRED 2026-08-13 — see HOW-MANY-BAD-PAIRS-BNEXT
      -- above: the CALLEE-TP return path, increment 3. INTENTIONAL.)
      -- (linear:HOW-MANY-BAD-PAIRS-BNEXT RETIRED 2026-08-15 — T1+2
      -- sprint P3c collection: dischargeLinearHyp decodes the stored
      -- :LINEAR rule from its defthm's replayed statement (source row
      -- unconditional), so the hypothesis left the telescope and the
      -- pinned type drops it. INTENTIONAL; diagnosed row-by-row.)
      EvTrue bsortSweepWorld env (ap1 "ORDEREDP" (ap1 "BSORT" (sym "X"))) :=
  ReplayedStatements.replayed_sorting_bsort_ORDEREDP_BSORT

#print axioms ReplayedStatements.replayed_sorting_bsort_ORDEREDP_BSORT

/-- PIN `TRUE-LISTP-BSORT` (bsort.lisp:68): the replayed statement of
      `(implies (true-listp x) (true-listp (bsort x)))`
    under the same μ-route hypothesis set as ORDEREDP-BSORT. -/
example :
    ∀ (env : Env),
      -- (total:BNEXT RETIRED 2026-08-14 — the R3 unified
      -- measure/arity table: BNEXT's emitted `:MEASURE (LEN X)` is a
      -- registered ROW, so its totality REPLAYS from the emitted
      -- decrease clauses and the hypothesis left the telescope.
      -- INTENTIONAL; diagnosed against the golden.)
      -- (total:BSORT RETIRED 2026-08-15 — T1+2 sprint phase 3a: BSORT's
      -- RECORDED admission replay now reaches its decrease. Its emitted
      -- ruler is (EQUAL (BNEXT X) X), an OPAQUE test whose value and
      -- convergence the body walk's if-split had already bound and then
      -- discarded; carrying that pair in the walk's branch facts lets the
      -- ruler peel consume it, so total:BSORT REPLAYS from the emitted
      -- admission data and the hypothesis left the telescope.
      -- INTENTIONAL; diagnosed against the golden.)
      -- (total:O< / total:O-P RETIRED 2026-08-15 — T1+2 sprint P3b: the
      -- ORDINAL registry row (Replay/OrdinalSim) + the O-FINP recognizer
      -- duality + the world-read EQUAL-alias normalization of ACL2's
      -- recomputed ground-zero rulers discharge both admissions from
      -- their OWN emitted :TERMINATION-CLAUSES, so the hypotheses left
      -- the telescope and the pinned types drop them. INTENTIONAL;
      -- diagnosed against the golden.)
      -- (tp:BNEXT-SIZE RETIRED 2026-08-13 — see HOW-MANY-BAD-PAIRS-BNEXT
      -- above: the CALLEE-TP return path, increment 3. INTENTIONAL.)
      -- (linear:HOW-MANY-BAD-PAIRS-BNEXT RETIRED 2026-08-15 — T1+2
      -- sprint P3c collection: dischargeLinearHyp decodes the stored
      -- :LINEAR rule from its defthm's replayed statement (source row
      -- unconditional), so the hypothesis left the telescope and the
      -- pinned type drops it. INTENTIONAL; diagnosed row-by-row.)
      EvTrue bsortSweepWorld env
        (ap2 "IMPLIES" (ap1 "TRUE-LISTP" (sym "X"))
          (ap1 "TRUE-LISTP" (ap1 "BSORT" (sym "X")))) :=
  ReplayedStatements.replayed_sorting_bsort_TRUE_LISTP_BSORT

#print axioms ReplayedStatements.replayed_sorting_bsort_TRUE_LISTP_BSORT

/-- PIN `HOW-MANY-BSORT` (bsort.lisp:76): the replayed statement of
      `(equal (how-many e (bsort x)) (how-many e x))`
    under the μ-route set + the linear
    snapshot — exactly the golden row's five conds (the cited
    NOT-MEMB-IMPLIES-HOW-MANY-IS-0 rule discharges cross-book in the
    sweep itself, so it appears in neither the row nor this pin; an
    earlier docstring here claimed the label showed it — false against
    the golden, corrected in the exit-audit fix round). -/
example :
    ∀ (env : Env),
      -- (total:BNEXT RETIRED 2026-08-14 — the R3 unified
      -- measure/arity table: BNEXT's emitted `:MEASURE (LEN X)` is a
      -- registered ROW, so its totality REPLAYS from the emitted
      -- decrease clauses and the hypothesis left the telescope.
      -- INTENTIONAL; diagnosed against the golden.)
      -- (total:BSORT RETIRED 2026-08-15 — T1+2 sprint phase 3a: BSORT's
      -- RECORDED admission replay now reaches its decrease. Its emitted
      -- ruler is (EQUAL (BNEXT X) X), an OPAQUE test whose value and
      -- convergence the body walk's if-split had already bound and then
      -- discarded; carrying that pair in the walk's branch facts lets the
      -- ruler peel consume it, so total:BSORT REPLAYS from the emitted
      -- admission data and the hypothesis left the telescope.
      -- INTENTIONAL; diagnosed against the golden.)
      -- (total:O< / total:O-P RETIRED 2026-08-15 — T1+2 sprint P3b: the
      -- ORDINAL registry row (Replay/OrdinalSim) + the O-FINP recognizer
      -- duality + the world-read EQUAL-alias normalization of ACL2's
      -- recomputed ground-zero rulers discharge both admissions from
      -- their OWN emitted :TERMINATION-CLAUSES, so the hypotheses left
      -- the telescope and the pinned types drop them. INTENTIONAL;
      -- diagnosed against the golden.)
      -- (tp:HOW-MANY RETIRED 2026-08-12 — same TP-replay route.)
      -- (tp:BNEXT-SIZE RETIRED 2026-08-13 — see HOW-MANY-BAD-PAIRS-BNEXT
      -- above: the CALLEE-TP return path, increment 3. INTENTIONAL.)
      -- (linear:HOW-MANY-BAD-PAIRS-BNEXT RETIRED 2026-08-15 — T1+2
      -- sprint P3c collection: dischargeLinearHyp decodes the stored
      -- :LINEAR rule from its defthm's replayed statement (source row
      -- unconditional), so the hypothesis left the telescope and the
      -- pinned type drops it. INTENTIONAL; diagnosed row-by-row.)
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

/-- PIN `BSORT-IS-ISORT` (sorts-equivalent.lisp:24, the endgame arc's W3
    one-hyp row — the functional-instance usefi DISCHARGED): the
    mirror of
      `(implies (true-listp x) (equal (bsort x) (isort x)))`
    conditional on the sweep row's honest premise set — totalities,
    the cited rules' content (each transcribed verbatim from its book's
    emitted spec), and the linear snapshot.

    RETURNED 2026-08-13 (the TP-replay arc's ATOM-leg increment) per the
    return condition recorded at its retirement (thin-Lean purge,
    2026-08-11): the row had regressed to ASSUMED ◌ so the sweep
    registered no constant to pin; with `total:PERM-COUNTER-EXAMPLE`
    retired by the replay route the usefi discharge succeeds and the row
    is REPLAYED ✓ again. The 15-hypothesis git-history text returns with
    THREE hypotheses gone — the TP corollaries whose conditions retired
    across this arc (`tp:HOW-MANY` 2026-08-12, `tp:INSERT` and
    `tp:BNEXT-SIZE` 2026-08-13) — marked in place below. -/
example :
    ∀ (env : Env),
      -- (total:BNEXT RETIRED 2026-08-14 — the R3 unified
      -- measure/arity table: BNEXT's emitted `:MEASURE (LEN X)` is a
      -- registered ROW, so its totality REPLAYS from the emitted
      -- decrease clauses and the hypothesis left the telescope.
      -- INTENTIONAL; diagnosed against the golden.)
      -- (total:BSORT RETIRED 2026-08-15 — T1+2 sprint P3c collection:
      -- the cross-book ADMISSION pre-pass replays BSORT's recorded
      -- admission at this world (:INCLUDE-BOOK source). INTENTIONAL.)
      -- (total:O< / total:O-P RETIRED 2026-08-15 — T1+2 sprint P3b: the
      -- ORDINAL registry row (Replay/OrdinalSim) + the O-FINP recognizer
      -- duality + the world-read EQUAL-alias normalization of ACL2's
      -- recomputed ground-zero rulers discharge both admissions from
      -- their OWN emitted :TERMINATION-CLAUSES, so the hypotheses left
      -- the telescope and the pinned types drop them. INTENTIONAL;
      -- diagnosed against the golden.)
      -- (tp:HOW-MANY RETIRED 2026-08-12 — the BINARY-+ return path;
      -- tp:INSERT RETIRED 2026-08-13 — the CONS return-path shape;
      -- tp:BNEXT-SIZE RETIRED 2026-08-13 — the CALLEE-TP shape. All
      -- three left the telescope.)
      -- (rule:TRUE-LISTP-RM, rule:CONVERT-PERM-TO-HOW-MANY,
      -- rule:ORDEREDP-ISORT, rule:ORDEREDP-BSORT RETIRED 2026-08-15 —
      -- T1+2 sprint P3c: the WP5 cross-book D1 transfer replays each
      -- dependency at this world, so all four hypotheses left the
      -- telescope. INTENTIONAL; diagnosed row-by-row.)
      -- true-listp-bnext:
      ruleEqHyp1 sortsEqSweepWorld
        (ap1 "TRUE-LISTP" (sym "X"))
        (ap1 "TRUE-LISTP" (ap1 "BNEXT" (sym "X"))) (qt (sym "T")) →
      -- (rule:TRUE-LISTP-BSORT, rule:HOW-MANY-BSORT RETIRED 2026-08-15
      -- — the same transfer (bsort-book rows now unconditional).
      -- INTENTIONAL. linear:HOW-MANY-BAD-PAIRS-BNEXT SURVIVES at this
      -- world — the sorts-equivalent occurrence, the row's honest
      -- residue.)
      linearHMBPB sortsEqSweepWorld →
      EvTrue sortsEqSweepWorld env
        (ap2 "IMPLIES" (ap1 "TRUE-LISTP" (sym "X"))
          (ap2 "EQUAL" (ap1 "BSORT" (sym "X")) (ap1 "ISORT" (sym "X")))) :=
  ReplayedStatements.replayed_sorting_sorts_equivalent_BSORT_IS_ISORT

#print axioms ReplayedStatements.replayed_sorting_sorts_equivalent_BSORT_IS_ISORT

end ACL2.Tests.SortingPinsEndgame
