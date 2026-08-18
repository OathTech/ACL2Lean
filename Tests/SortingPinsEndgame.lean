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

-- (The endgame arc's `linearHyp1` / `linearHMBPB` pin helpers — the
-- `mkLinearHypType` shape and the HOW-MANY-BAD-PAIRS-BNEXT snapshot's
-- verbatim hyp/concl — were DELETED 2026-08-16 (T1+2 sprint P6) with
-- their last use: `linear:HOW-MANY-BAD-PAIRS-BNEXT` retired from
-- BSORT-IS-ISORT's telescope, so the shape no longer appears in any
-- pinned type. The deletion+rewiring flow; the retirement is diagnosed
-- in place at the pin below. Their content is still LIVE-checked — the
-- golden row is unconditional only because the discharge fires.)

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
    **UNCONDITIONAL since 2026-08-14** — the pinned type is premise-free;
    bnext totality and how-many-smaller's emitted non-negative-integer TP
    corollary are retired, dated in the log below. -/
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
    **UNCONDITIONAL since 2026-08-14** — the pinned type is premise-free;
    its one former condition, bnext totality, is retired and dated in the
    log below. -/
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
    **UNCONDITIONAL since 2026-08-14** — the pinned type is premise-free;
    its one former condition, bnext totality, is retired and dated in the
    log below. -/
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
    **UNCONDITIONAL since 2026-08-15** — the pinned type is premise-free;
    the totalities the μ-route rides (bnext, bsort, o<, o-p) and the
    linear:HOW-MANY-BAD-PAIRS-BNEXT snapshot content (bsort's admitted
    measure decrease) are all retired, each dated in the log below. -/
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
    **UNCONDITIONAL since 2026-08-12** — the pinned type is premise-free;
    its one former condition, how-many's non-negative-integer TP
    corollary, is retired and dated in the log below. -/
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
    — as of 2026-08-16 (T1+2 sprint P6) UNCONDITIONAL: the telescope is
    empty, so what is pinned here is the replayed statement itself, with
    no premise left to transcribe. Every hypothesis this pin once carried
    is listed below with the date and mechanism of its retirement (the
    file's running record of the row's descent from 15 premises to 0).

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
      -- (rule:TRUE-LISTP-BSORT, rule:HOW-MANY-BSORT RETIRED 2026-08-15
      -- — the same transfer (bsort-book rows now unconditional).
      -- INTENTIONAL.)
      -- (rule:TRUE-LISTP-BNEXT and linear:HOW-MANY-BAD-PAIRS-BNEXT —
      -- the LAST TWO — RETIRED 2026-08-16, T1+2 sprint P6: both reach
      -- this telescope from BSORT's RECORDED ADMISSION proof, i.e.
      -- AFTER the dependency sweep had run, so nothing ever attempted
      -- them. Two pieces land together: the cross-book demand seed is
      -- widened with the consumer's own OFFER surfaces (so the transfer
      -- registers the two bsort-book dependencies), and the post-replay
      -- discharge lane runs to QUIESCENCE with `totalEnv` rebuilt as
      -- names arrive (so the dependency's own total:BNEXT /
      -- total:BNEXT-SIZE / tp:BNEXT-SIZE, which arrive after the
      -- totality/TP passes, are attempted and discharged in the next
      -- round). The row is REPLAYED ✓ UNCONDITIONAL and this pin's type
      -- is now premise-free. INTENTIONAL; diagnosed against the golden —
      -- the ONLY two golden lines that moved were this row and the
      -- header.)
      EvTrue sortsEqSweepWorld env
        (ap2 "IMPLIES" (ap1 "TRUE-LISTP" (sym "X"))
          (ap2 "EQUAL" (ap1 "BSORT" (sym "X")) (ap1 "ISORT" (sym "X")))) :=
  ReplayedStatements.replayed_sorting_sorts_equivalent_BSORT_IS_ISORT

#print axioms ReplayedStatements.replayed_sorting_sorts_equivalent_BSORT_IS_ISORT

/-! ## sorts-equivalent CAPSTONE statement pins — MOVED HERE from
Tests/SortingPins.lean 2026-08-18 (perf arc phase 2 item 3, the cascade
decoupling): these two pins were SortingPins' ONLY consumers of the
coverage import, and carrying them there serialized that module's ~13
minutes of pins replays AFTER the sweep's largest module. They bind THE
SAME sweep-registered constants as before (this module already imports
`Tests.Coverage.BSsortsEquivalent`); the pinned types now spell the
world as this module's `sortsEqSweepWorld` — the same `derive_world`
over the same log as the retired `sortsEqPinsWorld` (byte-identical
world constant, different name). Everything else — conclusions,
hypothesis history, retirement diagnoses — is the moved text verbatim.
The original section docs (close-out arc increment 0 provenance, the
2026-08-16 trueListpRmHyp/convertPermHyp deletion note) remain in the
git history of Tests/SortingPins.lean. -/

/-! ## Capstone pins — RETURNED 2026-08-13 (the TP-replay arc's ATOM-leg
increment)

They were retired by the thin-Lean purge (2026-08-11) with a recorded
return condition: the rows had regressed to ASSUMED ◌ when the usefi
pre-pass lost its forbidden Lean-side dischargers, so the sweep
registered no constant for them to pin. That condition is now met —
`total:PERM-COUNTER-EXAMPLE` retired by the replay route (the ATOM leg:
PCE's emitted termination clause rules on `(ATOM X)`), the usefi
discharge succeeds, and both rows are REPLAYED ✓ again.

RESURRECTED, NOT RE-DERIVED: the conclusions and every surviving
hypothesis are the git-history texts verbatim. What CHANGED is that
hypotheses LEFT the telescopes as their conditions retired across this
arc — each drop carries a diagnosis comment below, never a silent
edit. MSORT loses three (`tp:HOW-MANY`, `tp:INSERT`, `tp:EVENS`);
QSORT loses five (`total:PERM-COUNTER-EXAMPLE`, `tp:HOW-MANY`,
`tp:INSERT`, `tp:ALL-REL`, and — 2026-08-14, the D-A ts-algebra
consumer — `tp:ACL2-COUNT`) and, since 2026-08-16 (T1+2 sprint P5b,
the conditional stored-rule route), `tp:QSORT` as well. -/

/-- PIN the machine statement of `MSORT-IS-ISORT`
    (sorts-equivalent.lisp:12): the mirror of
    `(equal (msort x) (isort x))`, **UNCONDITIONAL since 2026-08-15** —
    the pinned type is premise-free. Its former cond[…] telescope
    (merge2/msort totality; the true-listp-rm and
    convert-perm-to-how-many stored rules) is retired item by item in
    the log below, each dated. -/
example :
    ∀ (env : Env),
      -- (total:MERGE2 and total:MSORT RETIRED 2026-08-14 — the R3
      -- unified measure/arity table; both left the telescope.)
      -- (tp:HOW-MANY RETIRED 2026-08-12 — the TP prover's BINARY-+
      -- return path; tp:INSERT and tp:EVENS RETIRED 2026-08-13 — the
      -- CONS return-path shape. All three left the telescope.)
      -- (rule:TRUE-LISTP-RM and rule:CONVERT-PERM-TO-HOW-MANY RETIRED
      -- 2026-08-15 — T1+2 sprint P3c: the WP5 cross-book D1 transfer
      -- replays both dependencies at this world, so both hypotheses
      -- left the telescope and the row is UNCONDITIONAL. INTENTIONAL;
      -- diagnosed row-by-row against the golden.)
      EvTrue sortsEqSweepWorld env
        (ap2 "EQUAL" (ap1 "MSORT" (sym "X")) (ap1 "ISORT" (sym "X"))) :=
  ReplayedStatements.replayed_sorting_sorts_equivalent_MSORT_IS_ISORT

#print axioms ReplayedStatements.replayed_sorting_sorts_equivalent_MSORT_IS_ISORT

/-- PIN the machine statement of `QSORT-IS-ISORT`
    (sorts-equivalent.lisp:18): the mirror of
    `(equal (qsort x) (isort x))`, **UNCONDITIONAL since 2026-08-16** —
    the pinned type is premise-free. Its former cond[…] telescope
    (qsort/o< totality, the emitted TPs, true-listp-rm +
    convert-perm-to-how-many, the arithmetic-3 commutativity + two
    if-lifting rules, and the three qsort-book rules how-many-filter-1 /
    how-many-qsort / orderedp-append) is retired item by item in the log
    below, each dated.
    DISCLOSURE RETIRED (2026-08-16): this docstring used to disclose
    `how-many-qsort` as "the row's disclosed own-obligation assumption,
    audit O-3". That assumption is GONE — it left the telescope with the
    P5b/P6 retirements, the type no longer carries it, and a standing
    disclosure of an assumption that no longer exists is itself a
    records defect. -/
example :
    ∀ (env : Env),
      -- (total:PERM-COUNTER-EXAMPLE RETIRED 2026-08-13 — the ATOM leg;
      -- it led this telescope in the pre-purge text.)
      -- (total:QSORT RETIRED 2026-08-15 — T1+2 sprint P3c: the
      -- cross-book ADMISSION pre-pass replays QSORT's recorded
      -- admission at this world (:INCLUDE-BOOK source), so the
      -- hypothesis left the telescope. INTENTIONAL.)
      -- (total:O< RETIRED 2026-08-15 — T1+2 sprint P3b: the ORDINAL
      -- registry row (Replay/OrdinalSim) + the O-FINP recognizer
      -- duality + the world-read EQUAL-alias normalization of ACL2's
      -- recomputed ground-zero rulers discharge O<'s admission from
      -- its OWN emitted :TERMINATION-CLAUSES, so the hypothesis left
      -- the telescope and the pinned type drops it. INTENTIONAL;
      -- diagnosed against the golden.)
      -- (tp:HOW-MANY RETIRED 2026-08-12; tp:INSERT 2026-08-13, the CONS
      -- shape; tp:ALL-REL 2026-08-13, the arity-3 assembly.)
      -- (tp:ACL2-COUNT RETIRED 2026-08-14 — the D-A ts-algebra
      -- consumer: the R2 fork batch's context-refined leaves carry
      -- ACL2's own derivation, so the corollary is PROVED and the
      -- hypothesis left the telescope.)
      -- (tp:QSORT RETIRED 2026-08-16 — T1+2 sprint P5b. P4b's verbatim
      -- frontier here was "proveTp: BINARY-APPEND's corollary class
      -- …conspOrArg neither matches nor implies the …trueListp class
      -- QSORT's prescription needs", and it was a CONSUMPTION item
      -- exactly as P4b's corrected map said: RT2 had already emitted the
      -- stored strengthening TRUE-LISTP-APPEND with its own hypotheses,
      -- `:term` and per-rule `:LEAVES`. The driver now takes the
      -- `:ALL-TPS` route — re-proving that rule from BINARY-APPEND's
      -- body under its hypothesis, discharging the hypothesis at
      -- QSORT's own leaf, and taking the FILTER-headed self-call's
      -- decrease from QSORT's REPLAYED admission. The hypothesis left
      -- the telescope and the pinned type drops it. INTENTIONAL;
      -- diagnosed against the golden.)
      -- (rule:TRUE-LISTP-RM and rule:CONVERT-PERM-TO-HOW-MANY RETIRED
      -- 2026-08-15 — the WP5 transfer, see MSORT-IS-ISORT above.)
      -- (the ARITHMETIC-3 family — rule:(+ y x), rule:(+ y (+ x z)),
      -- rule:(+ (+ x y) z), rule:(+ x (if a b c)) — and the if-lifting
      -- rule:(equal (if a b c) x) RETIRED 2026-08-15, T1+2 sprint P4b:
      -- all five are registered in `d5GzRules`, so the driver discharges
      -- each at its CITED rune from its D5 prelude constant
      -- (`Replay/GzRules.lean`, recompute-checked against the emitted
      -- `(:RULES …)` entry). This ALSO closes P3c's flagged +1: the
      -- rule:(+ (+ x y) z) that JOINED here when rule:HOW-MANY-FILTER-1
      -- retired is gone with the rest. INTENTIONAL; diagnosed against
      -- the golden.)
      -- (rule:HOW-MANY-FILTER-1 and rule:HOW-MANY-QSORT RETIRED
      -- 2026-08-15 — P3c: both are qsort-book theorems the transfer
      -- now replays at this world; FILTER-1's own arithmetic premise
      -- surfaces above. INTENTIONAL.)
      -- (rule:ORDEREDP-APPEND RETIRED 2026-08-16 — T1+2 sprint P5a: the
      -- IFF-CONCLUSION DECODE class. ACL2 stores this defthm's
      -- `(IFF lhs rhs)` conclusion as an `:EQUIV EQUAL` rewrite rule
      -- because both sides are boolean; `dischargeRuleHyp`'s `routeIff`
      -- RECOMPUTES that normalization, taking each side's two-valuedness
      -- from the EMITTED :TYPE-PRESCRIPTION corollaries (demanded, never
      -- assumed). The hypothesis left the telescope and the pinned type
      -- drops it; the waypoint layer's hand decode
      -- `dis_rule_orderedp_append` was deleted with it. INTENTIONAL;
      -- diagnosed against the golden.)
      EvTrue sortsEqSweepWorld env
        (ap2 "EQUAL" (ap1 "QSORT" (sym "X")) (ap1 "ISORT" (sym "X"))) :=
  ReplayedStatements.replayed_sorting_sorts_equivalent_QSORT_IS_ISORT

#print axioms ReplayedStatements.replayed_sorting_sorts_equivalent_QSORT_IS_ISORT

end ACL2.Tests.SortingPinsEndgame
