/-
  Tests/SortingPins — STATEMENT PINS for the sorting corpus (equiv-lane arc
  increment 0; audit rec 6, demanded by BOTH pre-merge auditors 2026-07-29).
  THE SCALABLE HOME for per-book statement pins: one section per book, each
  pinning machine-generated mirror statements against types HAND-WRITTEN
  from the ACL2 `.lisp` sources.

  WHY: the certified pipeline's statement derivation (stage 5) reads the
  same untrusted fork emission as the proof — the mirror statement is
  anchored to the `.lisp` source ONLY through pins like these. A pin
  assigns the machine constant (`runBook`'s CoverageMirrors /
  TerminationMirrors output — the exact sweep semantics, kernel-checked and
  axiom-filtered) to an `example` whose TYPE is transcribed from the source
  book, so any emission/translation drift that changes WHAT IS PROVED fails
  here at elaboration.

  Sources transcribed (the acl2/ submodule is the canonical copy):
  - acl2/books/sorting/isort.lisp            (insert, isort, orderedp-isort)
  - acl2/books/sorting/qsort.lisp            (qsort, perm-qsort,
                                              true-listp-qsort, how-many-qsort)
  - acl2/books/sorting/convert-perm-to-how-many.lisp
                                             (convert-perm-to-how-many)
  - acl2/books/arithmetic-3/pass1/basic-arithmetic.lisp:109
                                             (fold-consts-in-+)

  HYPOTHESIS discipline: a conditional mirror's `cond[…]` hypotheses are
  replay artifacts (emitted TP corollaries, totality of world fns, cited
  rules), not source text — each is transcribed below in full and
  source-checked for truthfulness (e.g. `tp:INSERT` = "insert always
  returns a cons": every branch of the source defun conses). Pinning them
  guards the other weakening direction: a drifted hypothesis set (extra or
  contradictory premises) fails the example, and the run elab pins the
  exact `cond[…]` status lines besides.
-/
import ACL2Lean.Replay.Runner

namespace ACL2.Tests.SortingPins

open Lean ACL2 ACL2.Replay ACL2.Replay.Driver

private def isortLog : String := include_str "../acl2_samples/sorting/isort.proof-log"
private def qsortLog : String := include_str "../acl2_samples/sorting/qsort.proof-log"

/-- The parsed isort development — the ONLY input is the log (as in the sweep). -/
def isortPinsDev : Development :=
  (((ProofLog.parse isortLog).toOption.bind
    fun l => (ClauseTree.buildDevelopment l).toOption)).getD .done

/-- The parsed qsort development. -/
def qsortPinsDev : Development :=
  (((ProofLog.parse qsortLog).toOption.bind
    fun l => (ClauseTree.buildDevelopment l).toOption)).getD .done

derive_world isortPinsWorld from isortPinsDev
derive_world qsortPinsWorld from qsortPinsDev

/-! ## The replay run — the exact sweep semantics (`runBook`), registering
    the mirror constants the pins below are stated against. `upTo` the last
    pinned theorem per book: earlier theorems still replay (identical
    mirror-registry state to the sweep) but their independent DP-leaf
    probes are skipped. The expected status LINES (incl. the full `cond[…]`
    sets) are pinned here exactly; drift fails the build before the type
    pins are even reached. -/

elab "sorting_statement_pins_run% " : term => do
  let r1 ← Runner.runBook "pins/sorting/isort" isortLog (upTo := some "ORDEREDP-ISORT")
  let r2 ← Runner.runBook "pins/sorting/qsort" qsortLog (upTo := some "TRUE-LISTP-QSORT")
  unless r1.integrityFails.isEmpty && r2.integrityFails.isEmpty do
    throwError "sorting statement pins: integrity failures \
      {r1.integrityFails.toList ++ r2.integrityFails.toList}"
  let expected : List (String × Array String) :=
    [("pins/sorting/isort", r1.lines),
     ("pins/sorting/qsort", r2.lines)]
  let mustHave : List (String × String) :=
    [("pins/sorting/isort",
      "    ORDEREDP-ISORT → REPLAYED ✓ cond[tp:INSERT]"),
     ("pins/sorting/qsort",
      "    PERM-QSORT → REPLAYED ✓ cond[total:PERM-COUNTER-EXAMPLE, total:O<, \
tp:HOW-MANY, tp:ACL2-COUNT, rule:FOLD-CONSTS-IN-+, rule:CONVERT-PERM-TO-HOW-MANY, \
rule:HOW-MANY-QSORT]"),
     ("pins/sorting/qsort",
      "    TRUE-LISTP-QSORT → REPLAYED ✓ cond[total:O<, tp:QSORT, tp:ACL2-COUNT, \
rule:FOLD-CONSTS-IN-+]  [DISCHARGE: Goal:preprocess/type-set-fc ✓ \
cond[total:(QSORT X), tp:QSORT]]")]
  for (book, line) in mustHave do
    let some (_, lines) := expected.find? (·.1 == book)
      | throwError "sorting statement pins: unknown book {book}"
    unless lines.any (· == line) do
      throwError "sorting statement pins: {book} lost pinned status line\n  \
        {line}\ngot:\n{"\n".intercalate lines.toList}"
  -- the QSORT termination mirror registers no status line; its existence is
  -- asserted here (the type pin below is the content gate)
  unless (← getEnv).contains
      (Name.mkStr2 "TerminationMirrors" "term_pins_sorting_qsort_QSORT") do
    throwError "sorting statement pins: QSORT termination mirror was not registered"
  logInfo "sorting statement pins: replay statuses hold (ORDEREDP-ISORT, \
    PERM-QSORT, TRUE-LISTP-QSORT + QSORT termination mirror)"
  return mkConst ``True.intro

-- unlimited at the command like the coverage sweep — the harness enforces
-- REAL per-theorem budgets internally (withRealMaxHeartbeats)
set_option maxHeartbeats 0 in
def sortingStatementPinsRun : True := sorting_statement_pins_run%

/-! ## Term helpers (transcription vocabulary) -/

private def sym (n : String) : SExpr := .atom (.symbol { name := n })
private def ap1 (f : String) (a : SExpr) : SExpr := .cons (sym f) (.cons a .nil)
private def ap2 (f : String) (a b : SExpr) : SExpr := .cons (sym f) (.cons a (.cons b .nil))
private def ap3 (f : String) (a b c : SExpr) : SExpr :=
  .cons (sym f) (.cons a (.cons b (.cons c .nil)))
/-- `(QUOTE e)`. -/
private def qt (e : SExpr) : SExpr := .cons (sym "QUOTE") (.cons e .nil)

/-- ACL2's translation of a `(syntaxp (quotep v))` hypothesis:
    `(SYNP 'NIL '(SYNTAXP (QUOTEP v)) '(IF (QUOTEP v) 'T 'NIL))`. -/
private def synpQuotep (v : String) : SExpr :=
  ap3 "SYNP" (qt .nil)
    (qt (ap1 "SYNTAXP" (ap1 "QUOTEP" (sym v))))
    (qt (ap3 "IF" (ap1 "QUOTEP" (sym v)) (qt (sym "T")) (qt .nil)))

/-! ## Hypothesis shapes (the `cond[…]` classes, spelled out once)

    Each is the exact machine shape of one condition class; the per-pin
    instantiations below say WHICH fn/rule and are source-checked there. -/

/-- `total:<fn>` for a unary world fn: if the argument converges, the
    application converges. -/
private def totalHyp1 (w : World) (fn : String) : Prop :=
  ∀ (env' : Env) (a0 : SExpr),
    (∃ N v, ∀ f ≥ N, evalOpt f w env' a0 = some v) →
    ∃ N v, ∀ f ≥ N, evalOpt f w env' (ap1 fn a0) = some v

/-- `total:<fn>` for a binary world fn. -/
private def totalHyp2 (w : World) (fn : String) : Prop :=
  ∀ (env' : Env) (a0 a1 : SExpr),
    (∃ N v, ∀ f ≥ N, evalOpt f w env' a0 = some v) →
    (∃ N v, ∀ f ≥ N, evalOpt f w env' a1 = some v) →
    ∃ N v, ∀ f ≥ N, evalOpt f w env' (ap2 fn a0 a1) = some v

/-- `tp:<fn>` (unary), emitted corollary "a non-negative integer":
    `(and (integerp v) (not (< v 0)))` at the value level. -/
private def tpNonnegInt1 (w : World) (fn : String) : Prop :=
  ∀ (env' : Env) (a0 v : SExpr),
    (∃ N, ∀ f ≥ N, evalOpt f w env' (ap1 fn a0) = some v) →
    (bif Logic.toBool (Logic.integerp v) then
      Logic.not (Logic.lt v (.atom (.number (.int 0))))
    else SExpr.nil) = SExpr.t

/-- `tp:<fn>` (binary), non-negative-integer corollary. -/
private def tpNonnegInt2 (w : World) (fn : String) : Prop :=
  ∀ (env' : Env) (a0 a1 v : SExpr),
    (∃ N, ∀ f ≥ N, evalOpt f w env' (ap2 fn a0 a1) = some v) →
    (bif Logic.toBool (Logic.integerp v) then
      Logic.not (Logic.lt v (.atom (.number (.int 0))))
    else SExpr.nil) = SExpr.t

/-- `tp:<fn>` (unary), single-predicate corollary (e.g. `true-listp`). -/
private def tpPred1 (w : World) (fn : String) (pred : SExpr → SExpr) : Prop :=
  ∀ (env' : Env) (a0 v : SExpr),
    (∃ N, ∀ f ≥ N, evalOpt f w env' (ap1 fn a0) = some v) →
    pred v = SExpr.t

/-- `tp:<fn>` (binary), single-predicate corollary (e.g. `consp`). -/
private def tpPred2 (w : World) (fn : String) (pred : SExpr → SExpr) : Prop :=
  ∀ (env' : Env) (a0 a1 v : SExpr),
    (∃ N, ∀ f ≥ N, evalOpt f w env' (ap2 fn a0 a1) = some v) →
    pred v = SExpr.t

/-- `rule:<thm>` for an unconditional rewrite: lhs and rhs evaluate
    identically in every environment (over the rule's own variables, free
    in the term and bound by the env quantifier). -/
private def ruleEqHyp (w : World) (lhs rhs : SExpr) : Prop :=
  ∀ env' : Env, ∃ N, ∀ f ≥ N, evalOpt f w env' lhs = evalOpt f w env' rhs

/-- `rule:FOLD-CONSTS-IN-+` (arithmetic-3/pass1/basic-arithmetic.lisp:109):
    `(implies (and (syntaxp (quotep x)) (syntaxp (quotep y)))
              (equal (+ x (+ y z)) (+ (+ x y) z)))`
    — the two `syntaxp` hypotheses as truthy SYNP terms, exactly as ACL2
    translates them. -/
private def foldConstsHyp (w : World) : Prop :=
  ∀ env' : Env,
    EvTrue w env' (synpQuotep "X") →
    EvTrue w env' (synpQuotep "Y") →
    ∃ N, ∀ f ≥ N,
      evalOpt f w env' (ap2 "BINARY-+" (sym "X") (ap2 "BINARY-+" (sym "Y") (sym "Z"))) =
      evalOpt f w env' (ap2 "BINARY-+" (ap2 "BINARY-+" (sym "X") (sym "Y")) (sym "Z"))

/-! ## isort book (acl2/books/sorting/isort.lisp) -/

/-- PIN the machine-generated statement of `ORDEREDP-ISORT`: the mirror of
    the ACL2 defthm `(orderedp (isort x))`, conditional on exactly one
    hypothesis — insert's emitted TP corollary `(consp (insert e x))`
    (source-true: every branch of the `insert` defun is a `cons`). -/
example :
    ∀ (env : Env),
      tpPred2 isortPinsWorld "INSERT" Logic.consp →
      EvTrue isortPinsWorld env (ap1 "ORDEREDP" (ap1 "ISORT" (sym "X"))) :=
  CoverageMirrors.mirror_pins_sorting_isort_ORDEREDP_ISORT

#print axioms CoverageMirrors.mirror_pins_sorting_isort_ORDEREDP_ISORT

/-! ## qsort book (acl2/books/sorting/qsort.lisp) -/

/-- PIN the machine-generated statement of `PERM-QSORT`: the mirror of the
    ACL2 defthm `(perm (qsort x) x)`, conditional on
    - totality of `perm-counter-example` and `o<` (world fns whose totality
      is not yet auto-discharged on this row),
    - the emitted non-negative-integer TP corollaries of `how-many` and
      `acl2-count` (source-true: both count),
    - the cited rules `fold-consts-in-+` (arithmetic-3),
      `convert-perm-to-how-many` and `how-many-qsort` (transcribed from
      their books; `how-many-qsort` is a hypothesis because its own replay
      currently fails at the J6 solidify frontier — no mirror to apply). -/
example :
    ∀ (env : Env),
      totalHyp2 qsortPinsWorld "PERM-COUNTER-EXAMPLE" →
      totalHyp2 qsortPinsWorld "O<" →
      tpNonnegInt2 qsortPinsWorld "HOW-MANY" →
      tpNonnegInt1 qsortPinsWorld "ACL2-COUNT" →
      foldConstsHyp qsortPinsWorld →
      -- convert-perm-to-how-many:
      --   (equal (perm x y) (equal (how-many (perm-counter-example x y) x)
      --                            (how-many (perm-counter-example x y) y)))
      ruleEqHyp qsortPinsWorld
        (ap2 "PERM" (sym "X") (sym "Y"))
        (ap2 "EQUAL"
          (ap2 "HOW-MANY" (ap2 "PERM-COUNTER-EXAMPLE" (sym "X") (sym "Y")) (sym "X"))
          (ap2 "HOW-MANY" (ap2 "PERM-COUNTER-EXAMPLE" (sym "X") (sym "Y")) (sym "Y"))) →
      -- how-many-qsort: (equal (how-many e (qsort x)) (how-many e x))
      ruleEqHyp qsortPinsWorld
        (ap2 "HOW-MANY" (sym "E") (ap1 "QSORT" (sym "X")))
        (ap2 "HOW-MANY" (sym "E") (sym "X")) →
      EvTrue qsortPinsWorld env (ap2 "PERM" (ap1 "QSORT" (sym "X")) (sym "X")) :=
  CoverageMirrors.mirror_pins_sorting_qsort_PERM_QSORT

#print axioms CoverageMirrors.mirror_pins_sorting_qsort_PERM_QSORT

/-- PIN the machine-generated statement of `TRUE-LISTP-QSORT`: the mirror
    of the ACL2 defthm `(true-listp (qsort x))`, conditional on `o<`
    totality, qsort's own emitted TP corollary `(true-listp (qsort x))`
    (the recursive TP — consumed on IH positions, NOT a circular discharge
    of the conclusion: the mirror still replays the tree), acl2-count's
    non-negative-integer TP, and `fold-consts-in-+`. -/
example :
    ∀ (env : Env),
      totalHyp2 qsortPinsWorld "O<" →
      tpPred1 qsortPinsWorld "QSORT" Logic.trueListp →
      tpNonnegInt1 qsortPinsWorld "ACL2-COUNT" →
      foldConstsHyp qsortPinsWorld →
      EvTrue qsortPinsWorld env (ap1 "TRUE-LISTP" (ap1 "QSORT" (sym "X"))) :=
  CoverageMirrors.mirror_pins_sorting_qsort_TRUE_LISTP_QSORT

#print axioms CoverageMirrors.mirror_pins_sorting_qsort_TRUE_LISTP_QSORT

/-! ## The QSORT termination mirror (recorded admission waterfall)

    `qsort` (source above) has exactly two recursive call sites, both in
    the final `cond` branch — ruled by `(not (endp x))` and
    `(not (endp (cdr x)))`:
      `(qsort (filter 'LT  (cdr x) (car x)))`
      `(qsort (filter 'GTE (cdr x) (car x)))`
    The admission obligation ACL2 records is, per call site, the raw
    termination clause "some ruler fails OR the argument's acl2-count
    decreases", i.e. `(if (endp x) 't (if (endp (cdr x)) 't (o< …)))`,
    conjoined over the two sites ((if c₁ c₂ 'nil) = (and c₁ c₂); the
    GTE-site clause first, in ACL2's recorded order). The mirror is the
    replayed waterfall's root — conditional on the same `o<` totality,
    `acl2-count` TP, and `fold-consts-in-+` classes as above. -/

/-- `(if (endp x) 't (if (endp (cdr x)) 't (o< (acl2-count (filter 'fn (cdr x) (car x))) (acl2-count x))))` -/
private def qsortDecreaseClause (fn : String) : SExpr :=
  ap3 "IF" (ap1 "ENDP" (sym "X")) (qt (sym "T"))
    (ap3 "IF" (ap1 "ENDP" (ap1 "CDR" (sym "X"))) (qt (sym "T"))
      (ap2 "O<"
        (ap1 "ACL2-COUNT" (ap3 "FILTER" (qt (sym fn)) (ap1 "CDR" (sym "X")) (ap1 "CAR" (sym "X"))))
        (ap1 "ACL2-COUNT" (sym "X"))))

example :
    ∀ (env : Env),
      totalHyp2 qsortPinsWorld "O<" →
      tpNonnegInt1 qsortPinsWorld "ACL2-COUNT" →
      foldConstsHyp qsortPinsWorld →
      EvTrue qsortPinsWorld env
        (ap3 "IF" (qsortDecreaseClause "GTE") (qsortDecreaseClause "LT") (qt .nil)) :=
  TerminationMirrors.term_pins_sorting_qsort_QSORT

#print axioms TerminationMirrors.term_pins_sorting_qsort_QSORT

end ACL2.Tests.SortingPins
