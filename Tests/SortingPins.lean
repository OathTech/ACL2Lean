/-
  Tests/SortingPins — STATEMENT PINS for the sorting corpus (equiv-lane arc
  increment 0; audit rec 6, demanded by BOTH pre-merge auditors 2026-07-29).
  THE SCALABLE HOME for per-book statement pins: one section per book, each
  pinning machine-generated replayed statements against types HAND-WRITTEN
  from the ACL2 `.lisp` sources.

  WHY: the certified pipeline's statement derivation (stage 5) reads the
  same untrusted fork emission as the proof — the replayed statement is
  anchored to the `.lisp` source ONLY through pins like these. A pin
  assigns the machine constant (`runBook`'s ReplayedStatements /
  ReplayedTermination output — the exact sweep semantics, kernel-checked and
  axiom-filtered) to an `example` whose TYPE is transcribed from the source
  book, so emission/translation drift in the STATEMENT TERM fails here at
  elaboration. SCOPE LIMIT (audit F5/F9, 2026-07-30): the world constant
  in every pinned type is itself derived from the same untrusted log, so
  drift in an emitted :DEFUN BODY passes these pins — the independent
  world anchor is gen-world (CLAUDE.md stage 5, tracked).

  Sources transcribed (the acl2/ submodule is the canonical copy):
  - acl2/books/sorting/isort.lisp            (insert, isort, orderedp-isort)
  - acl2/books/sorting/qsort.lisp            (qsort, perm-qsort,
                                              true-listp-qsort, how-many-qsort)
  - acl2/books/sorting/convert-perm-to-how-many.lisp
                                             (convert-perm-to-how-many)
  - acl2/books/arithmetic-3/pass1/basic-arithmetic.lisp:109
                                             (fold-consts-in-+)

  HYPOTHESIS discipline: a conditional replayed statement's `cond[…]` hypotheses are
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
    the replayed-statement constants the pins below are stated against. `upTo` the last
    pinned theorem per book: earlier theorems still replay (identical
    replayed-registry state to the sweep) but their independent DP-leaf
    probes are skipped. The expected status LINES (incl. the full `cond[…]`
    sets) are pinned here exactly; drift fails the build before the type
    pins are even reached. -/

elab "sorting_statement_pins_run% " : term => do
  let r1 ← Runner.runBook "pins/sorting/isort" isortLog (upTo := some "HOW-MANY-ISORT")
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
     ("pins/sorting/isort",
      -- (no DISCHARGE suffix here: upTo skips the earlier theorems' DP
      -- probes; the full sweep's golden carries them)
      "    TRUE-LISTP-ISORT → REPLAYED ✓ cond[tp:INSERT]"),
     ("pins/sorting/isort",
      "    HOW-MANY-ISORT → REPLAYED ✓ cond[tp:HOW-MANY, \
rule:FOLD-CONSTS-IN-+, rule:NOT-MEMB-IMPLIES-HOW-MANY-IS-0]"),
     ("pins/sorting/qsort",
      "    PERM-QSORT → REPLAYED ✓ cond[total:PERM-COUNTER-EXAMPLE, total:O<, \
tp:HOW-MANY, tp:ACL2-COUNT, rule:FOLD-CONSTS-IN-+, rule:CONVERT-PERM-TO-HOW-MANY, \
rule:HOW-MANY-QSORT]"),
     ("pins/sorting/qsort",
      "    TRUE-LISTP-QSORT → REPLAYED ✓ cond[total:O<, tp:QSORT, tp:ACL2-COUNT, \
rule:FOLD-CONSTS-IN-+]  [DISCHARGE: Goal:preprocess/type-set-fc ✓ \
cond[total:(QSORT X), tp:QSORT]]"),
     ("pins/sorting/qsort",
      "    ORDEREDP-QSORT → REPLAYED ✓ cond[total:PERM-COUNTER-EXAMPLE, \
total:O<, tp:HOW-MANY, tp:ALL-REL, tp:ACL2-COUNT, rule:FOLD-CONSTS-IN-+, \
rule:CONVERT-PERM-TO-HOW-MANY, rule:HOW-MANY-QSORT, rule:ORDEREDP-APPEND]")]
  for (book, line) in mustHave do
    let some (_, lines) := expected.find? (·.1 == book)
      | throwError "sorting statement pins: unknown book {book}"
    unless lines.any (· == line) do
      throwError "sorting statement pins: {book} lost pinned status line\n  \
        {line}\ngot:\n{"\n".intercalate lines.toList}"
  -- the QSORT termination replayed statement registers no status line; its existence is
  -- asserted here (the type pin below is the content gate)
  unless (← getEnv).contains
      (Name.mkStr2 "ReplayedTermination" "term_pins_sorting_qsort_QSORT") do
    throwError "sorting statement pins: QSORT termination replayed statement was not registered"
  logInfo "sorting statement pins: replay statuses hold (ORDEREDP-ISORT, \
    PERM-QSORT, TRUE-LISTP-QSORT + QSORT termination replayed statement)"
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
  ReplayedStatements.replayed_pins_sorting_isort_ORDEREDP_ISORT

#print axioms ReplayedStatements.replayed_pins_sorting_isort_ORDEREDP_ISORT

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
  ReplayedStatements.replayed_pins_sorting_qsort_PERM_QSORT

#print axioms ReplayedStatements.replayed_pins_sorting_qsort_PERM_QSORT

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
  ReplayedStatements.replayed_pins_sorting_qsort_TRUE_LISTP_QSORT

#print axioms ReplayedStatements.replayed_pins_sorting_qsort_TRUE_LISTP_QSORT

/-! ## The QSORT termination replayed statement (recorded admission waterfall)

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
  ReplayedTermination.term_pins_sorting_qsort_QSORT

#print axioms ReplayedTermination.term_pins_sorting_qsort_QSORT

/-! ## p3-conj-mid-literal (acl2_samples/pattern-tests/p3-conj-mid-literal.lisp)

    The equiv-lane rung-1 flip's STATEMENT PIN (the iff lane's sole green
    instance must provably say what its book says): the ACL2 defthm

      (implies (and (consp it)
                    (not (lexorder x1 (car it)))
                    (ordd (cdr it))
                    (ordd it))
               (or (ordd (ins x1 it))
                   (equal it 'junk)))

    under ACL2's standard translation (`and` → nested IFs, `or` →
    `(IF a a b)`), conditional on ins's emitted TP corollary
    `(consp (ins e x))` (source-true: every branch conses) and the
    ground-zero rule `default-cdr`
    (`(implies (not (consp x)) (equal (cdr x) nil))`). -/

private def p3ConjLog : String :=
  include_str "../acl2_samples/pattern-tests/p3-conj-mid-literal.proof-log"

def p3ConjPinsDev : Development :=
  (((ProofLog.parse p3ConjLog).toOption.bind
    fun l => (ClauseTree.buildDevelopment l).toOption)).getD .done

derive_world p3ConjPinsWorld from p3ConjPinsDev

elab "p3_conj_statement_pin_run% " : term => do
  let r ← Runner.runBook "pins/p3-conj" p3ConjLog none
  unless r.integrityFails.isEmpty do
    throwError "p3-conj statement pin: integrity failures \
      {r.integrityFails.toList}"
  unless r.lines.any (·.startsWith
      "    ORDD-INS-MID → REPLAYED ✓ cond[tp:INS, rule:DEFAULT-CDR]") do
    throwError "p3-conj statement pin: lost the pinned status prefix; got:\n\
      {"\n".intercalate r.lines.toList}"
  logInfo "p3-conj statement pin: replay status holds (ORDD-INS-MID)"
  return mkConst ``True.intro

set_option maxHeartbeats 0 in
def p3ConjStatementPinRun : True := p3_conj_statement_pin_run%

/-- `rule:<thm>` with ONE truthiness hypothesis (the conditional-rewrite
    hypothesis shape, `mkRuleHypType`). -/
private def ruleEqHyp1 (w : World) (hyp lhs rhs : SExpr) : Prop :=
  ∀ env' : Env, EvTrue w env' hyp →
    ∃ N, ∀ f ≥ N, evalOpt f w env' lhs = evalOpt f w env' rhs

/-- `(not x)` term. -/
private def notOf (x : SExpr) : SExpr := .cons (sym "NOT") (.cons x .nil)

example :
    ∀ (env : Env),
      tpPred2 p3ConjPinsWorld "INS" Logic.consp →
      -- default-cdr: (implies (not (consp x)) (equal (cdr x) nil))
      ruleEqHyp1 p3ConjPinsWorld
        (notOf (ap1 "CONSP" (sym "X")))
        (ap1 "CDR" (sym "X"))
        (qt .nil) →
      EvTrue p3ConjPinsWorld env
        (ap2 "IMPLIES"
          (ap3 "IF" (ap1 "CONSP" (sym "IT"))
            (ap3 "IF" (notOf (ap2 "LEXORDER" (sym "X1") (ap1 "CAR" (sym "IT"))))
              (ap3 "IF" (ap1 "ORDD" (ap1 "CDR" (sym "IT")))
                (ap1 "ORDD" (sym "IT"))
                (qt .nil))
              (qt .nil))
            (qt .nil))
          (ap3 "IF" (ap1 "ORDD" (ap2 "INS" (sym "X1") (sym "IT")))
            (ap1 "ORDD" (ap2 "INS" (sym "X1") (sym "IT")))
            (ap2 "EQUAL" (sym "IT") (qt (sym "JUNK"))))) :=
  ReplayedStatements.replayed_pins_p3_conj_ORDD_INS_MID

#print axioms ReplayedStatements.replayed_pins_p3_conj_ORDD_INS_MID

/-! ## ORDEREDP-QSORT (acl2/books/sorting/qsort.lisp:115) — the perm-lane
    headline row (G2 rung 2, 2026-07-30): the first green row whose replay
    consumes a USER-equivalence rewrite (PERM-QSORT under :EQUIV PERM at
    ALL-REL's defcong-licensed arg 2). The `rule:PERM-QSORT` and
    `cong:PERM-IMPLIES-EQUAL-ALL-REL-2` hypotheses are DISCHARGED from
    their replayed statements, so neither appears below — the kept set is the
    pre-existing debt classes only. -/

/-- `tp:<fn>` (ternary), boolean corollary
    `(if (equal v 't) 't (equal v 'nil))` — ALL-REL's emitted TP. -/
private def tpBool3 (w : World) (fn : String) : Prop :=
  ∀ (env' : Env) (a0 a1 a2 v : SExpr),
    (∃ N, ∀ f ≥ N, evalOpt f w env' (ap3 fn a0 a1 a2) = some v) →
    (bif Logic.toBool (Logic.equal v SExpr.t) then SExpr.t
     else Logic.equal v SExpr.nil) = SExpr.t

/-- PIN the machine-generated statement of `ORDEREDP-QSORT`: the mirror of
    the ACL2 defthm `(orderedp (qsort x))`, conditional on
    - totality of `perm-counter-example` and `o<`,
    - the emitted TP corollaries of `how-many`/`acl2-count` (non-negative
      integers — source-true: both count) and `all-rel` (boolean —
      source-true: every branch returns `t`/`nil`/a recursive call),
    - the cited rules `fold-consts-in-+`, `convert-perm-to-how-many`,
      `how-many-qsort` (as on PERM-QSORT's pin), and `orderedp-append`
      (qsort.lisp:85 — the IFF-stated defthm, stored with ACL2's
      iff→equal strengthening; hypothesis `(orderedp a)`, rhs the
      `and`-translation — kept because its own replay currently fails at
      the LEXORDER-TRANSITIVE type-alist relief frontier).
      SOURCE-CHECK of the strengthening (audit F7 — the `equal` form is
      NOT derivable from the source text alone; it needs both sides
      boolean): `orderedp` (qsort.lisp) returns `t`, `nil`, or a
      recursive call in every branch, so its range is {t, nil} by
      induction; `all-rel` likewise (`t`/`nil`/recursive). Hence
      `(iff a b) ⇔ (equal a b)` on these terms and the stored rule's
      strengthening is truthful. A drifted defun that made either
      non-boolean would make this kept hypothesis unprovable — vacuity
      risk documented, discharged when the relief class lands. -/
example :
    ∀ (env : Env),
      totalHyp2 qsortPinsWorld "PERM-COUNTER-EXAMPLE" →
      totalHyp2 qsortPinsWorld "O<" →
      tpNonnegInt2 qsortPinsWorld "HOW-MANY" →
      tpBool3 qsortPinsWorld "ALL-REL" →
      tpNonnegInt1 qsortPinsWorld "ACL2-COUNT" →
      foldConstsHyp qsortPinsWorld →
      ruleEqHyp qsortPinsWorld
        (ap2 "PERM" (sym "X") (sym "Y"))
        (ap2 "EQUAL"
          (ap2 "HOW-MANY" (ap2 "PERM-COUNTER-EXAMPLE" (sym "X") (sym "Y")) (sym "X"))
          (ap2 "HOW-MANY" (ap2 "PERM-COUNTER-EXAMPLE" (sym "X") (sym "Y")) (sym "Y"))) →
      ruleEqHyp qsortPinsWorld
        (ap2 "HOW-MANY" (sym "E") (ap1 "QSORT" (sym "X")))
        (ap2 "HOW-MANY" (sym "E") (sym "X")) →
      ruleEqHyp1 qsortPinsWorld
        (ap1 "ORDEREDP" (sym "A"))
        (ap1 "ORDEREDP" (ap2 "BINARY-APPEND" (sym "A") (ap2 "CONS" (sym "E") (sym "B"))))
        (ap3 "IF" (ap1 "ORDEREDP" (sym "B"))
          (ap3 "IF" (ap3 "ALL-REL" (qt (sym "LTE")) (sym "A") (sym "E"))
            (ap3 "ALL-REL" (qt (sym "GTE")) (sym "B") (sym "E"))
            (qt .nil))
          (qt .nil)) →
      EvTrue qsortPinsWorld env (ap1 "ORDEREDP" (ap1 "QSORT" (sym "X"))) :=
  ReplayedStatements.replayed_pins_sorting_qsort_ORDEREDP_QSORT

#print axioms ReplayedStatements.replayed_pins_sorting_qsort_ORDEREDP_QSORT

/-! ## p5-or-shape-flipped (acl2_samples/pattern-tests/p5-or-shape-flipped.lisp)

    The iff-lane's second green instance gets its STATEMENT PIN: the ACL2
    defthm

      (implies (and (consp x) (equal (car x) e) (dupp x))
               (or (equal x 'junk) (dupp (cons e x))))

    under ACL2's standard translation (`and` → nested IFs, `or` →
    `(IF a a b)`), UNCONDITIONAL — no hypotheses at all. -/

private def p5FlipLog : String :=
  include_str "../acl2_samples/pattern-tests/p5-or-shape-flipped.proof-log"

def p5FlipPinsDev : Development :=
  (((ProofLog.parse p5FlipLog).toOption.bind
    fun l => (ClauseTree.buildDevelopment l).toOption)).getD .done

derive_world p5FlipPinsWorld from p5FlipPinsDev

/-! ## p7-cong-collapse (acl2_samples/pattern-tests/p7-cong-collapse.lisp)

    Rung 2's decorrelated validation book gets STATEMENT PINS for the two
    theorems that carry its meaning:
    - `P7-TARGET` — `(equal (ln (dub x)) (ln x))`, the congruence-collapse
      instance itself;
    - `SAME-LN-IMPLIES-EQUAL-LN-1` — the defcong
      `(defcong same-ln equal (ln x) 1)`, whose ACL2 macro expansion is the
      defthm `(implies (same-ln x x-equiv) (equal (ln x) (ln x-equiv)))` —
      pinned because this formula is EXACTLY what `congSpecOfFormula?`
      parses into the consumed congruence license (a drift here would move
      the license itself).
    Both conditional on ln's emitted non-negative-integer TP corollary
    (source-true: ln counts). -/

private def p7CongLog : String :=
  include_str "../acl2_samples/pattern-tests/p7-cong-collapse.proof-log"

def p7CongPinsDev : Development :=
  (((ProofLog.parse p7CongLog).toOption.bind
    fun l => (ClauseTree.buildDevelopment l).toOption)).getD .done

derive_world p7CongPinsWorld from p7CongPinsDev

elab "pattern_statement_pins_run% " : term => do
  let r5 ← Runner.runBook "pins/p5-flip" p5FlipLog none
  let r7 ← Runner.runBook "pins/p7-cong" p7CongLog none
  unless r5.integrityFails.isEmpty && r7.integrityFails.isEmpty do
    throwError "pattern statement pins: integrity failures \
      {r5.integrityFails.toList ++ r7.integrityFails.toList}"
  let mustHave : List (String × Array String × String) :=
    [("pins/p5-flip", r5.lines, "    DUPP-REP-MID → REPLAYED ✓"),
     ("pins/p7-cong", r7.lines, "    P7-TARGET → REPLAYED ✓ cond[tp:LN]"),
     ("pins/p7-cong", r7.lines,
      "    SAME-LN-IMPLIES-EQUAL-LN-1 → REPLAYED ✓ cond[tp:LN]")]
  for (book, lines, line) in mustHave do
    unless lines.any (· == line) do
      throwError "pattern statement pins: {book} lost pinned status line\n  \
        {line}\ngot:\n{"\n".intercalate lines.toList}"
  logInfo "pattern statement pins: replay statuses hold (DUPP-REP-MID, \
    P7-TARGET, SAME-LN-IMPLIES-EQUAL-LN-1)"
  return mkConst ``True.intro

set_option maxHeartbeats 0 in
def patternStatementPinsRun : True := pattern_statement_pins_run%

/-- PIN the machine-generated statement of `DUPP-REP-MID` (p5): the mirror
    of the book's defthm, unconditional. -/
example :
    ∀ (env : Env),
      EvTrue p5FlipPinsWorld env
        (ap2 "IMPLIES"
          (ap3 "IF" (ap1 "CONSP" (sym "X"))
            (ap3 "IF" (ap2 "EQUAL" (ap1 "CAR" (sym "X")) (sym "E"))
              (ap1 "DUPP" (sym "X"))
              (qt .nil))
            (qt .nil))
          (ap3 "IF" (ap2 "EQUAL" (sym "X") (qt (sym "JUNK")))
            (ap2 "EQUAL" (sym "X") (qt (sym "JUNK")))
            (ap1 "DUPP" (ap2 "CONS" (sym "E") (sym "X"))))) :=
  ReplayedStatements.replayed_pins_p5_flip_DUPP_REP_MID

#print axioms ReplayedStatements.replayed_pins_p5_flip_DUPP_REP_MID

/-- PIN the machine-generated statement of `P7-TARGET`:
    `(equal (ln (dub x)) (ln x))` under ln's non-negative-integer TP. -/
example :
    ∀ (env : Env),
      tpNonnegInt1 p7CongPinsWorld "LN" →
      EvTrue p7CongPinsWorld env
        (ap2 "EQUAL" (ap1 "LN" (ap1 "DUB" (sym "X"))) (ap1 "LN" (sym "X"))) :=
  ReplayedStatements.replayed_pins_p7_cong_P7_TARGET

#print axioms ReplayedStatements.replayed_pins_p7_cong_P7_TARGET

/-- PIN the machine-generated statement of `SAME-LN-IMPLIES-EQUAL-LN-1`
    (the defcong's macro-expanded defthm). -/
example :
    ∀ (env : Env),
      tpNonnegInt1 p7CongPinsWorld "LN" →
      EvTrue p7CongPinsWorld env
        (ap2 "IMPLIES"
          (ap2 "SAME-LN" (sym "X") (sym "X-EQUIV"))
          (ap2 "EQUAL" (ap1 "LN" (sym "X")) (ap1 "LN" (sym "X-EQUIV")))) :=
  ReplayedStatements.replayed_pins_p7_cong_SAME_LN_IMPLIES_EQUAL_LN_1

#print axioms ReplayedStatements.replayed_pins_p7_cong_SAME_LN_IMPLIES_EQUAL_LN_1

/-! ## TRUE-LISTP-ISORT + HOW-MANY-ISORT (isort.lisp:26, 29) — the isort
    book's remaining green rows (validator/lifter arc W1 item 3: the
    survey's near-zero-marginal-cost pins; completes the book). -/

/-- PIN `TRUE-LISTP-ISORT`: `(true-listp (isort x))`, conditional on
    insert's `(consp (insert e x))` TP (source-true: every branch conses). -/
example :
    ∀ (env : Env),
      tpPred2 isortPinsWorld "INSERT" Logic.consp →
      EvTrue isortPinsWorld env (ap1 "TRUE-LISTP" (ap1 "ISORT" (sym "X"))) :=
  ReplayedStatements.replayed_pins_sorting_isort_TRUE_LISTP_ISORT

#print axioms ReplayedStatements.replayed_pins_sorting_isort_TRUE_LISTP_ISORT

/-- PIN `HOW-MANY-ISORT`: `(equal (how-many e (isort x)) (how-many e x))`,
    conditional on how-many's non-negative-integer TP, fold-consts-in-+,
    and `not-memb-implies-how-many-is-0`
    (`(implies (not (memb a x)) (equal (how-many a x) 0))` — transcribed
    from its book; kept because its own replay is cross-book). -/
example :
    ∀ (env : Env),
      tpNonnegInt2 isortPinsWorld "HOW-MANY" →
      foldConstsHyp isortPinsWorld →
      ruleEqHyp1 isortPinsWorld
        (notOf (ap2 "MEMB" (sym "A") (sym "X")))
        (ap2 "HOW-MANY" (sym "A") (sym "X"))
        (qt (.atom (.number (.int 0)))) →
      EvTrue isortPinsWorld env
        (ap2 "EQUAL"
          (ap2 "HOW-MANY" (sym "E") (ap1 "ISORT" (sym "X")))
          (ap2 "HOW-MANY" (sym "E") (sym "X"))) :=
  ReplayedStatements.replayed_pins_sorting_isort_HOW_MANY_ISORT

#print axioms ReplayedStatements.replayed_pins_sorting_isort_HOW_MANY_ISORT

end ACL2.Tests.SortingPins
