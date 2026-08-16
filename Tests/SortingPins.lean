/-
  Tests/SortingPins — STATEMENT PINS for the sorting corpus (equiv-lane arc
  increment 0; audit rec 6, demanded by BOTH pre-merge auditors 2026-07-29).
  THE SCALABLE HOME for per-book statement pins: one section per book, each
  pinning machine-generated replayed statements against types HAND-WRITTEN
  from the ACL2 `.lisp` sources.

  ROLE (relabeled under the two-category ruling, 2026-08-12): these are
  REGRESSION CANARIES, not trust anchors. The replayed layer is the
  METRIC, never the product, so nothing here carries product trust —
  that enters only at the NorthStar layer's user-supplied definitions.
  What the pins DETECT is silent statement-content drift: the coverage
  golden watches row STATUS, not statement CONTENT, so a fork/parser/
  recapture change that silently alters WHAT a row replays would pass
  the golden — and fail here. They fire exactly when a pipeline change
  alters statements, which is exactly when attention is warranted.

  ORIGINAL RATIONALE (kept as history; the trust half is superseded):
  the certified pipeline's statement derivation (stage 5) reads the
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
                                              true-listp-qsort; audit
                                              2026-07-31 §10: how-many-qsort
                                              has NO pin — removed from this
                                              list, statement anchored via
                                              the waypoint instead)
  - acl2/books/sorting/convert-perm-to-how-many.lisp
                                             (convert-perm-to-how-many)
  - acl2/books/arithmetic-3/pass1/basic-arithmetic.lisp:109
                                             (fold-consts-in-+)
  - acl2/books/sorting/perm.lisp             (perm-cons)
  - acl2/books/sorting/ordered-perms.lisp    (orderedp-rm)
  - acl2/books/sorting/msort.lisp            (orderedp-msort)
  - acl2/books/sorting/bsort.lisp            (how-many-bnext)

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
import ACL2Lean.DevLoad
import Tests.Coverage.BSsortsEquivalent

namespace ACL2.Tests.SortingPins

open Lean ACL2 ACL2.Replay ACL2.Replay.Driver

private def isortLog : String := include_str "../acl2_samples/sorting/isort.proof-log"
private def qsortLog : String := include_str "../acl2_samples/sorting/qsort.proof-log"
private def convertPermLog : String :=
  include_str "../acl2_samples/sorting/convert-perm-to-how-many.proof-log"
-- P4 completion (close-out arc Phase 7, 2026-08-05): one pin per remaining
-- row-bearing sweep book. sorts-equivalent and equisort are EXCLUDED by the
-- MDD arc-exit amendment (their only rows are the three capstones / the
-- abstract-world re-proofs, deferred to the follow-on arc — no green row
-- exists to pin).
private def permLog : String := include_str "../acl2_samples/sorting/perm.proof-log"
private def orderedPermsLog : String :=
  include_str "../acl2_samples/sorting/ordered-perms.proof-log"
private def msortLog : String := include_str "../acl2_samples/sorting/msort.proof-log"
private def bsortLog : String := include_str "../acl2_samples/sorting/bsort.proof-log"

/-- The committed sweep golden — the pins' MECHANICAL LINK to the sweep
    (audit F3): every pinned status line must be a PREFIX of some golden
    line (prefix, not equality: the pin runs skip non-target theorems'
    independent DP probes, so pinned lines omit `[DISCHARGE: …]`
    suffixes). Without this, a future sweep-side discharge the pins'
    narrower tree offer cannot reproduce would silently keep the pins
    green against a stale expectation. -/
private def sweepGolden : String := include_str "driver-coverage.golden"

/-- The convert-perm-to-how-many dependency trees (2a): the pins' runBook
    calls offer them like the sweep's prior-book accumulation, so the
    pinned rows match the sweep exactly. SCOPE: only this dependency's
    trees are offered (the sweep also accumulates perm/isort/… trees, but
    per the golden no isort/qsort row consumes any of those — the exact
    pinned status lines below are the drift detector for that claim). -/
def convertPermPinsTrees : List (String × ClauseProof) :=
  (((ProofLog.parse convertPermLog).toOption.bind
    fun l => (ClauseTree.buildDevelopment l).toOption)).map
    Runner.bookTrees |>.getD []

/-- The convert-perm DEVELOPMENT for the WP5 cross-book D1 transfer
    (T1+2 sprint P3c collection, 2026-08-15): the pins' qsort run gets
    the same dep development the sweep's crossDevs channel carries, so
    the pinned rows match the sweep's transfer-era truth (the pinned
    status lines below remain the drift detector). SCOPE: only this
    dependency, per the trees note above. -/
def convertPermPinsDevs : List (String × Development) :=
  -- (the perm dev rides along because PERM-TLFIX's transfer replay
  -- consumes the replayed PERM-IS-AN-EQUIVALENCE cross-book — the
  -- sweep's accumulated crossDevs carry it; the pins mirror that
  -- exactly and nothing more.)
  (match (ProofLog.parse permLog).toOption.bind
      fun l => (ClauseTree.buildDevelopment l).toOption with
   | some d => [("sorting/perm", d)]
   | none => []) ++
  (match (ProofLog.parse convertPermLog).toOption.bind
      fun l => (ClauseTree.buildDevelopment l).toOption with
   | some d => [("sorting/convert-perm-to-how-many", d)]
   | none => [])

/-- The parsed isort development — the ONLY input is the log (as in the sweep). -/
def isortPinsDev : Development :=
  load_development% isortLog

/-- The parsed qsort development. -/
def qsortPinsDev : Development :=
  load_development% qsortLog

/-- The parsed perm development. -/
def permPinsDev : Development :=
  load_development% permLog

/-- The parsed ordered-perms development. -/
def orderedPermsPinsDev : Development :=
  load_development% orderedPermsLog

/-- The parsed msort development. -/
def msortPinsDev : Development :=
  load_development% msortLog

/-- The parsed bsort development. -/
def bsortPinsDev : Development :=
  load_development% bsortLog

/-- The parsed convert-perm-to-how-many development (pre-merge audit fix
    M2, 2026-08-06: the book had trees offered cross-book but NO
    statement pin of its own — P4's "all 7 books" claim was 6/7). -/
def convertPermPinsDev : Development :=
  load_development% convertPermLog

derive_world isortPinsWorld from isortPinsDev
derive_world qsortPinsWorld from qsortPinsDev
derive_world permPinsWorld from permPinsDev
derive_world orderedPermsPinsWorld from orderedPermsPinsDev
derive_world msortPinsWorld from msortPinsDev
derive_world bsortPinsWorld from bsortPinsDev
derive_world convertPermPinsWorld from convertPermPinsDev

/-! ## The replay run — the exact sweep semantics (`runBook`), registering
    the replayed-statement constants the pins below are stated against. `upTo` the last
    pinned theorem per book: earlier theorems still replay (identical
    replayed-registry state to the sweep) but their independent DP-leaf
    probes are skipped. The expected status LINES (incl. the full `cond[…]`
    sets) are pinned here exactly; drift fails the build before the type
    pins are even reached. -/

elab "sorting_statement_pins_run% " : term => do
  -- NOTE (seams audit F5): the pin runs pass crossTrees but NOT
  -- crossRules — pins predate the channel and wiring it changes pin
  -- behavior; the golden-prefix cross-check below being green is the
  -- evidence no pinned row depends on it. Wire with the close-out arc.
  let (r1, _) ← Runner.runBook "pins/sorting/isort" isortLog
    (upTo := some "HOW-MANY-ISORT") (crossTrees := convertPermPinsTrees)
  let (r2, _) ← Runner.runBook "pins/sorting/qsort" qsortLog
    (upTo := some "TRUE-LISTP-QSORT") (crossTrees := convertPermPinsTrees)
    (crossDevs := convertPermPinsDevs)
  -- P4 books (Phase 7): each pinned at its earliest green row that
  -- exercises the book's own defuns; bsort gets the convert-perm trees
  -- like the sweep (the cross-book rule: discharge — without them the
  -- HOW-MANY-BNEXT row keeps rule:NOT-MEMB-IMPLIES-HOW-MANY-IS-0 as a
  -- residual hypothesis and the golden-prefix cross-check fails).
  let (r3, _) ← Runner.runBook "pins/sorting/perm" permLog
    (upTo := some "PERM-CONS")
  let (r4, _) ← Runner.runBook "pins/sorting/ordered-perms" orderedPermsLog
    (upTo := some "ORDEREDP-RM")
  let (r5, _) ← Runner.runBook "pins/sorting/msort" msortLog
    (upTo := some "ORDEREDP-MSORT")
  let (r6, _) ← Runner.runBook "pins/sorting/bsort" bsortLog
    (upTo := some "HOW-MANY-BNEXT") (crossTrees := convertPermPinsTrees)
  -- M2 (2026-08-06): the book's OWN pin — earliest green row exercising
  -- its own defuns (HOW-MANY, RM).
  let (r7, _) ← Runner.runBook "pins/sorting/convert-perm-to-how-many"
    convertPermLog (upTo := some "HOW-MANY-RM")
  unless r1.integrityFails.isEmpty && r2.integrityFails.isEmpty &&
      r3.integrityFails.isEmpty && r4.integrityFails.isEmpty &&
      r5.integrityFails.isEmpty && r6.integrityFails.isEmpty &&
      r7.integrityFails.isEmpty do
    throwError "sorting statement pins: integrity failures \
      {r1.integrityFails.toList ++ r2.integrityFails.toList ++
       r3.integrityFails.toList ++ r4.integrityFails.toList ++
       r5.integrityFails.toList ++ r6.integrityFails.toList ++
       r7.integrityFails.toList}"
  let expected : List (String × Array String) :=
    [("pins/sorting/isort", r1.lines),
     ("pins/sorting/qsort", r2.lines),
     ("pins/sorting/perm", r3.lines),
     ("pins/sorting/ordered-perms", r4.lines),
     ("pins/sorting/msort", r5.lines),
     ("pins/sorting/bsort", r6.lines),
     ("pins/sorting/convert-perm-to-how-many", r7.lines)]
  let mustHave : List (String × String) :=
    [("pins/sorting/isort",
      -- tp:INSERT DROPPED 2026-08-13 (TP-replay arc increment 2, the
      -- CONS return-path shape): the driver's TP prover discharges
      -- INSERT's emitted `(CONSP (INSERT E X))` corollary from its
      -- `:LEAVES` (every emitted leaf a CONS, ACL2's verdict 3072 =
      -- *ts-cons*), so BOTH isort rows are unconditional now — an
      -- INTENTIONAL improvement, diagnosed row-by-row against the
      -- golden, not a silent drift
      "    ORDEREDP-ISORT → REPLAYED ✓"),
     ("pins/sorting/isort",
      -- (no DISCHARGE suffix here: upTo skips the earlier theorems' DP
      -- probes; the full sweep's golden carries them)
      -- (tp:INSERT dropped 2026-08-13 — see ORDEREDP-ISORT above)
      "    TRUE-LISTP-ISORT → REPLAYED ✓"),
     ("pins/sorting/isort",
      -- tp:HOW-MANY DROPPED 2026-08-12 (TP-replay arc increment 1): the
      -- driver's TP prover discharges HOW-MANY's emitted corollary from
      -- its `:LEAVES` (the BINARY-+ return path), so the row is now
      -- unconditional — an INTENTIONAL improvement, diagnosed row-by-row
      -- against the golden, not a silent drift
      "    HOW-MANY-ISORT → REPLAYED ✓"),
     ("pins/sorting/qsort",
      -- (tp:HOW-MANY dropped 2026-08-12 — see HOW-MANY-ISORT above;
      -- total:PERM-COUNTER-EXAMPLE dropped 2026-08-13 — the ATOM leg:
      -- PCE's emitted termination clause rules on `(ATOM X)`, which the
      -- branch-fact coverage rule now reads as `(not (consp X))`, so the
      -- admission REPLAYS and the hypothesis left the telescope.
      -- INTENTIONAL; diagnosed row-by-row against the golden.
      -- tp:ACL2-COUNT dropped 2026-08-14 — the D-A ts-algebra consumer:
      -- ACL2's context-refined leaves + subterm verdicts now carry the
      -- non-negative-integer corollary through ACL2-COUNT's non-world
      -- return-path primitives, so the hypothesis left the telescope.)
      -- (total:O< dropped 2026-08-15 — T1+2 sprint P3b: the ORDINAL
      -- registry row (Replay/OrdinalSim) + the O-FINP recognizer
      -- duality + the EQUAL-alias reading of the recomputed ground-zero
      -- rulers make O<'s admission REPLAY from ACL2's own emitted
      -- :TERMINATION-CLAUSES, so the hypothesis left the telescope.)
      -- (rule:CONVERT-PERM-TO-HOW-MANY dropped 2026-08-15 — T1+2
      -- sprint P3c: the WP5 cross-book D1 transfer replays the
      -- dependency at this world, so the hypothesis left the
      -- telescope. INTENTIONAL; diagnosed row-by-row.)
      -- (the ARITHMETIC-3 family + the if-lifting rule RETIRED
      -- 2026-08-15 — T1+2 sprint P4b: all five are registered in
      -- `d5GzRules` and discharged at their CITED runes from the D5
      -- prelude constants. INTENTIONAL; diagnosed row-by-row.)
      "    PERM-QSORT → REPLAYED ✓"),
     ("pins/sorting/qsort",
      -- (tp:ACL2-COUNT dropped 2026-08-14 — the D-A consumer; see
      -- PERM-QSORT above.)
      -- (total:O< dropped 2026-08-15 — see PERM-QSORT above.)
      -- (tp:QSORT dropped 2026-08-16 — T1+2 sprint P5b: the CONDITIONAL
      -- stored-rule route. ACL2 keeps `TRUE-LISTP-APPEND` —
      -- `(IMPLIES (TRUE-LISTP B) (TRUE-LISTP (BINARY-APPEND A B)))` — as
      -- a second stored rule of BINARY-APPEND, emitted in `:ALL-TPS`
      -- with its own per-rule `:LEAVES`; the driver now re-proves that
      -- rule from BINARY-APPEND's body under its hypothesis and
      -- discharges the hypothesis at QSORT's own leaf, and the
      -- self-call's FILTER-headed measured actual takes QSORT's
      -- REPLAYED admission decrease. The ROW is unconditional;
      -- the DISCHARGE probe's own telescope still carries `tp:QSORT`
      -- (a separate accounting path — probe rows are informational).
      -- INTENTIONAL; diagnosed against the golden.)
      "    TRUE-LISTP-QSORT → REPLAYED ✓  [DISCHARGE: \
Goal:preprocess/type-set-fc ✓ cond[total:(QSORT X), tp:QSORT]]"),
     ("pins/sorting/qsort",
      -- (tp:HOW-MANY dropped 2026-08-12 — see HOW-MANY-ISORT above;
      -- tp:ALL-REL dropped 2026-08-13 — TP-replay arc increment 4, the
      -- ARITY-3 assembly: ALL-REL's emitted boolean corollary is proved
      -- from its `'T`/`'NIL` leaves and the admission-licensed IH, so
      -- the hypothesis left the telescope. INTENTIONAL; diagnosed
      -- row-by-row against the golden.
      -- total:PERM-COUNTER-EXAMPLE dropped 2026-08-13 — the ATOM leg,
      -- see PERM-QSORT above; tp:ACL2-COUNT dropped 2026-08-14 — the
      -- D-A consumer, also see PERM-QSORT.)
      -- (total:O< dropped 2026-08-15 — see PERM-QSORT above.)
      -- (rule:CONVERT-PERM-TO-HOW-MANY dropped 2026-08-15 — T1+2
      -- sprint P3c: the WP5 cross-book D1 transfer replays the
      -- dependency at this world, so the hypothesis left the
      -- telescope. INTENTIONAL; diagnosed row-by-row.)
      -- (the ARITHMETIC-3 family + the if-lifting rule RETIRED
      -- 2026-08-15 — T1+2 sprint P4b: all five are registered in
      -- `d5GzRules` and discharged at their CITED runes from the D5
      -- prelude constants. INTENTIONAL; diagnosed row-by-row.)
      -- (rule:ORDEREDP-APPEND RETIRED 2026-08-16 — T1+2 sprint P5a: the
      -- IFF-CONCLUSION DECODE class. ACL2 stores this defthm's
      -- `(IFF lhs rhs)` conclusion as an `:EQUIV EQUAL` rewrite rule
      -- because both sides are boolean; `dischargeRuleHyp` now
      -- RECOMPUTES that normalization, taking the two-valuedness of each
      -- side from the EMITTED :TYPE-PRESCRIPTION corollaries (never
      -- assumed — no source, no decode). The waypoint layer's registered
      -- DECODE EXCEPTION `dis_rule_orderedp_append` was deleted with it.
      -- INTENTIONAL; diagnosed row-by-row.)
      "    ORDEREDP-QSORT → REPLAYED ✓"),
     ("pins/sorting/perm",
      "    PERM-CONS → REPLAYED ✓"),
     ("pins/sorting/ordered-perms",
      "    ORDEREDP-RM → REPLAYED ✓"),
     ("pins/sorting/msort",
      -- (tp:EVENS dropped 2026-08-13 — the same CONS return-path shape,
      -- via the TRUE-LISTP corollary class: EVENS's emitted leaves are a
      -- CONS verdicted 1024 and 'NIL verdicted 128, both inside
      -- *ts-true-list* = 1152)
      "    ORDEREDP-MSORT → REPLAYED ✓"),
     ("pins/sorting/bsort",
      -- (tp:HOW-MANY dropped 2026-08-12 — see HOW-MANY-ISORT above)
      "    HOW-MANY-BNEXT → REPLAYED ✓"),
     ("pins/sorting/convert-perm-to-how-many",
      -- (tp:HOW-MANY dropped 2026-08-12 — see HOW-MANY-ISORT above)
      "    HOW-MANY-RM → REPLAYED ✓")]
  let goldenLines := sweepGolden.splitOn "\n"
  for (book, line) in mustHave do
    let some (_, lines) := expected.find? (·.1 == book)
      | throwError "sorting statement pins: unknown book {book}"
    unless lines.any (· == line) do
      throwError "sorting statement pins: {book} lost pinned status line\n  \
        {line}\ngot:\n{"\n".intercalate lines.toList}"
    -- audit F3: the pinned expectation itself must match the SWEEP's
    -- committed golden (prefix — see sweepGolden's docstring), so pins
    -- and sweep cannot drift apart silently
    unless goldenLines.any (·.startsWith line) do
      throwError "sorting statement pins: pinned line is NOT a prefix of \
        any committed sweep-golden line (pins/sweep drift — audit F3)\n  \
        {line}"
  -- the QSORT termination replayed statement's existence is asserted here
  -- (the type pin below is the content gate); since W1 item 6 it ALSO
  -- registers a golden row (termination:QSORT)
  unless (← getEnv).contains
      (Name.mkStr2 "ReplayedTermination" "term_pins_sorting_qsort_QSORT") do
    throwError "sorting statement pins: QSORT termination replayed statement was not registered"
  logInfo "sorting statement pins: replay statuses hold (ORDEREDP-ISORT, \
    PERM-QSORT, TRUE-LISTP-QSORT, PERM-CONS, ORDEREDP-RM, ORDEREDP-MSORT, \
    HOW-MANY-BNEXT + QSORT termination replayed statement)"
  return mkConst ``True.intro

-- unlimited at the command like the coverage sweep — the harness enforces
-- REAL per-theorem budgets internally (withRealMaxHeartbeats)
set_option maxHeartbeats 0 in
def sortingStatementPinsRun : True := sorting_statement_pins_run%

/-! ## Term helpers (transcription vocabulary) -/

def sym (n : String) : SExpr := .atom (.symbol { name := n })
def ap1 (f : String) (a : SExpr) : SExpr := .cons (sym f) (.cons a .nil)
def ap2 (f : String) (a b : SExpr) : SExpr := .cons (sym f) (.cons a (.cons b .nil))
def ap3 (f : String) (a b c : SExpr) : SExpr :=
  .cons (sym f) (.cons a (.cons b (.cons c .nil)))
/-- `(QUOTE e)`. -/
def qt (e : SExpr) : SExpr := .cons (sym "QUOTE") (.cons e .nil)

-- (`synpQuotep` — ACL2's translation of a `(syntaxp (quotep v))`
-- hypothesis — DELETED 2026-08-16: zero uses here, and a duplicate of
-- the LIVE copy at `ACL2Lean/Replay/GzRules.lean`. A pin vocabulary
-- with no pin is cruft; a second copy of a live definition is worse.)

/-! ## Hypothesis shapes (the `cond[…]` classes, spelled out once)

    Each is the exact machine shape of one condition class; the per-pin
    instantiations below say WHICH fn/rule and are source-checked there. -/

-- (`tpNonnegInt1` DELETED 2026-08-14 — orphaned vocabulary: its only
-- customers were the four qsort ACL2-COUNT tp: pins, retired with the
-- D-A ts-algebra consumer.)

-- (`tpPred2` — the BINARY single-predicate corollary vocabulary, used by
-- the `tp:INSERT`/`tp:INS` pins — DELETED 2026-08-13: every pin that
-- spoke it retired with the CONS return-path shape, and a pin
-- vocabulary with no pin is cruft. It comes back with the next binary
-- single-predicate TP that a pin actually keeps.)

-- (`totalHyp1`, `totalHyp2`, `tpNonnegInt2`, `tpPred1`, `ruleEqHyp`,
-- `ruleEqHyp1` — the rest of the `cond[…]` hypothesis-shape vocabulary
-- — DELETED 2026-08-16, same convention as the two tombstones above.
-- The T1+2 sprint retired every condition these spelled and left every
-- pin in this file premise-free: at the sprint's exit `totalHyp1` had
-- 0 users (20 at the sprint base), `totalHyp2` 0 (12), `tpPred1` 0 (3),
-- `tpNonnegInt2` 0 (already 0 at the base), and `ruleEqHyp`/`ruleEqHyp1`
-- survived only inside `trueListpRmHyp`/`convertPermHyp`, themselves
-- dead and deleted in the same pass. Each comes back the day a pin
-- keeps a condition of its class again — a pin vocabulary with no pin
-- is cruft.)

/-! ## isort book (acl2/books/sorting/isort.lisp) -/

/-- PIN the machine-generated statement of `ORDEREDP-ISORT`: the replayed statement of
    the ACL2 defthm `(orderedp (isort x))`, UNCONDITIONAL. Its one-time
    hypothesis — insert's emitted TP corollary `(consp (insert e x))` —
    RETIRED 2026-08-13 (TP-replay arc increment 2, the CONS return-path
    shape): the driver's TP prover discharges it from ACL2's own emitted
    corollary + `:LEAVES`, so the hypothesis left the telescope and the
    pinned type drops it too. INTENTIONAL; diagnosed against the golden. -/
example :
    ∀ (env : Env),
      EvTrue isortPinsWorld env (ap1 "ORDEREDP" (ap1 "ISORT" (sym "X"))) :=
  ReplayedStatements.replayed_pins_sorting_isort_ORDEREDP_ISORT

#print axioms ReplayedStatements.replayed_pins_sorting_isort_ORDEREDP_ISORT

/-! ## qsort book (acl2/books/sorting/qsort.lisp) -/

/-- PIN the machine-generated statement of `PERM-QSORT`: the replayed statement of the
    ACL2 defthm `(perm (qsort x) x)`, **UNCONDITIONAL since 2026-08-15**
    — the pinned type is premise-free; see the retirement log below,
    where each former condition (`o<` totality; the `how-many` /
    `acl2-count` TP corollaries; the cited rules) carries its own dated
    diagnosis. -/
example :
    ∀ (env : Env),
      -- (total:PERM-COUNTER-EXAMPLE RETIRED 2026-08-13 — PCE's emitted
      -- termination clause rules on `(ATOM X)`, which the branch-fact
      -- coverage rule now reads as `(not (consp X))`, so the admission
      -- REPLAYS and the hypothesis left the telescope. INTENTIONAL.)
      -- (total:O< RETIRED 2026-08-15 — T1+2 sprint P3b: the ORDINAL
      -- registry row (Replay/OrdinalSim) + the O-FINP recognizer
      -- duality + the world-read EQUAL-alias normalization of ACL2's
      -- recomputed ground-zero rulers discharge O<'s admission from
      -- its OWN emitted :TERMINATION-CLAUSES, so the hypothesis left
      -- the telescope and the pinned type drops it. INTENTIONAL;
      -- diagnosed against the golden.)
      -- (tp:HOW-MANY RETIRED 2026-08-12 — the driver's TP prover
      -- discharges HOW-MANY's emitted corollary from its `:LEAVES`;
      -- the hypothesis left the telescope, so the pinned type drops
      -- it too. INTENTIONAL; diagnosed against the golden.)
      -- (tp:ACL2-COUNT RETIRED 2026-08-14 — the D-A ts-algebra
      -- consumer: the R2 fork batch's context-refined `:LEAVES` (each
      -- leaf's governing tests + ACL2's derived type-alist) and per-leaf
      -- SUBTERM VERDICTS carry the non-negative-integer corollary through
      -- ACL2-COUNT's non-world return-path primitives, so the hypothesis
      -- left the telescope and the pinned type drops it. INTENTIONAL;
      -- diagnosed against the golden.)
      -- (the not-memb-implies-how-many-is-0 hypothesis is GONE: discharged
      -- CROSS-BOOK from the dependency book's replayed tree — 2a)
      -- (rule:CONVERT-PERM-TO-HOW-MANY RETIRED 2026-08-15 — T1+2
      -- sprint P3c collection: the WP5 cross-book D1 transfer replays
      -- the dependency at this world (the pins run now carries the
      -- same crossDevs channel as the sweep), so the hypothesis left
      -- the telescope and the pinned type drops it. INTENTIONAL;
      -- diagnosed against the golden.)
      -- the arithmetic-3 commutativity/associativity family + the two
      -- if-lifting rules (all unconditional; cited by HOW-MANY-QSORT's own
      -- replay, inherited since its rule: condition discharges from its
      -- replayed statement)
      -- (the ARITHMETIC-3 family — rule:(+ y x), rule:(+ y (+ x z)),
      -- rule:(+ (+ x y) z), rule:(+ x (if a b c)) — and the if-lifting
      -- rule:(equal (if a b c) x) RETIRED 2026-08-15, T1+2 sprint P4b:
      -- the five are registered in `d5GzRules`, so the driver discharges
      -- each at its CITED rune from its D5 prelude constant
      -- (`Replay/GzRules.lean`, recompute-checked against the emitted
      -- `(:RULES …)` entry). The hypotheses left the telescope and the
      -- pinned type drops them. INTENTIONAL; diagnosed against the
      -- golden.)
      EvTrue qsortPinsWorld env (ap2 "PERM" (ap1 "QSORT" (sym "X")) (sym "X")) :=
  ReplayedStatements.replayed_pins_sorting_qsort_PERM_QSORT

#print axioms ReplayedStatements.replayed_pins_sorting_qsort_PERM_QSORT

/-- PIN the machine-generated statement of `TRUE-LISTP-QSORT`: the replayed statement
    of the ACL2 defthm `(true-listp (qsort x))`, **UNCONDITIONAL since
    2026-08-16** — the pinned type is premise-free; see the retirement
    log below, where `o<` totality, qsort's own recursive TP corollary
    and acl2-count's non-negative-integer TP each carry a dated
    diagnosis. -/
example :
    ∀ (env : Env),
      -- (total:O< RETIRED 2026-08-15 — T1+2 sprint P3b: the ORDINAL
      -- registry row (Replay/OrdinalSim) + the O-FINP recognizer
      -- duality + the world-read EQUAL-alias normalization of ACL2's
      -- recomputed ground-zero rulers discharge O<'s admission from
      -- its OWN emitted :TERMINATION-CLAUSES, so the hypothesis left
      -- the telescope and the pinned type drops it. INTENTIONAL;
      -- diagnosed against the golden.)
      -- (tp:QSORT RETIRED 2026-08-16 — T1+2 sprint P5b: the CONDITIONAL
      -- stored-rule route (see the pinned status line above), so the
      -- hypothesis left the telescope and the pinned type drops it.
      -- INTENTIONAL; diagnosed against the golden.)
      -- (tp:ACL2-COUNT RETIRED 2026-08-14 — the D-A ts-algebra
      -- consumer: the R2 fork batch's context-refined `:LEAVES` (each
      -- leaf's governing tests + ACL2's derived type-alist) and per-leaf
      -- SUBTERM VERDICTS carry the non-negative-integer corollary through
      -- ACL2-COUNT's non-world return-path primitives, so the hypothesis
      -- left the telescope and the pinned type drops it. INTENTIONAL;
      -- diagnosed against the golden.)
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
    GTE-site clause first, in ACL2's recorded order). The replayed statement is the
    replayed waterfall's root — **UNCONDITIONAL since 2026-08-15**; the
    `o<` totality, `acl2-count` TP and `fold-consts-in-+` classes it once
    carried are retired, each with its dated diagnosis in the log below. -/

/-- `(if (endp x) 't (if (endp (cdr x)) 't (o< (acl2-count (filter 'fn (cdr x) (car x))) (acl2-count x))))` -/
private def qsortDecreaseClause (fn : String) : SExpr :=
  ap3 "IF" (ap1 "ENDP" (sym "X")) (qt (sym "T"))
    (ap3 "IF" (ap1 "ENDP" (ap1 "CDR" (sym "X"))) (qt (sym "T"))
      (ap2 "O<"
        (ap1 "ACL2-COUNT" (ap3 "FILTER" (qt (sym fn)) (ap1 "CDR" (sym "X")) (ap1 "CAR" (sym "X"))))
        (ap1 "ACL2-COUNT" (sym "X"))))

example :
    ∀ (env : Env),
      -- (total:O< RETIRED 2026-08-15 — T1+2 sprint P3b: the ORDINAL
      -- registry row (Replay/OrdinalSim) + the O-FINP recognizer
      -- duality + the world-read EQUAL-alias normalization of ACL2's
      -- recomputed ground-zero rulers discharge O<'s admission from
      -- its OWN emitted :TERMINATION-CLAUSES, so the hypothesis left
      -- the telescope and the pinned type drops it. INTENTIONAL;
      -- diagnosed against the golden.)
      -- (tp:ACL2-COUNT RETIRED 2026-08-14 — the D-A ts-algebra
      -- consumer: the R2 fork batch's context-refined `:LEAVES` (each
      -- leaf's governing tests + ACL2's derived type-alist) and per-leaf
      -- SUBTERM VERDICTS carry the non-negative-integer corollary through
      -- ACL2-COUNT's non-world return-path primitives, so the hypothesis
      -- left the telescope and the pinned type drops it. INTENTIONAL;
      -- diagnosed against the golden.)
      EvTrue qsortPinsWorld env
        (ap3 "IF" (qsortDecreaseClause "GTE") (qsortDecreaseClause "LT") (qt .nil)) :=
  ReplayedTermination.term_pins_sorting_qsort_QSORT

#print axioms ReplayedTermination.term_pins_sorting_qsort_QSORT

/-! ## perm book (acl2/books/sorting/perm.lisp) -/

/-- PIN the machine-generated statement of `PERM-CONS` (perm.lisp:32, a
    local defthm): the replayed statement of
      `(implies (memb a x) (equal (perm x (cons a y)) (perm (rm a x) y)))`
    — UNCONDITIONAL (the sweep row carries no cond). The pinned term is
    ACL2's translation: the IMPLIES form exactly as the source states it. -/
example :
    ∀ (env : Env),
      EvTrue permPinsWorld env
        (ap2 "IMPLIES" (ap2 "MEMB" (sym "A") (sym "X"))
          (ap2 "EQUAL"
            (ap2 "PERM" (sym "X") (ap2 "CONS" (sym "A") (sym "Y")))
            (ap2 "PERM" (ap2 "RM" (sym "A") (sym "X")) (sym "Y")))) :=
  ReplayedStatements.replayed_pins_sorting_perm_PERM_CONS

#print axioms ReplayedStatements.replayed_pins_sorting_perm_PERM_CONS

/-! ## ordered-perms book (acl2/books/sorting/ordered-perms.lisp) -/

/-- PIN the machine-generated statement of `ORDEREDP-RM`
    (ordered-perms.lisp:10, a local defthm): the replayed statement of
      `(implies (orderedp a) (orderedp (rm e a)))`
    — UNCONDITIONAL. -/
example :
    ∀ (env : Env),
      EvTrue orderedPermsPinsWorld env
        (ap2 "IMPLIES" (ap1 "ORDEREDP" (sym "A"))
          (ap1 "ORDEREDP" (ap2 "RM" (sym "E") (sym "A")))) :=
  ReplayedStatements.replayed_pins_sorting_ordered_perms_ORDEREDP_RM

#print axioms
  ReplayedStatements.replayed_pins_sorting_ordered_perms_ORDEREDP_RM

/-! ## msort book (acl2/books/sorting/msort.lisp) -/

/-- PIN the machine-generated statement of `ORDEREDP-MSORT`
    (msort.lisp:40): the replayed statement of `(orderedp (msort x))`,
    **UNCONDITIONAL since 2026-08-14** — the pinned type is premise-free.
    Retirement log:
    - (totality of `merge2` (binary) and `msort` (unary) RETIRED
      2026-08-14 — the R3 unified measure/arity table; both left the
      telescope, and the corresponding debt sorries went with them.)
    - (evens' emitted TP corollary `(true-listp (evens l))` RETIRED
      2026-08-13 — TP-replay arc increment 2's TRUE-LISTP corollary
      class: the driver discharges it from ACL2's emitted `:LEAVES`, so
      the hypothesis left the telescope. INTENTIONAL.) -/
example :
    ∀ (env : Env),
      -- (total:MERGE2 and total:MSORT RETIRED 2026-08-14 — the R3
      -- unified measure/arity table: MERGE2's two-measured-formal
      -- `(BINARY-+ (ACL2-COUNT X) (ACL2-COUNT Y))` measure is a
      -- registered ROW, and MSORT's opaque `(EVENS X)` measured actual
      -- is ∃-eliminated onto the existing EVENS/ODDS registry decrease.
      -- Both totalities REPLAY from the emitted clauses, so both
      -- hypotheses left the telescope. INTENTIONAL.)
      EvTrue msortPinsWorld env (ap1 "ORDEREDP" (ap1 "MSORT" (sym "X"))) :=
  ReplayedStatements.replayed_pins_sorting_msort_ORDEREDP_MSORT

#print axioms ReplayedStatements.replayed_pins_sorting_msort_ORDEREDP_MSORT

/-! ## bsort book (acl2/books/sorting/bsort.lisp) -/

/-- PIN the machine-generated statement of `HOW-MANY-BNEXT`
    (bsort.lisp:72): the replayed statement of
      `(equal (how-many e (bnext x)) (how-many e x))`
    **UNCONDITIONAL since 2026-08-14** — the pinned type is premise-free;
    `bnext` totality and how-many's emitted non-negative-integer TP
    corollary are retired, each dated in the log below. The
    cross-book rule condition `rule:NOT-MEMB-IMPLIES-HOW-MANY-IS-0` is
    GONE from the row exactly because the pin run offers the convert-perm
    dependency trees like the sweep (2a cross-discharge). -/
example :
    ∀ (env : Env),
      -- (total:BNEXT RETIRED 2026-08-14 — the R3 measure table's LEN
      -- row; the hypothesis left the telescope. INTENTIONAL.)
      -- (tp:HOW-MANY RETIRED 2026-08-12 — the driver's TP prover
      -- discharges HOW-MANY's emitted corollary from its `:LEAVES`;
      -- the hypothesis left the telescope, so the pinned type drops
      -- it too. INTENTIONAL; diagnosed against the golden.)
      EvTrue bsortPinsWorld env
        (ap2 "EQUAL"
          (ap2 "HOW-MANY" (sym "E") (ap1 "BNEXT" (sym "X")))
          (ap2 "HOW-MANY" (sym "E") (sym "X"))) :=
  ReplayedStatements.replayed_pins_sorting_bsort_HOW_MANY_BNEXT

#print axioms ReplayedStatements.replayed_pins_sorting_bsort_HOW_MANY_BNEXT

/-! ## convert-perm-to-how-many book
    (acl2/books/sorting/convert-perm-to-how-many.lisp) -/

/-- PIN the machine-generated statement of `HOW-MANY-RM`
    (convert-perm-to-how-many.lisp:30): the replayed statement of
      `(implies (not (equal a b)) (equal (how-many a (rm b x))
                                          (how-many a x)))`
    **UNCONDITIONAL since 2026-08-12** — the pinned type is premise-free;
    how-many's emitted non-negative-integer TP corollary is retired, dated
    in the log below. Pre-merge audit fix M2 (2026-08-06): the
    book's first own statement pin — P4's per-book coverage was 6/7
    without it. -/
example :
    ∀ (env : Env),
      -- (tp:HOW-MANY RETIRED 2026-08-12 — the driver's TP prover
      -- discharges HOW-MANY's emitted corollary from its `:LEAVES`;
      -- the hypothesis left the telescope, so the pinned type drops
      -- it too. INTENTIONAL; diagnosed against the golden.)
      EvTrue convertPermPinsWorld env
        (ap2 "IMPLIES" (ap1 "NOT" (ap2 "EQUAL" (sym "A") (sym "B")))
          (ap2 "EQUAL"
            (ap2 "HOW-MANY" (sym "A") (ap2 "RM" (sym "B") (sym "X")))
            (ap2 "HOW-MANY" (sym "A") (sym "X")))) :=
  ReplayedStatements.replayed_pins_sorting_convert_perm_to_how_many_HOW_MANY_RM

#print axioms
  ReplayedStatements.replayed_pins_sorting_convert_perm_to_how_many_HOW_MANY_RM

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
    `(IF a a b)`), UNCONDITIONAL: ins's emitted TP corollary
    `(consp (ins e x))` is discharged by the driver's TP prover from
    ACL2's own `:LEAVES` (TP-replay arc increment 2, 2026-08-13 — the
    CONS return-path shape); the ground-zero rule `default-cdr`
    discharges via its D5 prelude constant. -/

private def p3ConjLog : String :=
  include_str "../acl2_samples/pattern-tests/p3-conj-mid-literal.proof-log"

def p3ConjPinsDev : Development :=
  load_development% p3ConjLog

derive_world p3ConjPinsWorld from p3ConjPinsDev

elab "p3_conj_statement_pin_run% " : term => do
  let (r, _) ← Runner.runBook "pins/p3-conj" p3ConjLog none
  unless r.integrityFails.isEmpty do
    throwError "p3-conj statement pin: integrity failures \
      {r.integrityFails.toList}"
  -- tp:INS DROPPED 2026-08-13 (TP-replay arc increment 2): INS is an
  -- insert-shaped fn, so its emitted `(CONSP (INS E X))` corollary +
  -- `:LEAVES` (three CONS leaves, ACL2 verdict 3072 = *ts-cons*)
  -- discharge through the TP prover's CONS return-path arm — the row is
  -- unconditional now. INTENTIONAL; same shape as ORDEREDP-ISORT.
  unless r.lines.any (·.startsWith
      "    ORDD-INS-MID → REPLAYED ✓") do
    throwError "p3-conj statement pin: lost the pinned status prefix; got:\n\
      {"\n".intercalate r.lines.toList}"
  logInfo "p3-conj statement pin: replay status holds (ORDD-INS-MID)"
  return mkConst ``True.intro

set_option maxHeartbeats 0 in
def p3ConjStatementPinRun : True := p3_conj_statement_pin_run%

/-- `(not x)` term. -/
private def notOf (x : SExpr) : SExpr := .cons (sym "NOT") (.cons x .nil)

example :
    ∀ (env : Env),
      -- (tp:INS RETIRED 2026-08-13 — the CONS return-path shape; the
      -- hypothesis left the telescope, so the pinned type drops it.)
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

-- (`tpBool3` — the ternary boolean-corollary vocabulary — DELETED as
-- orphaned when `tp:ALL-REL` left this pin's telescope, TP-replay arc
-- increment 4, 2026-08-13.)

/-- PIN the machine-generated statement of `ORDEREDP-QSORT`: the replayed statement of
    the ACL2 defthm `(orderedp (qsort x))`, **UNCONDITIONAL since
    2026-08-16** — the pinned type is premise-free; every item below is
    RETIRED, and the dated diagnosis for each is in the retirement log in
    the body. The former telescope was:
    - totality of `o<` (perm-counter-example's left the telescope with
      the ATOM leg, 2026-08-13),
    - the emitted TP corollary of `acl2-count` (non-negative integer —
      source-true: it counts); `how-many`'s and `all-rel`'s are now
      supplied by the driver's own TP prover (TP-replay arc increments 1
      and 4),
    - the cited rules `convert-perm-to-how-many`,
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
      -- (total:PERM-COUNTER-EXAMPLE RETIRED 2026-08-13 — the ATOM leg,
      -- as on PERM-QSORT's pin above. INTENTIONAL.)
      -- (total:O< RETIRED 2026-08-15 — T1+2 sprint P3b: the ORDINAL
      -- registry row (Replay/OrdinalSim) + the O-FINP recognizer
      -- duality + the world-read EQUAL-alias normalization of ACL2's
      -- recomputed ground-zero rulers discharge O<'s admission from
      -- its OWN emitted :TERMINATION-CLAUSES, so the hypothesis left
      -- the telescope and the pinned type drops it. INTENTIONAL;
      -- diagnosed against the golden.)
      -- (tp:HOW-MANY RETIRED 2026-08-12 — the driver's TP prover
      -- discharges HOW-MANY's emitted corollary from its `:LEAVES`;
      -- the hypothesis left the telescope, so the pinned type drops
      -- it too. INTENTIONAL; diagnosed against the golden.)
      -- (tp:ALL-REL RETIRED 2026-08-13 — TP-replay arc increment 4:
      -- the driver's TP prover discharges ALL-REL's emitted boolean
      -- corollary at arity 3, so the hypothesis left the telescope and
      -- the pinned type drops it. INTENTIONAL; diagnosed against the
      -- golden.)
      -- (tp:ACL2-COUNT RETIRED 2026-08-14 — the D-A ts-algebra
      -- consumer: the R2 fork batch's context-refined `:LEAVES` (each
      -- leaf's governing tests + ACL2's derived type-alist) and per-leaf
      -- SUBTERM VERDICTS carry the non-negative-integer corollary through
      -- ACL2-COUNT's non-world return-path primitives, so the hypothesis
      -- left the telescope and the pinned type drops it. INTENTIONAL;
      -- diagnosed against the golden.)
      -- (not-memb-implies-how-many-is-0: discharged cross-book, 2a)
      -- (rule:CONVERT-PERM-TO-HOW-MANY RETIRED 2026-08-15 — T1+2
      -- sprint P3c collection: the WP5 cross-book D1 transfer replays
      -- the dependency at this world (the pins run now carries the
      -- same crossDevs channel as the sweep), so the hypothesis left
      -- the telescope and the pinned type drops it. INTENTIONAL;
      -- diagnosed against the golden.)
      -- the arithmetic-3 commutativity/associativity family + the two
      -- if-lifting rules (all unconditional; cited by HOW-MANY-QSORT's own
      -- replay, inherited since its rule: condition discharges from its
      -- replayed statement)
      -- (the ARITHMETIC-3 family — rule:(+ y x), rule:(+ y (+ x z)),
      -- rule:(+ (+ x y) z), rule:(+ x (if a b c)) — and the if-lifting
      -- rule:(equal (if a b c) x) RETIRED 2026-08-15, T1+2 sprint P4b:
      -- the five are registered in `d5GzRules`, so the driver discharges
      -- each at its CITED rune from its D5 prelude constant
      -- (`Replay/GzRules.lean`, recompute-checked against the emitted
      -- `(:RULES …)` entry). The hypotheses left the telescope and the
      -- pinned type drops them. INTENTIONAL; diagnosed against the
      -- golden.)
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
  load_development% p5FlipLog

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
    Both **UNCONDITIONAL since 2026-08-12** — both pinned types are
    premise-free; ln's emitted non-negative-integer TP corollary, which
    each once carried, is retired (dated in each body below). -/

private def p7CongLog : String :=
  include_str "../acl2_samples/pattern-tests/p7-cong-collapse.proof-log"

def p7CongPinsDev : Development :=
  load_development% p7CongLog

derive_world p7CongPinsWorld from p7CongPinsDev

elab "pattern_statement_pins_run% " : term => do
  let (r5, _) ← Runner.runBook "pins/p5-flip" p5FlipLog none
  let (r7, _) ← Runner.runBook "pins/p7-cong" p7CongLog none
  unless r5.integrityFails.isEmpty && r7.integrityFails.isEmpty do
    throwError "pattern statement pins: integrity failures \
      {r5.integrityFails.toList ++ r7.integrityFails.toList}"
  let mustHave : List (String × Array String × String) :=
    [("pins/p5-flip", r5.lines, "    DUPP-REP-MID → REPLAYED ✓"),
     -- tp:LN DROPPED 2026-08-12 (TP-replay arc increment 1): LN is
     -- len-shaped, so its emitted corollary + `:LEAVES` discharge through
     -- the TP prover's BINARY-+ return-path arm — an INTENTIONAL
     -- improvement (both rows became unconditional), diagnosed against
     -- the sweep, not a silent drift
     ("pins/p7-cong", r7.lines, "    P7-TARGET → REPLAYED ✓"),
     ("pins/p7-cong", r7.lines,
      "    SAME-LN-IMPLIES-EQUAL-LN-1 → REPLAYED ✓")]
  for (book, lines, line) in mustHave do
    unless lines.any (· == line) do
      throwError "pattern statement pins: {book} lost pinned status line\n  \
        {line}\ngot:\n{"\n".intercalate lines.toList}"
  logInfo "pattern statement pins: replay statuses hold (DUPP-REP-MID, \
    P7-TARGET, SAME-LN-IMPLIES-EQUAL-LN-1)"
  return mkConst ``True.intro

set_option maxHeartbeats 0 in
def patternStatementPinsRun : True := pattern_statement_pins_run%

/-- PIN the machine-generated statement of `DUPP-REP-MID` (p5): the replayed statement
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
      -- (tp:LN RETIRED 2026-08-12 — same TP-replay route as
      -- tp:HOW-MANY above: LN is len-shaped.)
      EvTrue p7CongPinsWorld env
        (ap2 "EQUAL" (ap1 "LN" (ap1 "DUB" (sym "X"))) (ap1 "LN" (sym "X"))) :=
  ReplayedStatements.replayed_pins_p7_cong_P7_TARGET

#print axioms ReplayedStatements.replayed_pins_p7_cong_P7_TARGET

/-- PIN the machine-generated statement of `SAME-LN-IMPLIES-EQUAL-LN-1`
    (the defcong's macro-expanded defthm). -/
example :
    ∀ (env : Env),
      -- (tp:LN RETIRED 2026-08-12 — same TP-replay route as
      -- tp:HOW-MANY above: LN is len-shaped.)
      EvTrue p7CongPinsWorld env
        (ap2 "IMPLIES"
          (ap2 "SAME-LN" (sym "X") (sym "X-EQUIV"))
          (ap2 "EQUAL" (ap1 "LN" (sym "X")) (ap1 "LN" (sym "X-EQUIV")))) :=
  ReplayedStatements.replayed_pins_p7_cong_SAME_LN_IMPLIES_EQUAL_LN_1

#print axioms ReplayedStatements.replayed_pins_p7_cong_SAME_LN_IMPLIES_EQUAL_LN_1

/-! ## TRUE-LISTP-ISORT + HOW-MANY-ISORT (isort.lisp:26, 29) — the isort
    book's remaining green rows (validator/lifter arc W1 item 3: the
    survey's near-zero-marginal-cost pins; completes the book). -/

/-- PIN `TRUE-LISTP-ISORT`: `(true-listp (isort x))`, UNCONDITIONAL —
    insert's `(consp (insert e x))` TP RETIRED 2026-08-13 (the CONS
    return-path shape; the driver discharges it from ACL2's emitted
    `:LEAVES`, so the hypothesis left the telescope). INTENTIONAL. -/
example :
    ∀ (env : Env),
      EvTrue isortPinsWorld env (ap1 "TRUE-LISTP" (ap1 "ISORT" (sym "X"))) :=
  ReplayedStatements.replayed_pins_sorting_isort_TRUE_LISTP_ISORT

#print axioms ReplayedStatements.replayed_pins_sorting_isort_TRUE_LISTP_ISORT

/-- PIN `HOW-MANY-ISORT`: `(equal (how-many e (isort x)) (how-many e x))`,
    **UNCONDITIONAL since 2026-08-12** — the pinned type is premise-free;
    how-many's non-negative-integer TP is retired (dated in the body
    below), fold-consts-in-+ discharges via its D5 prelude constant, and
    `not-memb-implies-how-many-is-0` discharges CROSS-BOOK from the
    dependency book's replayed tree (2a). -/
example :
    ∀ (env : Env),
      -- (tp:HOW-MANY RETIRED 2026-08-12 — the driver's TP prover
      -- discharges HOW-MANY's emitted corollary from its `:LEAVES`;
      -- the hypothesis left the telescope, so the pinned type drops
      -- it too. INTENTIONAL; diagnosed against the golden.)
      EvTrue isortPinsWorld env
        (ap2 "EQUAL"
          (ap2 "HOW-MANY" (sym "E") (ap1 "ISORT" (sym "X")))
          (ap2 "HOW-MANY" (sym "E") (sym "X"))) :=
  ReplayedStatements.replayed_pins_sorting_isort_HOW_MANY_ISORT

#print axioms ReplayedStatements.replayed_pins_sorting_isort_HOW_MANY_ISORT

/-! ## Equisort SCOPE pins (Phase 4, R6): the structured scope surface
    read off the recaptured log — the single derivation the parametric
    machinery (ConstraintsHold, R7b instantiation) consumes. Pinned
    truthfully against the artifact: three top-level scopes (a trivial
    grouping one, then SORTFN and SSORTFN), six constraint formulas and
    three scoped witnesses each. -/

private def equisortScopeLog : String :=
  include_str "../acl2_samples/sorting/equisort.proof-log"

elab "equisort_scope_pins% " : term => do
  let log ← match ProofLog.parse equisortScopeLog with
    | .ok l => pure l
    | .error e => throwError "equisort scope pin: parse failed: {e}"
  let dev ← match ClauseTree.buildDevelopment log with
    | .ok d => pure d
    | .error e => throwError "equisort scope pin: recon failed: {e}"
  let scopes ← match dev.scopes with
    | .ok s => pure s
    | .error e => throwError "equisort scope pin: scopes failed: {e}"
  let shape := scopes.map fun s =>
    (s.sigs.map (·.name), s.constraintFns.map (·.map (·.name)),
     s.constraintFormulas.length, s.witnesses.length,
     s.theoremNames.length)
  let expected : List (List String × Option (List String) × Nat × Nat × Nat) :=
    [([], none, 0, 0, 0),
     (["SORTFN1", "SORTFN2"], some ["SORTFN1", "SORTFN2"], 6, 3, 6),
     (["SSORTFN1", "SSORTFN2"], some ["SSORTFN1", "SSORTFN2"], 6, 3, 6)]
  unless shape == expected do
    throwError "equisort scope pin: shape {repr shape} ≠ expected \
      {repr expected} — re-pin truthfully"
  logInfo "equisort scope pins hold (3 scopes; 6 constraints + 3 \
    witnesses each on the two constrained scopes)"
  return Lean.mkConst ``True.intro

def equisortScopePins : True := equisort_scope_pins%

/-! ## sorts-equivalent CAPSTONE statement pins (final close-out arc
    increment 0 — close-out audit follow-up, both reviewers). The two
    FI capstone rows are the corpus's headline artifacts and had no
    statement pin. These pin the MACHINE statements — the sweep's own
    registered constants, imported from `Tests.Coverage.BSsortsEquivalent`
    (no re-replay: the constants are reused, so the pin costs two
    example elaborations) — against types hand-transcribed from
    `acl2/books/sorting/sorts-equivalent.lisp`, so statement-derivation
    drift through a RECAPTURE fails here at elaboration. HYPOTHESIS
    discipline as above: every `cond[…]` entry transcribed in telescope
    order; stored-rule forms from the emitted `(:RULES …)` entries
    (TRUE-LISTP-RM is the ordered-perms book's cross entry). -/

private def sortsEqLog : String :=
  include_str "../acl2_samples/sorting/sorts-equivalent.proof-log"

def sortsEqPinsDev : Development := load_development% sortsEqLog

derive_world sortsEqPinsWorld from sortsEqPinsDev

-- (`trueListpRmHyp` — `rule:TRUE-LISTP-RM`, ordered-perms.lisp:34 —
-- and `convertPermHyp` — `rule:CONVERT-PERM-TO-HOW-MANY`,
-- convert-perm-to-how-many.lisp:92 — DELETED 2026-08-16. Both had 3
-- users each at the sprint base and 0 at its exit: the P3c cross-book
-- D1 transfer retired both conditions from every telescope in this
-- file (diagnosed in place at the capstone pins below). Same
-- convention as the vocabulary tombstones above; they come back with
-- the next pin that keeps their class.)

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
      EvTrue sortsEqPinsWorld env
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
      EvTrue sortsEqPinsWorld env
        (ap2 "EQUAL" (ap1 "QSORT" (sym "X")) (ap1 "ISORT" (sym "X"))) :=
  ReplayedStatements.replayed_sorting_sorts_equivalent_QSORT_IS_ISORT

#print axioms ReplayedStatements.replayed_sorting_sorts_equivalent_QSORT_IS_ISORT

end ACL2.Tests.SortingPins
