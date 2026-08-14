/-
  Tests/PatternPins — replay GATES for pattern-corpus validation books
  (sorting arc 2026-07-29). THE SCALABLE HOME for per-family pins: one
  section + one `..._pin%` elab per arc/family, each pinning its books'
  TRUTHFUL replay outcomes (green counts AND frontier tripwires — a 0/1
  pin flips loudly when the blocking frontier lands, which is the moment
  the book's target machinery earns its green validation). Do NOT grow
  `Tests/DriverTests.lean` with new book gates; add sections here.

  `runBook` is the sweep harness: a ✓ row is kernel-checked AND
  axiom-filtered, so a pinned green count is an end-to-end validation.
-/
import ACL2Lean.Replay.Runner

namespace ACL2.Tests.PatternPins

open Lean ACL2 ACL2.Replay

/-! ## Sorting-completion arc (2026-07-29): the recorded-termination route
    + the AND-shape conjunction composer, validated DECORRELATED from the
    qsort book (the mapping-arc amendment: synthetic BOOKS through real
    ACL2 + capture; never synthetic artifacts). -/

private def recordedTermLog : String :=
  include_str "../acl2_samples/pattern-tests/p3-recorded-termination.proof-log"
private def conjMidLog : String :=
  include_str "../acl2_samples/pattern-tests/p3-conj-mid-literal.proof-log"
private def iffOrShapeLog : String :=
  include_str "../acl2_samples/pattern-tests/p4-iff-or-shape.proof-log"
private def orShapeFlippedLog : String :=
  include_str "../acl2_samples/pattern-tests/p5-or-shape-flipped.proof-log"
private def orCollapseArithLog : String :=
  include_str "../acl2_samples/pattern-tests/p6-or-collapse-arith.proof-log"
private def clausifyDetailLog : String :=
  include_str "../acl2_samples/pattern-tests/p8-clausify-detail.proof-log"

elab "sorting_arc_pattern_pins% " : term => do
  -- (book, log, expected replayed, expected total)
  --
  -- p3-recorded-termination 2/2: THIN (1-ary through the fresh SKIP-ONE
  -- shrinker) + PRUNE (the audit-F4 2-ary negative) both replay
  -- CONDITIONALLY on the ORDINARY hypothesis-backed path: their
  -- termination replayed statements currently frontier at the NESTED-admission-
  -- induction shape ("ran out of items with no closer", *1.1), so the
  -- recorded route is NOT yet exercised by this book (audit H-4/S1: the
  -- decode chain still has exactly one covering instance, QSORT). This
  -- pin holds the count; cond-SET pinning arrives with the statement-pin
  -- work (the next segment's first item).
  --
  -- p3-conj-mid-literal 1/1 (FLIPPED, equiv-lane inc-2c 2026-07-29): the
  -- or-shape IFF normalization + or-collapse bridge + R-threaded literal
  -- chain + taut-dropped clausify + non-variable branch substitution
  -- (folds/drops) + singleton spine arms all replay — the conjunction
  -- composer's MID-LITERAL arm's first green validation (the tripwire's
  -- design purpose).
  -- p5-or-shape-flipped 1/1 UNCONDITIONAL: a second green IFF-lane
  -- instance (disjunct order flipped, dupp/rep family). Pre-merge audit
  -- correction (2026-07-30): the or-collapse does NOT fire — type-set
  -- kills the leading test (EQUAL/TYPE-SET-NIL), rewrite-if takes the
  -- constant-test path, and the or survives clausify INTACT as one
  -- literal (zero IF-FINISH/COMBINED records). Validates the iff
  -- preprocess lane, NOT the or-collapse bridge.
  -- p6-or-collapse-arith 0/1: the or-collapse bridge's second instance
  -- (the collapse fires 8x in the record and REPLAYS); a truthful
  -- tripwire at the linear-in-simplify EMISSION gap (*1/3.14', a
  -- fake-rune-for-linear leaf with no discharge node — flips when that
  -- emission lands).
  for (nm, content, expR, expT) in
      [("p3-recorded-termination", recordedTermLog, 2, 2),
       ("p3-conj-mid-literal", conjMidLog, 1, 1),
       ("p5-or-shape-flipped", orShapeFlippedLog, 1, 1),
       ("p6-or-collapse-arith", orCollapseArithLog, 0, 1)] do
    let (res, _) ← ACL2.Replay.Runner.runBook nm content none
    unless res.replayed == expR && res.total == expT &&
        res.integrityFails.isEmpty do
      throwError "pattern pin {nm}: replayed {res.replayed}/{res.total} \
        (expected {expR}/{expT}); integrity: {res.integrityFails.toList}"
  -- p6 pin TIGHTENED (pre-merge audit, 2026-07-30): the 0/1 count alone
  -- would stay green if the or-collapse bridge regressed to an EARLIER
  -- failure; pin the frontier MESSAGE — reaching *1/3.14''s
  -- ran-out-of-items means everything before it (including the 7 bridge
  -- replays) composed.
  let (resP6, _) ← ACL2.Replay.Runner.runBook "p6-or-collapse-arith" orCollapseArithLog none
  unless resP6.lines.any (fun l =>
      -- RE-PINNED (2b, linear-verdicts): the previous pin (*1/3.14' "ran
      -- out of items with no closer") WAS the linear-in-simplify emission
      -- gap — closed by emit/simplify-clause/linear-contradiction (the
      -- row's DP leaves now prove ✓); the walk advances to the
      -- DEFAULT-<-1 hypothesis-relief emission gap.
      l.startsWith "    ORDN-INSN-MID → FAIL: rule DEFAULT-<-1: hyp \
(NOT (ACL2-NUMBERP 'NIL)) has NO emitted relief record") do
    throwError "pattern pin p6-or-collapse-arith: the pinned frontier message \
      moved — got:\n{"\n".intercalate resP6.lines.toList}\nre-pin truthfully \
      (an EARLIER failure means the or-collapse bridge regressed)"
  -- p4-iff-or-shape RE-PINNED (2e, bsort-recon): the clausify-region
  -- RECON wall FELL — collectClausify now attaches the interleaved
  -- expand-and-or detail steps to their expansion markers (the tree
  -- builds; bsort's corpus entry unblocked). The book advances to its
  -- next truthful frontier: the literal chain ends still-IFF at the
  -- literal root (the R-parameterized literal-chain class, equiv-lane
  -- rung 2 — the book's original target class, now actually reachable).
  let (res, _) ← ACL2.Replay.Runner.runBook "p4-iff-or-shape" iffOrShapeLog none
  unless res.integrityFails.isEmpty && res.lines.any (fun l =>
      l.startsWith "    HAS-E-SNOC → FAIL: replayRewrites: or-shape iff \
chain still IFF at the literal root") do
    throwError "pattern pin p4-iff-or-shape: the pinned frontier moved — \
      integrity {res.integrityFails.toList}, got:\n\
      {"\n".intercalate res.lines.toList}\nre-pin truthfully (an integrity \
      failure means the clausify recon REGRESSED)"
  -- p8-clausify-detail — the DETAIL-ATTACHMENT coverage pin, at its MDD
  -- completion criterion (2026-08-01): the detail-chain replay LANDED
  -- (endgame arc, 2026-08-10 — the 2e stepwise consumption:
  -- `consumeExpandDetail` + the value-equality detail lemmas), so the
  -- book is a GREEN ROW (1/1 unconditional) with the WAYPOINT
  -- `cons_neq_detail_native_driver` (Imported/Waypoints/P8ClausifyDetail,
  -- decoded FROM the replayed statement, axioms-clean). A regression in
  -- the detail attachment or its replay flips this pin back to FAIL.
  let (resP8, _) ← ACL2.Replay.Runner.runBook "p8-clausify-detail"
    clausifyDetailLog none
  unless resP8.integrityFails.isEmpty && resP8.replayed == 1 &&
      resP8.total == 1 && resP8.lines.any (fun l =>
        l == "    CONS-NEQ-DETAIL → REPLAYED ✓") do
    throwError "pattern pin p8-clausify-detail: expected the GREEN row \
      (the landed detail-chain replay, MDD completion criterion) — \
      integrity {resP8.integrityFails.toList}, got:\n      \
      {"\n".intercalate resP8.lines.toList}"
  logInfo "sorting-arc pattern pins hold (p3-recorded-termination 2/2, \
    p3-conj-mid-literal 1/1 — the mid-literal composer validated; \
    p4-iff-or-shape at the R-parameterized literal-chain frontier; \
    p8-clausify-detail GREEN at the landed detail-chain replay)"
  return mkConst ``True.intro

-- unlimited at the command like the coverage sweep — the harness enforces
-- REAL per-theorem/per-leaf budgets internally (withRealMaxHeartbeats)
set_option maxHeartbeats 0 in
def sortingArcPatternPins : True := sorting_arc_pattern_pins%

/-! ## Perm-lane arc (2026-07-30, G2 rung 2): the congruence collapse,
    validated DECORRELATED from the qsort book (fresh relation family,
    arity-1 congruence position vs the anchor's arity-3 arg-2). -/

private def congCollapseLog : String :=
  include_str "../acl2_samples/pattern-tests/p7-cong-collapse.proof-log"

elab "perm_arc_pattern_pins% " : term => do
  -- p7-cong-collapse 4/4:
  -- - P7-TARGET — the R-COLLAPSE's decorrelated instance: SAME-LN-DUB
  --   (stored :EQUIV SAME-LN, hyp-free) applied at LN's arg-1 under the
  --   defcong SAME-LN-IMPLIES-EQUAL-LN-1, with BOTH the `rule:` (the
  --   interpreted-relation shape) and `cong:` (whole-formula replayed statement)
  --   hypotheses DISCHARGED from their replayed statements (tp:LN was
  --   the last kept condition until 2026-08-12, when the TP prover's
  --   return-path arm discharged it too — the row is unconditional now);
  -- - SAME-LN-IS-AN-EQUIVALENCE — the multi-clause clausify bridge's
  --   TAUT-DROPPED split (the sym conjunct, recorded :CLAUSE ('T)),
  --   closed by the COMMUTED-EQUAL tautology pair;
  -- - the defcong and R-rule replayed statements themselves.
  let (res, _) ← ACL2.Replay.Runner.runBook "p7-cong-collapse" congCollapseLog none
  unless res.replayed == 4 && res.total == 4 && res.integrityFails.isEmpty do
    throwError "pattern pin p7-cong-collapse: replayed \
      {res.replayed}/{res.total} (expected 4/4); integrity: \
      {res.integrityFails.toList}"
  logInfo "perm-arc pattern pins hold (p7-cong-collapse 4/4 — the \
    congruence collapse validated decorrelated)"
  return mkConst ``True.intro

set_option maxHeartbeats 0 in
def permArcPatternPins : True := perm_arc_pattern_pins%

/-! ## G1 R-lane (2026-08-14): the R-parameterized collapse's DECORRELATED
    exerciser — a different relation (SAME-LEN2), a different licence
    route (a real `defcong`), and a different R-fact source (a stored
    rule) from the anchor case (PERM-TLFIX, whose R-fact is the induction
    hypothesis and whose licence is the built-in own-position geneqv of an
    `:EQUIVALENCE` rule). -/

private def congConsumeLog : String :=
  include_str "../acl2_samples/pattern-tests/cov-cong-consume.proof-log"

elab "r_lane_pattern_pins% " : term => do
  -- cov-cong-consume 3/4 — a FRONTIER pin (the tripwire flips loudly when
  -- the blocking frontier lands). The three green rows are the pieces the
  -- R-collapse consumes (the defequiv statement, the defcong statement,
  -- the R-rule's own statement); the fourth, LEN-CONS-UNDER-CONG, is the
  -- consumption itself and stops at a frontier the G1 lane does NOT
  -- cover: the stored rule `CONS-NORM-SAME-LEN2` carries ONE hypothesis —
  -- ACL2's `SYNP` syntactic guard, from the book's `syntaxp` (the
  -- emitted :TFORMULA is `(IMPLIES (SYNP 'NIL '(SYNTAXP (NOT (QUOTEP A)))
  -- …) (SAME-LEN2 …))`) — and the R-fact route replays hyp-free R-rules
  -- only, exactly as the preprocess lane's collapse always has. SYNP
  -- relief is a stored-rule HYPOTHESIS class, not a congruence question.
  -- Second recorded finding (documented, not worked around): this
  -- R-step's OWN `:RUNES` are `((:DEFINITION SYNP))` — the licensing
  -- `(:CONGRUENCE SAME-LEN2-IMPLIES-EQUAL-LEN-1)` appears only in the
  -- CLAUSE-level `:STEP :RUNES`, so even past SYNP the step-level BUG-023
  -- anchor the walker uses would find no cited congruence. The queued
  -- `:CR-RUNE` fork item (brief §Q2) is the tightening that fixes both
  -- lanes' anchor at the source.
  let (res, _) ← ACL2.Replay.Runner.runBook
    "cov-cong-consume" congConsumeLog none
  unless res.replayed == 3 && res.total == 4 && res.integrityFails.isEmpty do
    throwError "pattern pin cov-cong-consume: replayed \
      {res.replayed}/{res.total} (expected 3/4 — the SYNP-guarded R-rule \
      frontier); integrity: {res.integrityFails.toList}\n      \
      {"\n".intercalate res.lines.toList}"
  unless res.lines.any (fun l => (l.splitOn
      "LEN-CONS-UNDER-CONG → FAIL: R-step: rule CONS-NORM-SAME-LEN2 \
carries 1 hyps").length ≥ 2) do
    throwError "pattern pin cov-cong-consume: LEN-CONS-UNDER-CONG is not \
      at the recorded SYNP frontier — the tripwire moved:\n      \
      {"\n".intercalate res.lines.toList}"
  logInfo "G1 R-lane pattern pins hold (cov-cong-consume 3/4 — the \
    class-D consumption pinned at the SYNP-guarded R-rule frontier)"
  return mkConst ``True.intro

set_option maxHeartbeats 0 in
def rLanePatternPins : True := r_lane_pattern_pins%

/-! ## Swap family (fold-back audit fix round 2026-07-31): the books whose
    headers exist to pin rewrite-if's `(if x nil t)` branch swap — the
    audit found the family had NO Lean gate at all while carrying most of
    the V2/V3 emission witnesses. Pinned on the `:SWAPPED-P`-emitting logs
    (acl2 9f12ded573). -/

private def swapDescendLog : String :=
  include_str "../acl2_samples/pattern-tests/p1-swap-descend.proof-log"
private def swapDoubleNegLog : String :=
  include_str "../acl2_samples/pattern-tests/p1-swap-double-neg.proof-log"
private def swapJointLog : String :=
  include_str "../acl2_samples/pattern-tests/p1-swap-joint.proof-log"

elab "swap_family_pattern_pins% " : term => do
  -- p1-swap-descend 1/1: the descend/target swap bridge's home book
  -- (ZIPW-TRUE-LISTP) — the swap fires in the record (:SWAPPED-P T on the
  -- if-left window at argument 3) and the replay composes through it.
  -- p1-swap-double-neg 1/1 UNCONDITIONAL: iterated swap ×2 (the double
  -- negation cancels).
  -- p1-swap-joint 1/1 (CNTNE-CONS): the (NOT (EQUAL …)) body-test swap
  -- resolved through the branch-anchored window context (the fix-round's
  -- assume-true-false rework).
  for (nm, content, expR, expT) in
      [("p1-swap-descend", swapDescendLog, 1, 1),
       ("p1-swap-double-neg", swapDoubleNegLog, 1, 1),
       ("p1-swap-joint", swapJointLog, 1, 1)] do
    let (res, _) ← ACL2.Replay.Runner.runBook nm content none
    unless res.replayed == expR && res.total == expT &&
        res.integrityFails.isEmpty do
      throwError "pattern pin {nm}: replayed {res.replayed}/{res.total} \
        (expected {expR}/{expT}); integrity: {res.integrityFails.toList}"
  logInfo "swap-family pattern pins hold (p1-swap-descend 1/1, \
    p1-swap-double-neg 1/1, p1-swap-joint 1/1)"
  return mkConst ``True.intro

set_option maxHeartbeats 0 in
def swapFamilyPatternPins : True := swap_family_pattern_pins%

/-! ## Empty-encapsulate success exits (fresh-verify N1, 2026-08-03): a
    LOCAL-ONLY encapsulate exits by `:empty-encapsulate` on BOTH the
    proving path (helper book, captured directly) and the include-book
    path (include book — the FOURTH success exit, whose
    `(:ENCAPSULATE-END)` the first bracket fix round missed; pre-fix the
    include capture left the BEGIN unclosed and `buildDevelopment`
    hard-failed a legitimate ACL2 pattern). -/

private def encEmptyHelperLog : String :=
  include_str "../acl2_samples/pattern-tests/cov-encapsulate-empty-helper.proof-log"
private def encEmptyIncludeLog : String :=
  include_str "../acl2_samples/pattern-tests/cov-encapsulate-empty-include.proof-log"

elab "encapsulate_empty_pins% " : term => do
  -- helper 1/1: the local defthm proves during direct ld and replays.
  let (res, _) ← ACL2.Replay.Runner.runBook
    "cov-encapsulate-empty-helper" encEmptyHelperLog none
  unless res.replayed == 1 && res.total == 1 && res.integrityFails.isEmpty do
    throwError "pattern pin cov-encapsulate-empty-helper: replayed \
      {res.replayed}/{res.total} (expected 1/1); integrity: \
      {res.integrityFails.toList}"
  -- include book: recon must SUCCEED (bracket balance holds — the N1
  -- teeth; pre-fix this hard-failed "1 unclosed (:ENCAPSULATE-BEGIN)").
  -- 0 theorems is TRUTHFUL (include-book skips proofs; the local probe
  -- never re-proves), so runBook's zero-theorems integrity heuristic is
  -- expected here and recon is pinned directly instead.
  match (ProofLog.parse encEmptyIncludeLog).bind ClauseTree.buildDevelopment with
  | .error msg =>
    throwError "pattern pin cov-encapsulate-empty-include: parse/recon \
      FAILED — the include-path empty-encapsulate bracket balance \
      regressed (N1): {msg}"
  | .ok _ => pure ()
  logInfo "encapsulate-empty pins hold (helper 1/1; include-path \
    empty-encapsulate balanced + reconstructed)"
  return mkConst ``True.intro

set_option maxHeartbeats 0 in
def encapsulateEmptyPins : True := encapsulate_empty_pins%

end ACL2.Tests.PatternPins
