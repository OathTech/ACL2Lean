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
  -- p4-iff-or-shape (equiv-lane arc): a TRUTHFUL RECON TRIPWIRE — the
  -- book lands on the KNOWN clausify-region reconstruction wall (the
  -- bsort wall: clausify-input's second expand-abbreviations interleaves
  -- steps into the clausify event stream). The pin flips when that wall
  -- falls, which also unblocks bsort's corpus entry.
  let (res, _) ← ACL2.Replay.Runner.runBook "p4-iff-or-shape" iffOrShapeLog none
  unless res.integrityFails.size == 1 &&
      ((res.integrityFails[0]!).splitOn "collectClausify").length > 1 do
    throwError "pattern pin p4-iff-or-shape: expected the clausify-region \
      RECON tripwire, got integrity {res.integrityFails.toList} \
      ({res.replayed}/{res.total} replayed) — the wall moved: re-pin \
      truthfully"
  logInfo "sorting-arc pattern pins hold (p3-recorded-termination 2/2, \
    p3-conj-mid-literal 1/1 — the mid-literal composer validated; \
    p4-iff-or-shape recon-tripwire)"
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
  --   hypotheses DISCHARGED from their replayed statements — only tp:LN kept;
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

end ACL2.Tests.PatternPins
