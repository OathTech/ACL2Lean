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
  -- termination mirrors currently frontier at the NESTED-admission-
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
  -- instance (disjunct order flipped, dupp/rep family) — clausify splits
  -- its or apart, so it validates the iff preprocess lane, NOT the
  -- or-collapse bridge.
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
    let res ← ACL2.Replay.Runner.runBook nm content none
    unless res.replayed == expR && res.total == expT &&
        res.integrityFails.isEmpty do
      throwError "pattern pin {nm}: replayed {res.replayed}/{res.total} \
        (expected {expR}/{expT}); integrity: {res.integrityFails.toList}"
  -- p4-iff-or-shape (equiv-lane arc): a TRUTHFUL RECON TRIPWIRE — the
  -- book lands on the KNOWN clausify-region reconstruction wall (the
  -- bsort wall: clausify-input's second expand-abbreviations interleaves
  -- steps into the clausify event stream). The pin flips when that wall
  -- falls, which also unblocks bsort's corpus entry.
  let res ← ACL2.Replay.Runner.runBook "p4-iff-or-shape" iffOrShapeLog none
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

end ACL2.Tests.PatternPins
