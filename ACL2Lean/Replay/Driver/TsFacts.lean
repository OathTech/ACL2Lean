/-
  Driver/TsFacts — THE TYPING-TEST REGISTRY (T1+2 sprint P3b,
  2026-08-15).

  ACL2 turns a branch's ruling TESTS into type-alist entries
  (`assume-true-false`); every consumer of an emitted type-set has to
  reconstruct the same entries from the facts it can see. Two consumers
  now exist —

    * the ADMISSION walk's `tsFromFacts` (Driver/TsConsumer), which reads
      the totality walker's own branch facts, and
    * the CLAUSE-context `inTsFromCtx` (Driver/NodeCore/TypeSetWalk),
      which asks the type-set walker whether the clause context
      establishes a test —

  and they must not drift, so the MASKS and the PROVED MODEL LEMMAS live
  HERE, once. `tsFactOf` is the MATCHING side (an emitted fact ↦ what it
  types); `tsCtxProbes` is the GENERATING side (which tests to ask about
  a term). A probe whose test `tsFactOf` does not recognize contributes
  nothing, so the two can only ever agree.

  `tsFactOf` moved here from Driver/TsConsumer unchanged (T1+2 sprint
  phase 1's definition) — a MOVE, not a clone.
-/
import ACL2Lean.Replay.Lemmas.TsAlgebra
import ACL2Lean.Replay.Driver.BranchFacts

namespace ACL2.Replay.Driver

open ACL2

/-- `(QUOTE 0)` — the constant ACL2's `assume-true-false` splits `<` on. -/
def tsQuotedZero : SExpr :=
  .cons (.atom (.symbol { name := "QUOTE" }))
    (.cons (.atom (.number (.int 0))) .nil)

/-- Read an in-scope BRANCH FACT as a type-set statement about one term:
    `(test-term, truth-value)` ↦ `(the term it types, the mask, the proved
    fact)`. These are the ONLY way an `InTs` fact enters a walk — a
    recognizer the body itself tested, on the branch the walk is in.

    Each proved fact takes `Logic.toBool <the test's lifted value> =
    <the polarity>` and lands in the mask ACL2's own type-set machinery
    uses for that test. -/
def tsFactOf (f : SExpr) (pos : Bool) : Option (SExpr × Int × Lean.Name) :=
  match f with
  | .cons (.atom (.symbol r)) (.cons a .nil) =>
    if r.name == "INTEGERP" && pos then
      some (a, 23, ``ACL2.Replay.inTs_integerp_true)
    else none
  | .cons (.atom (.symbol r)) (.cons a (.cons b .nil)) =>
    if r.name == "<" && b == tsQuotedZero then
      if pos then some (a, 48, ``ACL2.Replay.inTs_lt_zero_true)
      else some (a, -49, ``ACL2.Replay.inTs_lt_zero_false)
    else if r.name == "<" && a == tsQuotedZero && pos then
      -- the constant on the LEFT (`CLASSIFY-POS`'s `(< '0 N)` hypothesis)
      some (b, 14, ``ACL2.Replay.inTs_zero_lt_true)
    else none
  | _ => none

/-- The typing TESTS to ask the clause context about for a term `t` —
    the GENERATING side of `tsFactOf`. Demand-driven: one shape per
    registry entry above, and the result is interpreted back THROUGH
    `tsFactOf`, so a shape listed here that the registry does not
    recognize simply contributes nothing. -/
def tsCtxProbes (t : SExpr) : List SExpr :=
  let app1 (f : String) (a : SExpr) : SExpr :=
    .cons (.atom (.symbol { name := f })) (.cons a .nil)
  let app2 (f : String) (a b : SExpr) : SExpr :=
    .cons (.atom (.symbol { name := f })) (.cons a (.cons b .nil))
  [app1 "INTEGERP" t, app2 "<" t tsQuotedZero, app2 "<" tsQuotedZero t]

/-- TEST-NIL registry — the `.isNil` direction of `tsFactOf`: a test
    term ↦ `(the term it types, the test's own TRUE type-set, the proved
    model fact `tsDisjointM m <trueTs> = true → InTs m arg → <the test's
    value> = nil`)`. Same masks, opposite direction; ACL2 records such a
    resolution only as an `:IF-TEST-FALSE` marker with a
    `fake-rune-for-type-set` justification, so the replay reconstructs
    the type-set derivation exactly as the D-A consumer does elsewhere.
    Demand-driven: `CLASSIFY-POS`'s `(< N '0)` is the corpus witness. -/
def tsTestNilOf (t : SExpr) : Option (SExpr × Int × Lean.Name) :=
  match t with
  | .cons (.atom (.symbol r)) (.cons a (.cons b .nil)) =>
    if r.name == "<" && b == tsQuotedZero then
      some (a, 48, ``ACL2.Replay.logic_lt_zero_nil_of_ts_disjoint)
    else none
  | _ => none

/-- RECOGNIZER-VERDICT registry, `'T` side: recognizer ↦ (ACL2's TRUE
    type-set for it, the proved fact
    `tsSubsumedM m <trueTs> = true → InTs m v → <recog> v = 'T`). The
    step's OWN emitted `:TRUETS` is cross-checked against the registry
    number before the fact is used, so a drifted emission fails closed.
    Demand-driven: `CD2-BOUND`'s `(INTEGERP N) ⇒ 'T`. -/
def tsRecogTrue : List (String × Int × Lean.Name) :=
  [("INTEGERP", 23, ``ACL2.Replay.logic_integerp_t_of_inTs),
   ("NATP", 7, ``ACL2.Replay.logic_natp_t_of_inTs)]

/-- RECOGNIZER-VERDICT registry, `'NIL` side: recognizer ↦ (its TRUE
    type-set, the proved fact
    `tsDisjointM m <trueTs> = true → InTs m v → <recog> v = 'NIL`).
    Demand-driven: the trio's `(CONSP (IF …)) ⇒ 'NIL`. -/
def tsRecogNil : List (String × Int × Lean.Name) :=
  [("CONSP", 3072, ``ACL2.Replay.logic_consp_nil_of_ts_disjoint),
   ("ZP", -7, ``ACL2.Replay.logic_zp_nil_of_ts_disjoint)]

/-- ARITHMETIC-PRIMITIVE ts registry: a 2-ary primitive ↦ (the in-mask
    the proved fact demands of BOTH arguments, the out-mask it
    establishes, the fact). ACL2's `type-set-binary-+` mirrored one cell
    at a time — ACL2 stores no rule for the primitives, so its only
    statement about such an occurrence is the emitted verdict and the
    implication is ours to prove. Demand-driven: the
    arithmetic-countdown trio's `(BINARY-+ '-1 N)` / `(BINARY-+ '-2 N)`
    arguments. -/
def tsBinaryOf (op : String) : Option (Int × Int × Lean.Name) :=
  if op == "BINARY-+" then some (23, 23, ``ACL2.Replay.inTs_plus_int)
  else none

/-- COMPOUND-RECOGNIZER probes — `(rune name, the recognizer fn, the mask
    its REFUTED branch establishes, the proved model fact)`. Kept apart
    from `tsCtxProbes` because a compound recognizer is a RULE, not a
    primitive: it may be consumed ONLY where the step's own ttree cites
    its rune (the BUG-023 anchor), so the caller passes the cited names
    and an uncited entry is never probed.

    `ZP-COMPOUND-RECOGNIZER`: ACL2 states `(zp x)`'s negative branch as
    `(and (integerp x) (< 0 x))` — mask 6 = one ∪ integer>1. Corpus
    witness: `CD2-BOUND` (`acl2_samples/recon-tests/11-custom-measure`),
    whose `(INTEGERP N) ⇒ 'T` recognizer step cites exactly this rune. -/
def tsCompoundRecogProbes : List (String × String × Int × Lean.Name) :=
  [("ZP-COMPOUND-RECOGNIZER", "ZP", 6, ``ACL2.Replay.inTs_zp_false)]

end ACL2.Replay.Driver
