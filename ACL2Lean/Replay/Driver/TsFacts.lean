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
import ACL2Lean.ProofLog

namespace ACL2.Replay.Driver

open ACL2

/-- The COMPOUND-RECOGNIZER runes an `:IF-TEST-TRUE/FALSE` marker CITES,
    read off the marker's OWN `:JUSTIFICATION` ttree.

    ACL2's `rewrite-if-finish` resolves a test from the type-alist and
    returns the surviving branch, recording the marker plus the ttree
    that carried the decision. That ttree IS the basis, so a
    marker-anchored collapse must consume exactly it — the BUG-023
    direction (the RECORD's own runes, never the clause-level set) that
    `Node.lean`'s recognizer site and `compoundRecogTsCell` already take.
    Without it a compound-recognizer probe is never licensed and the
    collapse fails closed even though ACL2 recorded its reason.

    Three `:JUSTIFICATION` shapes are attested across all 5040 IF-test
    markers in the corpus: `NIL` (the test was NOT resolved —
    `:IF-TEST-UNKNOWN`), `:REWRITTEN-TO-CONSTANT` (the test rewrote to a
    quoted constant, so the basis is the recorded chain and not a
    ttree), and the type-set ttree `(:RUNES <runes> :PARENTS <parents>)`.
    Anything else is a NEW emission shape to design for: hard-fail,
    never swallow. -/
def ifMarkerCitedCr (justification : SExpr) : Except String (List String) :=
  match justification with
  | .nil => pure []
  | .atom (.keyword k) =>
    if k == "REWRITTEN-TO-CONSTANT" then pure [] else
      throw s!"ifMarkerCitedCr: unmodeled :IF-TEST :JUSTIFICATION \
               keyword {repr justification}"
  | .cons (.atom (.keyword k)) (.cons runes _) =>
    if k == "RUNES" then do
      let rs ← ProofLog.parseRunes runes
      pure (rs.filterMap fun r =>
        if r.ty == "compound-recognizer" then some r.name else none)
    else
      throw s!"ifMarkerCitedCr: unmodeled :IF-TEST :JUSTIFICATION \
               ttree {repr justification}"
  | _ =>
    throw s!"ifMarkerCitedCr: unmodeled :IF-TEST :JUSTIFICATION shape \
             {repr justification}"

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
   ("NATP", 7, ``ACL2.Replay.logic_natp_t_of_inTs),
   ("ZP", -7, ``ACL2.Replay.logic_zp_t_of_inTs)]

/-- ACL2'S MASK, READ AGAINST OURS UNDER THE MODEL'S PINNED DOMAIN
    RESTRICTION (T1+2 sprint P4b, `CD2-BOUND`).

    `recogVerdictFromTs`'s cross-check asks that ACL2's emitted
    `:TYPESET` be INSIDE the mask the replay derived — "we may prove
    something weaker than ACL2 knew, never something it contradicts".
    Basic type INDEX 6 is `*ts-complex-rational*`, and the model has NO
    complex values at all (BUG-009): `tsIndex` never returns 6, so
    `InTs m v` and `InTs (m ∪ {6}) v` are the SAME proposition here and
    a derived mask can never carry that bit. ACL2's `<` does order
    complex rationals, so `(< N '0)` true gets `:TYPESET 112` where the
    model derives `48` — 112 = 48 ∪ {bit 6} exactly.

    So the comparison DISCOUNTS index 6 and nothing else: ACL2's mask
    must be inside ours ∪ {complex-rational}. Any OTHER bit ACL2 has and
    we do not still fails the check, closed. This is not a weaker
    verdict — the proof still runs on OUR mask `m` and OUR `InTs` fact —
    it is the BUG-009 domain restriction applied at one more site, the
    same treatment `mkVacuousTruthyBranch` already gives ACL2's complex
    admission case. Delete the discount the day complex rationals are
    modeled (BUG-009's fix makes index 6 inhabited and this becomes
    unsound to skip). -/
def tsAcl2MaskOk (acl2Ts derived : Int) : Bool :=
  (List.range 14).all fun i =>
    i == 6 || !ACL2.Replay.tsMember acl2Ts i
      || ACL2.Replay.tsMember derived i

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

/-- The QUOTED-CONSTANT reading of a term: `'k` ↦ `k`, for an INTEGER
    `k`. The one shape `tsPlusConstOf` is keyed on. -/
def quotedInt? (t : SExpr) : Option Int :=
  match t with
  | .cons (.atom (.symbol q)) (.cons (.atom (.number (.int k))) .nil) =>
    if q.name == "QUOTE" then some k else none
  | _ => none

/-- ARITHMETIC-PRIMITIVE ts registry, the SHARP CONSTANT cells:
    `(the quoted constant, the OTHER argument's mask)` ↦ `(the resulting
    mask, the proved fact)`. Same rule as `tsBinaryOf` — ACL2's
    `type-set-binary-+` mirrored ONE CELL AT A TIME, the verdict ACL2's
    and the implication ours to prove — but keyed on the constant as
    well, because ACL2's partition keeps `*ts-one*` precisely so that
    adding `∓1` stays sharp where the plain integer cell (23 + 23 ⊆ 23)
    would not.

    `(-1, 6) ↦ 7`: mask 6 is `ZP-COMPOUND-RECOGNIZER`'s refuted branch
    (the integers `≥ 1`) and mask 7 is the integers `≥ 0`.
    Demand-driven, and the emission itself demonstrates the asymmetry:
    `COUNT-DOWN` / `MY-EVENP` emit `:TYPESET 7` for `(BINARY-+ '-1 N)`
    under that branch, while `CD2`'s `(BINARY-+ '-2 N)` gets the coarse
    23 — so there is no `-2` cell to add. -/
def tsPlusConstOf (k : Int) (m : Int) : Option (Int × Lean.Name) :=
  if k == -1 && m == 6 then some (7, ``ACL2.Replay.inTs_plus_neg_one)
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
