import ACL2Lean.Replay.Driver.NodeCore.Recognizer
import ACL2Lean.Replay.Lemmas.TpClosure

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

private def basisCitations (prov : StepProvenance) : List String × List String :=
  (prov.taRunes.filterMap (fun r =>
    if r.ty == "compound-recognizer" then some r.name else none),
   prov.taRunes.filterMap (fun r =>
    if r.ty == "type-prescription" then some r.name else none))

/-- New known-true captures carry the original recursive query. Consume it
before legacy relief adapters; failure after selecting this record is final. -/
def replayKnownTrueQuery? (cfg : ReplayConfig) (ctx : ReplayCtx)
    (hyp : SExpr) (markers : List ProofNode) : MetaM (Option Expr) := do
  let some (.node _ _ _ _ prov) := markers.find? (fun n => (nodeLhsRhs n).1 == hyp)
    | return none
  let some raw := prov.hypTypeSetBasis | return none
  unless prov.origin == "relieve-hyp/known-true" do
    throwError "known query: record on unsupported relief origin"
  let (mask, p) ← replayOperandTsQuery cfg ctx hyp raw
  unless !tsMember mask 7 do throwError "known query: result does not establish truth"
  let hn ← mkAppM ``ne_nil_of_inTs #[← mkDecideProof
    (← mkEq (← mkAppM ``tsMember #[toExpr mask, toExpr (7 : Nat)]) (toExpr false)), p]
  return some (← mkAppM ``evtrue_of_conv_ne_nil #[← ctxValProof cfg ctx hyp, hn])

/-- Consume the selected primitive table route for a zero/positive-rational
comparison. Both masks and the numeric projection come from the actual query;
the existing type-set walk proves membership before the primitive law applies.
An emitted alternative route is retained and refused, never re-solved. -/
def replayKnownTrueComparison? (cfg : ReplayConfig) (ctx : ReplayCtx)
    (hyp : SExpr) (markers : List ProofNode) : MetaM (Option Expr) := do
  let some (.node _ _ _ _ prov) := markers.find? (fun n => (nodeLhsRhs n).1 == hyp)
    | return none
  let some basis := prov.comparisonBasis | return none
  unless prov.origin == "relieve-hyp/known-true" do
    throwError "known comparison: basis on unsupported relief origin"
  let some [.atom (.keyword "TABLE"), .atom (.keyword "LEFT-TS"),
      .atom (.number (.int mL)), .atom (.keyword "RIGHT-TS"), .atom (.number (.int mR)),
      .atom (.keyword "NUMERIC-LEFT-TS"), .atom (.number (.int nL)),
      .atom (.keyword "NUMERIC-RIGHT-TS"), .atom (.number (.int nR)),
      .atom (.keyword "RESULT"), .atom (.number (.int result))] := basis.route.toList?
    | throwFrontier m!"known comparison: unsupported recorded route {repr basis.route}"
  unless basis.resultTs == 256 && result == basis.resultTs &&
      mL == 1 && nL == mL && nR == mR && tsSubsumedM mR 14 do
    throwFrontier m!"known comparison: unsupported or inconsistent table masks {repr basis}"
  let some (fn, [a, b]) := asApp hyp
    | throwError "known comparison: malformed application"
  unless fn.name == "<" && quotedInt? a == some 0 do
    throwFrontier m!"known comparison: table cell requires the recorded zero left operand"
  let (citedCr, citedTp) := basisCitations prov
  let some hB ← inTsFromCtx cfg ctx [] citedCr b (← ctxValExpr cfg ctx b) mR citedTp
    | throwFrontier m!"known comparison: cannot establish recorded right mask {mR}"
  let fact ← mkAppM ``zero_lt_of_inTs #[← tsSubsumedProofM mR 14, hB]
  let conv ← mkAppM ``re_val_cast
    #[cfg.worldExpr, cfg.envExpr, reflectSExpr hyp, ← ctxValExpr cfg ctx hyp,
      mkConst ``SExpr.t, ← ctxValProof cfg ctx hyp, fact]
  return some (← mkAppM ``evtrue_of_eq_t #[conv])

/-- The actual root-IF basis follows the existing addressed leaf walk. Its
recorded result must exclude NIL; an unsupported leaf remains a frontier. -/
def replayKnownTrueIf? (cfg : ReplayConfig) (ctx : ReplayCtx)
    (hyp : SExpr) (markers : List ProofNode) : MetaM (Option Expr) := do
  let some (.node _ _ _ _ prov) := markers.find? (fun n => (nodeLhsRhs n).1 == hyp)
    | return none
  unless prov.origin == "relieve-hyp/known-true" do return none
  let some basis := prov.ifBasis | return none
  let .cons (.atom (.symbol fn)) args := hyp | return none
  unless fn.name == "IF" && args.toList?.map List.length == some 3 do return none
  unless tsMember basis.resultTs 7 == false do return none
  let (citedCr, citedTp) := basisCitations prov
  let some h ← inTsFromArgLeaves cfg ctx basis.leaves [] citedCr hyp basis.resultTs citedTp
    | return none
  let hMask ← mkDecideProof (← mkEq
    (← mkAppM ``ACL2.Replay.tsMember #[Lean.toExpr basis.resultTs, Lean.toExpr (7 : Nat)])
    (mkConst ``Bool.false))
  let hNe ← mkAppM ``ACL2.Replay.ne_nil_of_inTs #[hMask, h]
  return some (← mkAppM ``evtrue_of_conv_ne_nil #[← ctxValProof cfg ctx hyp, hNe])

/-- A primitive value closure at an actually recorded known-true recognizer
query. The marker supplies the exact argument type-set and enabled tuple;
missing basis or an unregistered primitive remains a frontier. No type-set
is inferred here, and the value proof still checks against the evaluator. -/
def replayKnownTruePrimitive? (cfg : ReplayConfig) (ctx : ReplayCtx)
    (hyp : SExpr) (markers : List ProofNode) : MetaM (Option Expr) := do
  let some (.node _ _ _ _ prov) := markers.find? (fun n => (nodeLhsRhs n).1 == hyp)
    | return none
  unless prov.origin == "relieve-hyp/known-true" do return none
  let some basis := prov.recogBasis | return none
  let .cons (.atom (.symbol recog)) (.cons arg .nil) := hyp | return none
  checkRecogVerdict basis.argTs basis.trueTs basis.falseTs recog.name true
  let (citedCr, citedTp) := basisCitations prov
  -- The same recorded mask consumer used by explicit recognizer nodes.
  -- INTEGERP-MOD supplies argTs 59 / trueTs 63 for RATIONALP(UNARY-/ N).
  let fact? ← recogVerdictFromTs cfg ctx recog.name arg .t
    (some basis.argTs) (some basis.trueTs) [] citedCr citedTp
  let fact ← match fact? with
    | some fact => pure fact
    | none =>
      let .cons (.atom (.symbol fn)) (.cons a (.cons b .nil)) := arg | return none
      unless recog.name == "ACL2-NUMBERP" do return none
      let some lemmaName :=
          [("BINARY-+", ``acl2NumberpCor_closed_plus),
           ("BINARY-*", ``acl2NumberpCor_closed_times)].lookup fn.name | return none
      mkAppM lemmaName #[← ctxValExpr cfg ctx a, ← ctxValExpr cfg ctx b,
        mkConst ``True.intro, mkConst ``True.intro]
  let p ← ctxValProof cfg ctx hyp
  let conv ← mkAppM ``re_val_cast
    #[cfg.worldExpr, cfg.envExpr, reflectSExpr hyp, ← ctxValExpr cfg ctx hyp,
      mkConst ``SExpr.t, p, fact]
  return some (← mkAppM ``evtrue_of_eq_t #[conv])

/-- Replay the recorded successful type-alist lookup through the shared
mask consumer. The entry term must be exactly the recognizer argument;
its recorded type must be inside the mask that ACL2 actually requested. -/
def replayHypLookupFromBasis? (cfg : ReplayConfig) (ctx : ReplayCtx)
    (hyp : SExpr) (markers : List ProofNode) : MetaM (Option Expr) := do
  let some (.node _ _ _ _ prov) := markers.find? (fun n => (nodeLhsRhs n).1 == hyp)
    | return none
  unless prov.origin == "relieve-hyp/type-alist" do return none
  let some basis := prov.lookupBasis | return none
  let (test, positive) := match asApp hyp with
    | some (f, [a]) => if f.name == "NOT" then (a, false) else (hyp, true)
    | _ => (hyp, true)
  let .cons (.atom (.symbol recog)) (.cons arg .nil) := test | return none
  unless basis.term == arg && basis.rune.isSome do return none
  let registry := if positive then tsRecogTrue else tsRecogNil
  let some (_, trueTs, _) := registry.find? (fun (n, _, _) => n == recog.name)
    | return none
  -- A negated recognizer requests the complement of the true mask.
  -- Both masks are checked against the actual successful lookup; the
  -- same primitive verdict consumer proves the unnegated test false.
  let target := if positive then trueTs else -trueTs - 1
  unless basis.targetTs == target && tsSubsumedM basis.entryTs target do return none
  if !positive then
    unless basis.rune == some ⟨"fake-rune-for-anonymous-enabled-rule", "NIL", none⟩ do
      throwFrontier m!"hyp lookup: negated recognizer uses an unsupported cited rune"
  let citedCr := prov.taRunes.filterMap fun r =>
    if r.ty == "compound-recognizer" then some r.name else none
  let some fact ← recogVerdictFromTs cfg ctx recog.name arg (if positive then .t else .nil)
      (some basis.entryTs) (some trueTs) [] citedCr | return none
  let fact ← if positive then pure fact else mkAppM ``logic_not_t_of_nil #[fact]
  let conv ← mkAppM ``re_val_cast
    #[cfg.worldExpr, cfg.envExpr, reflectSExpr hyp, ← ctxValExpr cfg ctx hyp,
      mkConst ``SExpr.t, ← ctxValProof cfg ctx hyp, fact]
  return some (← mkAppM ``evtrue_of_eq_t #[conv])

end ACL2.Replay.Driver
