import ACL2Lean.Replay.Driver.NodeCore.Recognizer
import ACL2Lean.Replay.Lemmas.TpClosure

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

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
  -- The same recorded mask consumer used by explicit recognizer nodes.
  -- INTEGERP-MOD supplies argTs 59 / trueTs 63 for RATIONALP(UNARY-/ N).
  let fact? ← recogVerdictFromTs cfg ctx recog.name arg .t
    (some basis.argTs) (some basis.trueTs) [] []
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
  let .cons (.atom (.symbol recog)) (.cons arg .nil) := hyp | return none
  unless basis.term == arg && basis.rune.isSome do return none
  let some (_, trueTs, _) := tsRecogTrue.find? (fun (n, _, _) => n == recog.name)
    | return none
  unless basis.targetTs == trueTs && tsSubsumedM basis.entryTs trueTs do return none
  let citedCr := prov.taRunes.filterMap fun r =>
    if r.ty == "compound-recognizer" then some r.name else none
  let some fact ← recogVerdictFromTs cfg ctx recog.name arg .t
      (some basis.entryTs) (some basis.targetTs) [] citedCr | return none
  let conv ← mkAppM ``re_val_cast
    #[cfg.worldExpr, cfg.envExpr, reflectSExpr hyp, ← ctxValExpr cfg ctx hyp,
      mkConst ``SExpr.t, ← ctxValProof cfg ctx hyp, fact]
  return some (← mkAppM ``evtrue_of_eq_t #[conv])

end ACL2.Replay.Driver
