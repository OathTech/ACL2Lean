import ACL2Lean.Replay.Driver.NodeCore

namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

/-- A named primitive axiom used through :USE rather than a rewrite rune.
Its source schema is instantiated with the recorded translated substitution
and checked verbatim against :HYPS. The ordinary USE consumer still replays
the application clause; this supplies only the cited axiom premise. -/
def primitiveUseInstance? (cfg : ReplayConfig) (ctx : ReplayCtx) (name : String)
    (subst : List (Symbol × SExpr)) (hyp : SExpr) : MetaM (Option (Expr × ReplayCtx)) := do
  if name != "DISTRIBUTIVITY" then return none
  -- axioms.lisp: (equal (* x (+ y z)) (+ (* x y) (* x z))).
  let sym := fun n => SExpr.atom (.symbol { name := n })
  let app := fun n xs => SExpr.cons (sym n) (SExpr.ofList xs)
  let x := sym "X"
  let y := sym "Y"
  let z := sym "Z"
  let lhs := app "BINARY-*" [x, app "BINARY-+" [y, z]]
  let rhs := app "BINARY-+" [app "BINARY-*" [x, y], app "BINARY-*" [x, z]]
  let instantiate := substTerm (subst.map (·.1)) (subst.map (·.2))
  unless instantiate (app "EQUAL" [lhs, rhs]) == hyp do
    throwError "primitive use:{name}: recorded substitution disagrees with :HYPS"
  let ctx ← pinTermOpaques cfg cfg.envExpr ctx hyp
  let law ← mkAppM ``Logic.times_add #[← ctxValExpr cfg ctx (instantiate x),
    ← ctxValExpr cfg ctx (instantiate y), ← ctxValExpr cfg ctx (instantiate z)]
  let equalIff ← mkAppM ``Logic.equal_t_iff
    #[← ctxValExpr cfg ctx (instantiate lhs), ← ctxValExpr cfg ctx (instantiate rhs)]
  let ht ← mkAppM ``Iff.mpr #[equalIff, law]
  let tNeNil ← mkDecideProof (← mkAppM ``Ne #[mkConst ``SExpr.t, mkConst ``SExpr.nil])
  let hne ← mkAppM ``ne_of_eq_of_ne #[ht, tNeNil]
  let pf ← mkAppM ``evtrue_of_conv_ne_nil #[← ctxValProof cfg ctx hyp, hne]
  return some (pf, ctx)

end ACL2.Replay.Driver
