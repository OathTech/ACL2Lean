import ACL2Lean.Logic
import Lean

namespace ACL2
namespace Tactics

open Logic Lean Elab Tactic Meta

/--
Helper to find the first recursive function application in an expression.
-/
partial def findRecursiveApp (e : Expr) : MetaM (Option (Name × Array Expr)) := do
  let env ← getEnv
  match e with
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    if let .const declName .. := fn then
      -- Check if it's a recursive definition (has an induct principle)
      if env.contains (declName ++ `induct) then
        let s := declName.toString
        -- Filter out common tactic/logic/init/lean namespaces
        let isBuiltin := s.startsWith "Lean" || s.startsWith "Init" || s.startsWith "ACL2.Logic" || s.startsWith "ACL2.Tactics" || s == "toBool" || s == "if_" || s == "toInt" || s == "toNat" || s == "not" || s == "equal"
        if !isBuiltin then
          return some (declName, args)
    for arg in args do
      if let some res ← findRecursiveApp arg then
        return some res
    return none
  | .lam _ _ b _ => findRecursiveApp b
  | .forallE _ _ b _ => findRecursiveApp b
  | .letE _ _ v b _ => do
    match ← findRecursiveApp v with
    | some res => return some res
    | none => findRecursiveApp b
  | .mdata _ e => findRecursiveApp e
  | .proj _ _ e => findRecursiveApp e
  | _ => return none

macro "acl2_simp" : tactic =>
  `(tactic| simp [Logic.toBool, Logic.if_, Logic.plus, Logic.minus, Logic.times, Logic.div,
                 Logic.lt, Logic.eq, Logic.equal, Logic.consp, Logic.atom, Logic.car,
                 Logic.cdr, Logic.cons, Logic.list, Logic.zp, Logic.evenp, Logic.oddp,
                 Logic.integerp, Logic.posp, Logic.natp, Logic.implies, Logic.and,
                 Logic.or, Logic.not, Logic.expt, Logic.le, Logic.ge, Logic.gt,
                 Logic.first, Logic.second, Logic.endp,
                 Logic.append, Logic.len, Logic.trueListp,
                 Logic.iff, Logic.force, Logic.double_rewrite,
                 Logic.evens, Logic.odds])

macro "acl2_grind" : tactic =>
  `(tactic| (acl2_simp; try grind))

/--
`acl2_induct [f [args...]]` applies the induction principle for the function `f`.
If `f` is omitted, it tries to find a recursive function call in the goal.
-/
elab "acl2_induct" f:(ident)? args:term* : tactic => do
  let (fName, fArgs) ← match f with
    | some id => pure (id.getId, args)
    | none => do
      let goal ← getMainGoal
      let target ← goal.getType
      match ← findRecursiveApp target with
      | some (name, eArgs) =>
        let tArgs ← eArgs.mapM fun e => do
          let stx ← Term.exprToSyntax e
          return (TSyntax.mk stx)
        pure (name, tArgs)
      | none => throwError "Could not find a recursive function call to induct on."

  let inductName := fName ++ `induct
  let inductTerm := mkIdent inductName
  let mut targets : Array (TSyntax ``Parser.Tactic.elimTarget) := fArgs.map fun a => ⟨a.raw⟩

  if targets.isEmpty then
     -- No explicit args: use `apply` to let Lean figure out the targets
     evalTactic (← `(tactic| apply $(inductTerm)))
  else
     evalTactic (← `(tactic| induction $[$targets],* using $inductTerm))

end Tactics
end ACL2
