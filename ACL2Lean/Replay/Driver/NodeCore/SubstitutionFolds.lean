import ACL2Lean.Replay.Driver.NodeCore.GroundFold

/-! Replay only the ground folds recorded by ACL2's actual substitution walk.
Each fold is checked at its emitted argument path, then composed to the exact
hypothesis handed to known-whether-nil. This module does no hypothesis relief. -/
namespace ACL2.Replay.Driver
open ACL2 ACL2.Replay Lean Lean.Meta

/-- Convert the observer's zero-based argument indices without searching for a redex. -/
private def substitutionPath (term : SExpr) (indices : List Nat) :
    Except String (List PathFrame) := do
  let mut current := term
  let mut frames := []
  for i in indices do
    let .cons (.atom (.symbol fn)) args := current
      | throw "hypothesis substitution: path crosses a non-symbol application"
    if fn.name == "QUOTE" then throw "hypothesis substitution: path enters quoted data"
    let some args := args.toList? | throw "hypothesis substitution: improper application"
    let some child := args[i]? | throw "hypothesis substitution: path index out of range"
    frames := frames ++ [.arg (i + 1) fn]
    current := child
  return frames

/-- Check a cons-term computation against its captured primitive domain and guard. -/
private def substitutionFoldProof (cfg : ReplayConfig) (fold : SubstitutionFold) : MetaM Expr := do
  let .cons (.atom (.symbol fn)) args := fold.lhs
    | throwError "hypothesis substitution: fold lhs is not an application"
  let some args := args.toList? | throwError "hypothesis substitution: improper fold application"
  unless args.all (fun t => match t with
      | .cons (.atom (.symbol q)) (.cons _ .nil) => q.name == "QUOTE"
      | _ => false) do
    throwError "hypothesis substitution: fold arguments are not all quoted"
  let .cons (.atom (.symbol q)) (.cons value .nil) := fold.rhs
    | throwError "hypothesis substitution: fold result is not quoted"
  unless q.name == "QUOTE" do throwError "hypothesis substitution: fold result is not QUOTE"
  -- cons-term1-body has explicit IF and NOT cases in addition to the
  -- emitted primitive/guard table. IFF is not one of these cases.
  if fn.name == "IF" || fn.name == "NOT" then
    unless args.length == (if fn.name == "IF" then 3 else 1) do
      throwError "hypothesis substitution: IF/NOT fold arity differs"
  else
    let some spec := cfg.consTermGuards.find? (·.fn == fn)
      | throwError "hypothesis substitution: fold head has no emitted cons-term guard"
    unless spec.formals.length == args.length do
      throwError "hypothesis substitution: primitive fold arity differs"
    let (_, guardValue) ← findGroundValue cfg (substTerm spec.formals args spec.guardTerm)
    unless Logic.toBool guardValue do
      throwError "hypothesis substitution: emitted primitive guard is false"
  let _ ← proveNoShadow cfg fn
  let p ← replayExecGround cfg fold.lhs value
  let pq ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr value]
  mkAppM ``fuel_eq_of_conv #[p, pq, ← mkEqRefl (reflectSExpr value)]

/-- Return the equality from the plain instance to the recorded relieved term. -/
def replayHypSubstitution (cfg : ReplayConfig) (basis : HypSubstitutionBasis)
    (target : SExpr) : MetaM (Option Expr) := do
  let mut current := basis.input
  let mut proofs := []
  for fold in basis.folds do
    let frames ← ofExcept (substitutionPath current fold.path)
    let p ← substitutionFoldProof cfg fold
    let (p, next) ← emitCongruenceAlong cfg.worldExpr cfg.envExpr current frames fold.lhs fold.rhs p
    proofs := proofs ++ [p]
    current := next
  unless current == target do
    throwError "hypothesis substitution: recorded folds end at {repr current}, expected {repr target}"
  if proofs.isEmpty then return none
  return some (← chainEqs proofs)

/-- Transport an instantiated USE premise through its recorded closed folds.
The final term is checked exactly even when the recorded fold list is empty. -/
def foldUseInstanceProof (cfg : ReplayConfig) (input target : SExpr)
    (folds : List SubstitutionFold) (proof : Expr) : MetaM Expr := do
  match ← replayHypSubstitution cfg { input, folds } target with
  | none => return proof
  | some eq =>
    mkAppM ``evtrue_of_fuel_eq #[← mkAppM ``fuel_eq_symm #[eq], proof]

/-- The new basis names the plain instance; older markers already name that instance. -/
def hypothesisMarkerInput : ProofNode → SExpr
  | .node _ lhs _ _ prov => (prov.substBasis.map (·.input)).getD lhs

end ACL2.Replay.Driver
