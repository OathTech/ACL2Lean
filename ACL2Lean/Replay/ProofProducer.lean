/-
  Proof-producing checker for ACL2 proof trees (stage 7 — the eventual
  `acl2_replay` tactic).

  ⚠ WIP / NOT WIRED IN / CANNOT REPLAY A REAL TREE YET. Status (2026-06):
  - Orphaned: imported by NOTHING (not in `ACL2Lean.lean`, not in `Main`, not in
    `Tests`); exercised only by in-file `#eval`/`example` tests on synthetic
    ground terms over the empty world. Discharges ZERO real nodes of any
    `.proof-log`.
  - `proveNode` covers only `equal-self` / `if-simplification` /
    `executable-counterpart` and `throwError`s on `definition` / `recognizer` /
    `rewrite` / `rewriting-equivalence` — i.e. the rune types that actually
    dominate real trees (e.g. `simple.proof-log`) are unhandled.
  - Its chain path goes through `evalOpt_replace_congr_fwd` → `evalOpt_ctx_pcEq`
    (T1), which is `sorry` — so any multi-node proof it builds contains `sorryAx`.
  This is the intended real (kernel-checked) path and is SAVABLE, but it is not
  functional today. Do not treat anything it returns as a real proof.

  Walks the parsed proof tree and constructs Lean proof terms (Expr) for each
  node. Architecture: reflection (SExpr → Expr); side-condition provers (decide /
  simp); per-rune node provers (apply the corresponding EvalLemma); composition
  via T1 (congruence) + T16 (chain).
-/
import ACL2Lean.Replay.EvalLemmas
import ACL2Lean.ProofTree
import Lean

namespace ACL2.Replay.ProofProducer

open ACL2 ACL2.Replay Lean Elab Meta

/-! ## Context -/

/-- Context for proof production. -/
structure ProofCtx where
  /-- Lean Expr for the World being used. -/
  worldExpr : Expr
  /-- The actual World value (for meta-time lookups). -/
  world : World
  /-- Lean Expr for the environment (variable bindings). -/
  envExpr : Expr
  /-- Names to unfold when using simp (world definition name, etc.). -/
  worldUnfoldNames : Array Name := #[]

/-! ## Reflection: SExpr → Lean Expr -/

/-- Reflect an Int as a Lean Expr of type Int. -/
def reflectInt : Int → Expr
  | .ofNat n => mkApp (Lean.mkConst ``Int.ofNat) (mkNatLit n)
  | .negSucc n => mkApp (Lean.mkConst ``Int.negSucc) (mkNatLit n)

/-- Reflect an ACL2 Symbol as a Lean Expr of type Symbol. -/
def reflectSymbol (s : Symbol) : Expr :=
  mkApp2 (Lean.mkConst ``Symbol.mk) (mkStrLit s.package) (mkStrLit s.name)

/-- Reflect an ACL2 Number as a Lean Expr of type Number. -/
def reflectNumber : Number → Expr
  | .int v => mkApp (Lean.mkConst ``Number.int) (reflectInt v)
  | .rational num den =>
    mkApp2 (Lean.mkConst ``Number.rational) (reflectInt num) (mkNatLit den)
  | .decimal m e =>
    mkApp2 (Lean.mkConst ``Number.decimal) (reflectInt m) (reflectInt e)

/-- Reflect an ACL2 Atom as a Lean Expr of type Atom. -/
def reflectAtom : Atom → Expr
  | .symbol s => mkApp (Lean.mkConst ``Atom.symbol) (reflectSymbol s)
  | .keyword k => mkApp (Lean.mkConst ``Atom.keyword) (mkStrLit k)
  | .string s => mkApp (Lean.mkConst ``Atom.string) (mkStrLit s)
  | .number n => mkApp (Lean.mkConst ``Atom.number) (reflectNumber n)

/-- Reflect an ACL2 SExpr as a Lean Expr of type SExpr. -/
def reflectSExpr : SExpr → Expr
  | .nil => Lean.mkConst ``SExpr.nil
  | .atom a => mkApp (Lean.mkConst ``SExpr.atom) (reflectAtom a)
  | .cons car cdr =>
    mkApp2 (Lean.mkConst ``SExpr.cons) (reflectSExpr car) (reflectSExpr cdr)

/-- Construct the Expr for an empty Env (`{} : Env`). -/
def mkEmptyEnv : TermElabM Expr := do
  Term.elabTerm (← `(({} : Env))) none

/-! ## Side condition provers -/

/-- Prove a proposition using simp with the default simp set plus
    optional definition unfolding. -/
def proveBySimp (goalType : Expr) (unfoldNames : Array Name := #[])
    (extraLemmas : Array Name := #[]) : MetaM Expr := do
  let defaultCtx ← Simp.Context.mkDefault
  let mut simpThms := defaultCtx.simpTheorems[0]!
  for n in unfoldNames do
    simpThms ← simpThms.addDeclToUnfold n
  for n in extraLemmas do
    simpThms ← simpThms.addConst n
  let ctx ← Simp.mkContext (simpTheorems := #[simpThms])
  let (result, _) ← Meta.simp goalType ctx
  match result.proof? with
  | some proof =>
    if result.expr == Lean.mkConst ``True then
      mkAppM ``of_eq_true #[proof]
    else
      throwError "proveBySimp: simp reduced to {result.expr}, not True"
  | none =>
    -- No proof needed: already True definitionally
    mkAppM ``of_eq_true #[← mkEqRefl (Lean.mkConst ``True)]

/-- Prove a decidable proposition by kernel reduction. -/
def proveByDecide (p : Expr) : MetaM Expr := do
  let inst ← synthInstance (mkApp (Lean.mkConst ``Decidable) p)
  let decideApp := mkApp2 (Lean.mkConst ``decide) p inst
  let reduced ← withTransparency .all <| whnf decideApp
  unless reduced == Lean.mkConst ``Bool.true do
    throwError "proveByDecide: does not decide to true:\n  {← ppExpr p}"
  let rflTrue := mkApp2 (Lean.mkConst ``Eq.refl [1])
    (Lean.mkConst ``Bool) (Lean.mkConst ``Bool.true)
  return mkApp3 (Lean.mkConst ``of_decide_eq_true) p inst rflTrue

/-! ## Proof builders for side conditions -/

/-- Prove `s.isNamed "quote" = false ∧ s.isNamed "if" = false ∧
    s.isNamed "let" = false ∧ s.isNamed "let*" = false`. -/
def proveNotSpecial (s : Symbol) : MetaM Expr := do
  let sExpr := reflectSymbol s
  let boolType := Lean.mkConst ``Bool
  let falseExpr := Lean.mkConst ``Bool.false
  let mkEqFalse (name : String) : Expr :=
    mkApp3 (Lean.mkConst ``Eq [1]) boolType
      (mkApp2 (Lean.mkConst ``Symbol.isNamed) sExpr (mkStrLit name)) falseExpr
  let mkAnd (a b : Expr) : Expr := mkApp2 (Lean.mkConst ``And) a b
  proveByDecide (mkAnd (mkEqFalse "quote")
    (mkAnd (mkEqFalse "if") (mkAnd (mkEqFalse "let") (mkEqFalse "let*"))))

/-- Prove `w.defs.get? s = none` (builtin not shadowed). -/
def proveWorldLookupNone (ctx : ProofCtx) (s : Symbol) : MetaM Expr := do
  let worldDefs := mkApp (Lean.mkConst ``World.defs) ctx.worldExpr
  let lookupExpr ← mkAppM ``Std.HashMap.get? #[worldDefs, reflectSymbol s]
  let lookupType ← inferType lookupExpr
  let noneExpr := mkApp (Lean.mkConst ``Option.none [0]) lookupType.appArg!
  proveBySimp (mkApp3 (Lean.mkConst ``Eq [1]) lookupType lookupExpr noneExpr)
    (unfoldNames := ctx.worldUnfoldNames)

/-- Prove a ground evaluation: `evalOpt fuel w env term = some value`. -/
def proveGroundEval (ctx : ProofCtx) (fuel : Nat) (term value : SExpr) :
    MetaM Expr := do
  let optSExpr := mkApp (Lean.mkConst ``Option [0]) (Lean.mkConst ``SExpr)
  let evalExpr := mkAppN (Lean.mkConst ``evalOpt)
    #[mkNatLit fuel, ctx.worldExpr, ctx.envExpr, reflectSExpr term]
  let someValue := mkApp2 (Lean.mkConst ``Option.some [0])
    (Lean.mkConst ``SExpr) (reflectSExpr value)
  proveBySimp (mkApp3 (Lean.mkConst ``Eq [1]) optSExpr evalExpr someValue)
    (unfoldNames := ctx.worldUnfoldNames ++ #[``evalOpt, ``evalOptStep])

/-! ## Node provers -/

/-- Prove: `evalOpt (f+1) w env (QUOTE v) = some v`
    Uses `evalOpt_quote`. -/
def proveQuoteEval (ctx : ProofCtx) (f : Nat) (v : SExpr) : MetaM Expr :=
  return mkAppN (Lean.mkConst ``evalOpt_quote)
    #[mkNatLit f, ctx.worldExpr, ctx.envExpr, reflectSExpr v]

/-- Prove: `evalOpt (f+1) w env (.atom (.number n)) = some (.atom (.number n))`
    Uses `evalOpt_number`. -/
def proveNumberEval (ctx : ProofCtx) (f : Nat) (n : Number) : MetaM Expr :=
  return mkAppN (Lean.mkConst ``evalOpt_number)
    #[mkNatLit f, ctx.worldExpr, ctx.envExpr, reflectNumber n]

/-- Prove: `evalOpt (f+1) w env .nil = some .nil`
    Uses `evalOpt_nil`. -/
def proveNilEval (ctx : ProofCtx) (f : Nat) : MetaM Expr :=
  return mkAppN (Lean.mkConst ``evalOpt_nil)
    #[mkNatLit f, ctx.worldExpr, ctx.envExpr]

/-- Prove: `evalOpt (f+1) w env (EQUAL t t) = some T`
    Uses `evalOpt_equal_self`. Requires convergence proof for `t`. -/
def proveEqualSelf (ctx : ProofCtx) (f : Nat)
    (t v : SExpr) (hConverge : Expr) : MetaM Expr := do
  let hNoDef ← proveWorldLookupNone ctx { name := "equal" }
  return mkAppN (Lean.mkConst ``evalOpt_equal_self)
    #[mkNatLit f, ctx.worldExpr, ctx.envExpr,
      reflectSExpr t, reflectSExpr v, hConverge, hNoDef]

/-- Prove: `evalOpt (f+1) w env (IF c t e) = evalOpt f w env e`
    when the test `c` evaluates to nil.
    Uses `evalOpt_if_false`. -/
def proveIfFalse (ctx : ProofCtx) (f : Nat)
    (c t e : SExpr) (hTestNil : Expr) : MetaM Expr :=
  return mkAppN (Lean.mkConst ``evalOpt_if_false)
    #[mkNatLit f, ctx.worldExpr, ctx.envExpr,
      reflectSExpr c, reflectSExpr t, reflectSExpr e, hTestNil]

/-- Prove: `evalOpt (f+1) w env (IF c t e) = evalOpt f w env t`
    when the test `c` evaluates to a truthy value `cv`.
    Uses `evalOpt_if_true`. -/
def proveIfTrue (ctx : ProofCtx) (f : Nat)
    (c t e cv : SExpr) (hTestConv : Expr) (hTruthy : Expr) : MetaM Expr :=
  return mkAppN (Lean.mkConst ``evalOpt_if_true)
    #[mkNatLit f, ctx.worldExpr, ctx.envExpr,
      reflectSExpr c, reflectSExpr t, reflectSExpr e,
      reflectSExpr cv, hTestConv, hTruthy]

/-- Prove: `evalOpt (f+1) w env (S arg) = some (callBuiltin s.name [av])`
    for a 1-arg builtin function.
    Uses `evalOpt_builtin_1`. -/
def proveBuiltin1 (ctx : ProofCtx) (f : Nat)
    (s : Symbol) (arg av : SExpr) (hArgEval : Expr) : MetaM Expr := do
  let hNotSpecial ← proveNotSpecial s
  let hNoDef ← proveWorldLookupNone ctx s
  return mkAppN (Lean.mkConst ``evalOpt_builtin_1)
    #[mkNatLit f, ctx.worldExpr, ctx.envExpr,
      reflectSymbol s, reflectSExpr arg, reflectSExpr av,
      hNotSpecial, hNoDef, hArgEval]

/-- Prove: `evalOpt (f+1) w env (S arg1 arg2) = some (callBuiltin s.name [av1, av2])`
    for a 2-arg builtin function.
    Uses `evalOpt_builtin_2`. -/
def proveBuiltin2 (ctx : ProofCtx) (f : Nat)
    (s : Symbol) (arg1 arg2 av1 av2 : SExpr)
    (hArg1 hArg2 : Expr) : MetaM Expr := do
  let hNotSpecial ← proveNotSpecial s
  let hNoDef ← proveWorldLookupNone ctx s
  return mkAppN (Lean.mkConst ``evalOpt_builtin_2)
    #[mkNatLit f, ctx.worldExpr, ctx.envExpr,
      reflectSymbol s, reflectSExpr arg1, reflectSExpr arg2,
      reflectSExpr av1, reflectSExpr av2,
      hNotSpecial, hNoDef, hArg1, hArg2]

/-- Prove: `evalOpt (f+1) w env (S arg) = evalOpt f w (bindArgs [formal] [av]) body`
    for a 1-arg user-defined function.
    Uses `evalOpt_defn_1`. -/
def proveDefn1 (ctx : ProofCtx) (f : Nat)
    (s : Symbol) (arg av : SExpr) (formal : Symbol) (body : SExpr)
    (hArgEval : Expr) (hDef : Expr) : MetaM Expr := do
  let hNotSpecial ← proveNotSpecial s
  return mkAppN (Lean.mkConst ``evalOpt_defn_1)
    #[mkNatLit f, ctx.worldExpr, ctx.envExpr,
      reflectSymbol s, reflectSExpr arg, reflectSExpr av,
      reflectSymbol formal, reflectSExpr body,
      hNotSpecial, hDef, hArgEval]

/-- Prove: `evalOpt (f+1) w env (S a1 a2) = evalOpt f w (bindArgs [f1,f2] [v1,v2]) body`
    for a 2-arg user-defined function.
    Uses `evalOpt_defn_2`. -/
def proveDefn2 (ctx : ProofCtx) (f : Nat)
    (s : Symbol) (arg1 arg2 av1 av2 : SExpr)
    (formal1 formal2 : Symbol) (body : SExpr)
    (hArg1 hArg2 : Expr) (hDef : Expr) : MetaM Expr := do
  let hNotSpecial ← proveNotSpecial s
  return mkAppN (Lean.mkConst ``evalOpt_defn_2)
    #[mkNatLit f, ctx.worldExpr, ctx.envExpr,
      reflectSymbol s, reflectSExpr arg1, reflectSExpr arg2,
      reflectSExpr av1, reflectSExpr av2,
      reflectSymbol formal1, reflectSymbol formal2, reflectSExpr body,
      hNotSpecial, hDef, hArg1, hArg2]

/-- Prove: `evalOpt (f+1) w env (.atom (.symbol s)) = some v`
    for a bound variable.
    Uses `evalOpt_var`. -/
def proveVar (ctx : ProofCtx) (f : Nat)
    (s : Symbol) (v : SExpr) (hLookup : Expr) : MetaM Expr :=
  return mkAppN (Lean.mkConst ``evalOpt_var)
    #[mkNatLit f, ctx.worldExpr, ctx.envExpr,
      reflectSymbol s, reflectSExpr v, hLookup]

/-! ## Fuel management -/

/-- Build the predicate `fun N => ∀ f ≥ N, evalOpt f w env a = rhs`
    where `rhs` is an Expr (either `evalOpt f w env b` or `some v`). -/
private def mkFuelPred (ctx : ProofCtx) (aExpr : Expr)
    (mkRhs : Expr → Expr) : MetaM Expr := do
  withLocalDeclD `N (Lean.mkConst ``Nat) fun nVar => do
    withLocalDeclD `f (Lean.mkConst ``Nat) fun fVar => do
      let geType ← mkAppM ``GE.ge #[fVar, nVar]
      withLocalDeclD `hf geType fun hfVar => do
        let lhsEval := mkAppN (Lean.mkConst ``evalOpt) #[fVar, ctx.worldExpr, ctx.envExpr, aExpr]
        let eqType ← mkAppM ``Eq #[lhsEval, mkRhs fVar]
        let forall_ ← mkForallFVars #[fVar, hfVar] eqType
        mkLambdaFVars #[nVar] forall_

/-- Wrap concrete-fuel proofs into existential form.
    Given `hA : evalOpt N w env a = some v` and `hB : evalOpt N w env b = some v`,
    produce `∃ M, ∀ f ≥ M, evalOpt f w env a = evalOpt f w env b`.
    Uses `evalOpt_ge_fuel` to lift from fuel N to arbitrary fuel ≥ N. -/
def mkFuelEqExist (ctx : ProofCtx) (N : Nat)
    (a b v : SExpr) (hA hB : Expr) : MetaM Expr := do
  let NE := mkNatLit N
  let aE := reflectSExpr a
  let bE := reflectSExpr b
  -- Build predicate: fun N => ∀ f ≥ N, eval f w env a = eval f w env b
  let pred ← mkFuelPred ctx aE fun fVar =>
    mkAppN (Lean.mkConst ``evalOpt) #[fVar, ctx.worldExpr, ctx.envExpr, bE]
  -- Build proof body: fun f hf => geA.trans geB.symm
  withLocalDeclD `f (Lean.mkConst ``Nat) fun fVar => do
    let geType ← mkAppM ``GE.ge #[fVar, NE]
    withLocalDeclD `hf geType fun hfVar => do
      let geA := mkAppN (Lean.mkConst ``evalOpt_ge_fuel)
        #[NE, fVar, ctx.worldExpr, ctx.envExpr,
          aE, reflectSExpr v, hA, hfVar]
      let geB := mkAppN (Lean.mkConst ``evalOpt_ge_fuel)
        #[NE, fVar, ctx.worldExpr, ctx.envExpr,
          bE, reflectSExpr v, hB, hfVar]
      let eqProof ← mkAppM ``Eq.trans #[geA, ← mkAppM ``Eq.symm #[geB]]
      let body ← mkLambdaFVars #[fVar, hfVar] eqProof
      return mkApp4 (Lean.mkConst ``Exists.intro [1])
        (Lean.mkConst ``Nat) pred NE body

/-- Wrap a convergence proof into existential "= some v" form.
    Given `hA : evalOpt N w env a = some v`,
    produce `∃ M, ∀ f ≥ M, evalOpt f w env a = some v`. -/
def mkFuelConvergeExist (ctx : ProofCtx) (N : Nat)
    (a : SExpr) (v : SExpr) (hA : Expr) : MetaM Expr := do
  let NE := mkNatLit N
  let aE := reflectSExpr a
  let vE := reflectSExpr v
  let someV := mkApp2 (Lean.mkConst ``Option.some [0]) (Lean.mkConst ``SExpr) vE
  -- Build predicate: fun N => ∀ f ≥ N, eval f w env a = some v
  let pred ← mkFuelPred ctx aE fun _ => someV
  -- Build proof body
  withLocalDeclD `f (Lean.mkConst ``Nat) fun fVar => do
    let geType ← mkAppM ``GE.ge #[fVar, NE]
    withLocalDeclD `hf geType fun hfVar => do
      let geA := mkAppN (Lean.mkConst ``evalOpt_ge_fuel)
        #[NE, fVar, ctx.worldExpr, ctx.envExpr,
          aE, vE, hA, hfVar]
      let body ← mkLambdaFVars #[fVar, hfVar] geA
      return mkApp4 (Lean.mkConst ``Exists.intro [1])
        (Lean.mkConst ``Nat) pred NE body

/-! ## Proof tree walking -/

/-- Evaluate an SExpr at meta-time using the world's evaluator.
    Returns the value if the term converges at the given fuel. -/
def metaEval (w : World) (env : Env) (fuel : Nat) (term : SExpr) :
    Option SExpr :=
  evalOpt fuel w env term

/-- Prove a single proof node. Returns an existential fuel proof:
    `∃ N, ∀ f ≥ N, evalOpt f w env node.lhs = evalOpt f w env node.rhs`
    Dispatches on the rune type, mirroring the Bool checker. -/
partial def proveNode (ctx : ProofCtx) (node : ProofNode) : MetaM Expr :=
  match node with
  | .node (runeType, _runeName) lhs rhs _children _prov =>
    match runeType with
    | "equal-self" => proveEqualSelfNode ctx lhs rhs
    | "if-simplification" => proveIfSimplNode ctx lhs rhs
    | "executable-counterpart" => proveExecCounterpart ctx lhs rhs
    | other => throwError "proveNode: unsupported rune type '{other}'"
where
  /-- Find the minimum fuel at which a ground term converges. -/
  findFuel (w : World) (term : SExpr) (maxFuel : Nat := 20) : Option Nat := do
    for f in List.range (maxFuel + 1) do
      if (evalOpt f w {} term).isSome then return f
    none

  /-- equal-self: (EQUAL X X) → (QUOTE T) -/
  proveEqualSelfNode (ctx : ProofCtx) (lhs rhs : SExpr) : MetaM Expr := do
    -- Decompose LHS as (EQUAL X X)
    let x := match lhs with
      | .cons _ (.cons x (.cons _ .nil)) => x
      | _ => panic! "equal-self: LHS is not (EQUAL X X)"
    -- Find minimum fuel for X to converge
    let some fuel := findFuel ctx.world x
      | throwError "equal-self: subterm does not converge"
    let some xVal := metaEval ctx.world {} fuel x
      | throwError "equal-self: unreachable"
    -- hConv: evalOpt fuel w env X = some xVal
    let hConv ← proveGroundEval ctx fuel x xVal
    -- hA: evalOpt (fuel+1) w env (EQUAL X X) = some T
    let hA ← proveEqualSelf ctx fuel x xVal hConv
    -- hB: evalOpt (fuel+1) w env (QUOTE T) = some T (rhs is QUOTE T)
    let hB ← proveQuoteEval ctx fuel SExpr.t
    -- Wrap into existential
    mkFuelEqExist ctx (fuel + 1) lhs rhs SExpr.t hA hB

  /-- if-simplification: (IF (QUOTE NIL) A B) → B or (IF (QUOTE T) A B) → A -/
  proveIfSimplNode (ctx : ProofCtx) (lhs rhs : SExpr) : MetaM Expr := do
    let (c, t, e) := match lhs with
      | .cons _ (.cons c (.cons t (.cons e .nil))) => (c, t, e)
      | _ => panic! "if-simplification: LHS is not (IF c t e)"
    let some fuel := findFuel ctx.world c
      | throwError "if-simplification: test does not converge"
    let some cVal := metaEval ctx.world {} fuel c
      | throwError "if-simplification: unreachable"
    let hTestEval ← proveGroundEval ctx fuel c cVal
    if cVal == SExpr.nil then
      let hIfFalse ← proveIfFalse ctx fuel c t e hTestEval
      if e == rhs then
        let some eVal := metaEval ctx.world {} fuel e
          | throwError "if-simplification: else branch does not converge"
        let hElse ← proveGroundEval ctx fuel e eVal
        let hA ← mkAppM ``Eq.trans #[hIfFalse, hElse]
        let hB ← proveGroundEval ctx (fuel + 1) rhs eVal
        mkFuelEqExist ctx (fuel + 1) lhs rhs eVal hA hB
      else
        throwError "if-simplification: else branch {e} ≠ rhs {rhs}"
    else
      throwError "if-simplification: truthy test not yet supported"

  /-- executable-counterpart: ground eval -/
  proveExecCounterpart (ctx : ProofCtx) (lhs rhs : SExpr) : MetaM Expr := do
    let some fuelL := findFuel ctx.world lhs
      | throwError "executable-counterpart: LHS does not converge"
    let some fuelR := findFuel ctx.world rhs
      | throwError "executable-counterpart: RHS does not converge"
    let fuel := max fuelL fuelR
    let some lhsVal := metaEval ctx.world {} fuel lhs
      | throwError "executable-counterpart: unreachable"
    let some rhsVal := metaEval ctx.world {} fuel rhs
      | throwError "executable-counterpart: unreachable"
    unless lhsVal == rhsVal do
      throwError "executable-counterpart: LHS evaluates to {repr lhsVal} but RHS to {repr rhsVal}"
    let hA ← proveGroundEval ctx fuel lhs lhsVal
    let hB ← proveGroundEval ctx fuel rhs rhsVal
    mkFuelEqExist ctx fuel lhs rhs lhsVal hA hB

/-- Compose a chain of node proofs for a literal.
    Given nodes `[n1, n2, ..., nk]` and the literal term,
    produces `∃ N, ∀ f ≥ N, evalOpt f w env literal = some T`.

    Each node proves `eval lhs_i = eval rhs_i`. T1 (congruence) lifts
    this to the enclosing term, and T16 (chain) composes successive steps. -/
def proveLiteralChain (ctx : ProofCtx) (literal : SExpr)
    (nodes : List ProofNode) : MetaM Expr := do
  -- Process each node to get its proof
  let mut currentTerm := literal
  let mut chainProof : Option Expr := none

  for node in nodes do
    match node with
    | .node _ nodeLhs nodeRhs _ _ =>
      -- Prove this node: ∃ N, ∀ f ≥ N, eval nodeLhs = eval nodeRhs
      let nodeProof ← proveNode ctx node
      -- Lift to enclosing term via T1 (congruence):
      -- ∃ N, ∀ f ≥ N, eval currentTerm = eval (replace currentTerm nodeLhs nodeRhs)
      let stepProof ← mkAppM ``evalOpt_replace_congr_fwd
        #[ctx.worldExpr, ctx.envExpr,
          reflectSExpr currentTerm, reflectSExpr nodeLhs,
          reflectSExpr nodeRhs, nodeProof]
      -- Chain with previous steps via T16
      match chainProof with
      | none => chainProof := some stepProof
      | some prev =>
        chainProof := some (← mkAppM ``fuel_chain_eq #[prev, stepProof])
      -- Update current term
      currentTerm := replaceSubterm currentTerm nodeLhs nodeRhs

  -- After all nodes, currentTerm should be (QUOTE T) or similar.
  -- The chain proof gives: ∃ N, ∀ f ≥ N, eval literal = eval currentTerm
  -- We need: ∃ N, ∀ f ≥ N, eval literal = some T
  -- Prove: ∃ N, ∀ f ≥ N, eval currentTerm = some T
  let hFinalExist ← proveTermConverges ctx currentTerm

  -- Chain: eval literal = eval currentTerm = some T
  match chainProof with
  | none => return hFinalExist  -- no nodes, literal is already the final term
  | some chain => mkAppM ``fuel_chain_eq #[chain, hFinalExist]
where
  /-- Prove ∃ N, ∀ f ≥ N, evalOpt f w env term = some value
      by dispatching on the term structure and using structured lemmas. -/
  proveTermConverges (ctx : ProofCtx) (term : SExpr) : MetaM Expr := do
    match term with
    | .nil =>
      let h ← proveNilEval ctx 0
      mkFuelConvergeExist ctx 1 term .nil h
    | .atom (.number n) =>
      let h ← proveNumberEval ctx 0 n
      mkFuelConvergeExist ctx 1 term (.atom (.number n)) h
    | .cons (.atom (.symbol q)) (.cons v .nil) =>
      if q.isNamed "quote" then
        let h ← proveQuoteEval ctx 0 v
        mkFuelConvergeExist ctx 1 term v h
      else
        throwError "proveLiteralChain: final term is not a simple value: {repr term}"
    | _ =>
      throwError "proveLiteralChain: final term is not a simple value: {repr term}"

-- ============================================================
-- Validation: term-mode proofs using our lemmas directly.
-- These demonstrate what the proof-producing checker emits.
-- ============================================================

-- Test 1: equal-self on ground terms
-- The checker would emit exactly this term.
example : evalOpt 2 World.empty {}
    (.cons (.atom (.symbol { name := "equal" }))
      (.cons (.atom (.number (.int 1)))
        (.cons (.atom (.number (.int 1))) .nil)))
    = some SExpr.t :=
  evalOpt_equal_self 1 World.empty {}
    (.atom (.number (.int 1)))
    (.atom (.number (.int 1)))
    (by simp [evalOpt, evalOptStep])
    (by show World.empty.defs[({ name := "equal" } : Symbol)]? = none; simp [World.empty])

-- Test 2: IF with nil test takes else branch
-- Simpler than consp — just IF with a constant test.
example : evalOpt 2 World.empty {}
    (.cons (.atom (.symbol { name := "if" }))
      (.cons .nil
        (.cons (.atom (.number (.int 42)))
          (.cons (.atom (.number (.int 0))) .nil))))
    = some (.atom (.number (.int 0))) :=
  evalOpt_if_false 1 World.empty {}
    .nil (.atom (.number (.int 42))) (.atom (.number (.int 0)))
    (by simp [evalOpt, evalOptStep])

-- Test 3: definition expansion of a 1-arg function
-- World with identity function: (defun id (x) x)
private def idWorld : World where
  defs := ({} : Std.HashMap Symbol (List Symbol × SExpr))
    |>.insert { name := "id" } ([{ name := "x" }], .atom (.symbol { name := "x" }))

-- eval(id 42) = eval(42) = some 42
example : evalOpt 3 idWorld {}
    (.cons (.atom (.symbol { name := "id" }))
      (.cons (.atom (.number (.int 42))) .nil))
    = some (.atom (.number (.int 42))) :=
  evalOpt_defn_1 2 idWorld {}
    { name := "id" }
    (.atom (.number (.int 42)))
    (.atom (.number (.int 42)))
    { name := "x" }
    (.atom (.symbol { name := "x" }))
    (by decide) -- not special
    (by show idWorld.defs[({ name := "id" } : Symbol)]? = _
        simp [idWorld])
    (by simp [evalOpt, evalOptStep]) -- arg 42 evals to 42
  |>.trans (by -- body x in {x→42} evals to 42
    simp [evalOpt, evalOptStep, bindArgs])

-- Test 4: Chaining two steps — definition expansion followed by equal-self.
-- World: (defun id (x) x)
-- Theorem: (EQUAL (id 42) 42) = T
example : evalOpt 4 idWorld {}
    (.cons (.atom (.symbol { name := "equal" }))
      (.cons (.cons (.atom (.symbol { name := "id" }))
              (.cons (.atom (.number (.int 42))) .nil))
        (.cons (.atom (.number (.int 42))) .nil)))
    = some SExpr.t := by
  rw [evalOpt_builtin_2 3 idWorld {} { name := "equal" }
      (.cons (.atom (.symbol { name := "id" })) (.cons (.atom (.number (.int 42))) .nil))
      (.atom (.number (.int 42)))
      (.atom (.number (.int 42)))  -- v_lhs: id 42 evaluates to 42
      (.atom (.number (.int 42)))  -- v_rhs: 42 evaluates to 42
      (by decide)  -- "equal" not special
      (by show idWorld.defs[({ name := "equal" } : Symbol)]? = none; simp [idWorld])
      -- LHS arg: (id 42) evaluates to 42
      (by rw [evalOpt_defn_1 2 idWorld {} { name := "id" }
              (.atom (.number (.int 42))) (.atom (.number (.int 42)))
              { name := "x" } (.atom (.symbol { name := "x" }))
              (by decide)
              (by show idWorld.defs[({ name := "id" } : Symbol)]? = _; simp [idWorld])
              (by simp [evalOpt, evalOptStep])]
          simp [evalOpt, evalOptStep, bindArgs])
      -- RHS arg: 42 evaluates to 42
      (by simp [evalOpt, evalOptStep])]
  -- Now goal: some (callBuiltin "equal" [42, 42]) = some T
  simp [callBuiltin_equal]

-- Test 5: Definition expansion with IF resolution.
-- World with: (defun f (x) (if (consp x) (quote 1) (quote 0)))
-- Prove: eval(f NIL) = some 0  (consp nil = nil → else branch → 0)
-- This chains: defn expand → IF-false → quote.
private def testWorld5 : World where
  defs := ({} : Std.HashMap Symbol (List Symbol × SExpr))
    |>.insert { name := "f" } ([{ name := "x" }],
      .cons (.atom (.symbol { name := "if" }))
        (.cons (.cons (.atom (.symbol { name := "consp" }))
                (.cons (.atom (.symbol { name := "x" })) .nil))
          (.cons (.cons (.atom (.symbol { name := "quote" }))
                  (.cons (.atom (.number (.int 1))) .nil))
            (.cons (.cons (.atom (.symbol { name := "quote" }))
                    (.cons (.atom (.number (.int 0))) .nil))
              .nil))))

-- The body term, written out explicitly
private def testBody5 : SExpr :=
  .cons (.atom (.symbol { name := "if" }))
    (.cons (.cons (.atom (.symbol { name := "consp" }))
            (.cons (.atom (.symbol { name := "x" })) .nil))
      (.cons (.cons (.atom (.symbol { name := "quote" }))
              (.cons (.atom (.number (.int 1))) .nil))
        (.cons (.cons (.atom (.symbol { name := "quote" }))
                (.cons (.atom (.number (.int 0))) .nil))
          .nil)))

example : evalOpt 5 testWorld5 {}
    (.cons (.atom (.symbol { name := "f" }))
      (.cons .nil .nil))
    = some (.atom (.number (.int 0))) := by
  -- Step 1: T4 (defn expand): eval(f nil) = eval(body) in {x→nil}
  have h_defn : testWorld5.defs.get? { name := "f" } = some ([{ name := "x" }], testBody5) := by
    show testWorld5.defs[({ name := "f" } : Symbol)]? = _; simp [testWorld5, testBody5]
  rw [evalOpt_defn_1 4 testWorld5 {} { name := "f" }
      .nil .nil { name := "x" } testBody5
      (by decide) h_defn
      (by simp [evalOpt, evalOptStep])]
  -- Goal: evalOpt 4 testWorld5 (bindArgs [x] [nil]) testBody5 = some 0
  -- Body is (IF (CONSP x) (QUOTE 1) (QUOTE 0)) in env {x→nil}
  -- Step 2: T5 (if-false) — consp nil = nil, take else branch
  -- But to apply T5, we need to unfold testBody5 first
  unfold testBody5
  -- Now apply T5 with consp nil = nil as the test
  rw [evalOpt_if_false 3 testWorld5 (bindArgs [{ name := "x" }] [.nil])
      (.cons (.atom (.symbol { name := "consp" })) (.cons (.atom (.symbol { name := "x" })) .nil))
      (.cons (.atom (.symbol { name := "quote" })) (.cons (.atom (.number (.int 1))) .nil))
      (.cons (.atom (.symbol { name := "quote" })) (.cons (.atom (.number (.int 0))) .nil))
      (by -- eval consp(x) in {x→nil} = some nil
          rw [evalOpt_builtin_1 2 testWorld5 _ { name := "consp" }
              (.atom (.symbol { name := "x" })) .nil
              (by decide)
              (by show testWorld5.defs[({ name := "consp" } : Symbol)]? = none
                  simp [testWorld5])
              (evalOpt_var 1 testWorld5 _ { name := "x" } .nil
                (by show (bindArgs [{ name := "x" }] [.nil]).get? { name := "x" } = some .nil
                    simp [bindArgs]))]
          simp [callBuiltin_consp, Logic.consp])]
  -- Goal: evalOpt 3 testWorld5 {x→nil} (QUOTE 0) = some 0
  exact evalOpt_quote 2 testWorld5 _ (.atom (.number (.int 0)))

-- ============================================================
-- MetaM proof construction tests.
-- These verify the proof producers emit correct proof terms.
-- ============================================================

section MetaMTests

-- Test: MetaM construction of equal-self proof
-- Proves: evalOpt 2 World.empty {} (EQUAL 1 1) = some T
elab "#test_prove_equal_self" : command => do
  Elab.Command.liftTermElabM do
    let emptyEnv ← mkEmptyEnv
    let ctx : ProofCtx := {
      worldExpr := Lean.mkConst ``World.empty
      world := World.empty
      envExpr := emptyEnv
      worldUnfoldNames := #[``World.empty]
    }
    let one : SExpr := .atom (.number (.int 1))
    let hConverge ← proveGroundEval ctx 1 one one
    let proof ← proveEqualSelf ctx 1 one one hConverge
    let _ ← check proof
    logInfo m!"equal-self proof OK: {← inferType proof}"

#test_prove_equal_self

-- Test: MetaM construction of quote eval proof
elab "#test_prove_quote" : command => do
  Elab.Command.liftTermElabM do
    let emptyEnv ← mkEmptyEnv
    let ctx : ProofCtx := {
      worldExpr := Lean.mkConst ``World.empty
      world := World.empty
      envExpr := emptyEnv
      worldUnfoldNames := #[``World.empty]
    }
    let proof ← proveQuoteEval ctx 1 SExpr.t
    let _ ← check proof
    logInfo m!"quote proof OK: {← inferType proof}"

#test_prove_quote

-- Test: MetaM construction of number eval proof
elab "#test_prove_number" : command => do
  Elab.Command.liftTermElabM do
    let emptyEnv ← mkEmptyEnv
    let ctx : ProofCtx := {
      worldExpr := Lean.mkConst ``World.empty
      world := World.empty
      envExpr := emptyEnv
      worldUnfoldNames := #[``World.empty]
    }
    let proof ← proveNumberEval ctx 1 (.int 42)
    let _ ← check proof
    logInfo m!"number proof OK: {← inferType proof}"

#test_prove_number

-- Test: MetaM construction of if-false proof
elab "#test_prove_if_false" : command => do
  Elab.Command.liftTermElabM do
    let emptyEnv ← mkEmptyEnv
    let ctx : ProofCtx := {
      worldExpr := Lean.mkConst ``World.empty
      world := World.empty
      envExpr := emptyEnv
      worldUnfoldNames := #[``World.empty]
    }
    -- Prove: evalOpt 1 World.empty {} .nil = some .nil (test evals to nil)
    let hTestNil ← proveGroundEval ctx 1 .nil .nil
    let proof ← proveIfFalse ctx 1 .nil
      (.atom (.number (.int 42))) (.atom (.number (.int 0))) hTestNil
    let _ ← check proof
    logInfo m!"if-false proof OK: {← inferType proof}"

#test_prove_if_false

-- Test: MetaM construction of builtin-1 proof
elab "#test_prove_builtin1" : command => do
  Elab.Command.liftTermElabM do
    let emptyEnv ← mkEmptyEnv
    let ctx : ProofCtx := {
      worldExpr := Lean.mkConst ``World.empty
      world := World.empty
      envExpr := emptyEnv
      worldUnfoldNames := #[``World.empty]
    }
    let arg : SExpr := .atom (.number (.int 42))
    let hArgEval ← proveGroundEval ctx 1 arg arg
    let proof ← proveBuiltin1 ctx 1 { name := "consp" } arg arg hArgEval
    let _ ← check proof
    logInfo m!"builtin-1 proof OK: {← inferType proof}"

#test_prove_builtin1

-- Test: proveNode dispatch for equal-self
-- Proof tree node: (EQUAL 1 1) → (QUOTE T)
elab "#test_prove_node_equal_self" : command => do
  Elab.Command.liftTermElabM do
    let emptyEnv ← mkEmptyEnv
    let ctx : ProofCtx := {
      worldExpr := Lean.mkConst ``World.empty
      world := World.empty
      envExpr := emptyEnv
      worldUnfoldNames := #[``World.empty]
    }
    let one : SExpr := .atom (.number (.int 1))
    let equal_1_1 : SExpr := .cons (.atom (.symbol { name := "equal" }))
      (.cons one (.cons one .nil))
    let quote_t : SExpr := .cons (.atom (.symbol { name := "quote" }))
      (.cons SExpr.t .nil)
    let node : ProofNode := .node ("equal-self", "NIL") equal_1_1 quote_t []
    let proof ← proveNode ctx node
    let _ ← check proof
    logInfo m!"proveNode equal-self OK: {← inferType proof}"

#test_prove_node_equal_self

-- Test: proveLiteralChain with a single equal-self node
-- Literal: (EQUAL 1 1), nodes: [equal-self], result: (QUOTE T)
elab "#test_literal_chain" : command => do
  Elab.Command.liftTermElabM do
    let emptyEnv ← mkEmptyEnv
    let ctx : ProofCtx := {
      worldExpr := Lean.mkConst ``World.empty
      world := World.empty
      envExpr := emptyEnv
      worldUnfoldNames := #[``World.empty]
    }
    let one : SExpr := .atom (.number (.int 1))
    let equal_1_1 : SExpr := .cons (.atom (.symbol { name := "equal" }))
      (.cons one (.cons one .nil))
    let quote_t : SExpr := .cons (.atom (.symbol { name := "quote" }))
      (.cons SExpr.t .nil)
    let node : ProofNode := .node ("equal-self", "NIL") equal_1_1 quote_t []
    let proof ← proveLiteralChain ctx equal_1_1 [node]
    let _ ← check proof
    logInfo m!"literal chain OK: {← inferType proof}"

#test_literal_chain

end MetaMTests

end ACL2.Replay.ProofProducer
