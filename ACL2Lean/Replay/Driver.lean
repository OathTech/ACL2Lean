/-
  Proof-producing driver (stage 7 — the eventual `acl2_replay`).

  This is the schematic replay driver: it walks the reconstructed proof tree and
  emits a Lean `Expr` proving the mirror theorem, by instantiating — per node —
  the per-rune combinator the hand proofs (`Imported/SimpleWorld.lean`,
  `Imported/AppAssoc.lean`) were written to be instances of. See
  `docs/plans/2026-06-08_driver-build-plan.md` and
  `docs/notes/2026-06-07_{driver-design,schematic-replay-rule}.md`.

  Replaces the retired `Replay/ProofProducer.lean` (the old value-computation
  skeleton, which computed both sides and matched — the banned shortcut).

  ## Architecture (per `docs/notes/2026-06-07_driver-design.md`).

  The driver is a RECURSIVE function over the reconstructed tree —
  `replayClause : World → Env → ReplayCtx → ClauseNode → MetaM Expr` and
  `replayNode : … → ProofNode → MetaM Expr` — reading every term/rune/subst/scheme
  FROM the tree. Nothing is transcribed or pre-staged: the only inputs are the
  parsed `Development`/`ClauseProof` (from `ProofLog.parse → buildDevelopment`) and
  the `World` + mirror statement (from `gen-world`).

  FAIL-CLOSED, NEVER `sorry`. Each `replay*` either returns a real, kernel-checkable
  `Expr` of the node's exact goal, or **throws** — so an unimplemented frontier makes
  the theorem fail to compile, never produces a fake proof. This is a soundness
  invariant: a driver built only from `throwError` + kernel-checked per-rune lemmas
  can only ever emit valid proofs. (NO `mkSorry` anywhere — that would be a cheat.)

  Build sequence (see the plan file):
  - S1 — dummy driver, correct type, fail-closed (`throwError` on every node). Proven
    by `#check` of the types + a NEGATIVE test that it fails cleanly on a tree.
  - S2 — one `equal-self` node (hand-built minimal `ClauseProof` value) → a real
    sorry-free mirror theorem, `#print axioms` clean. Solves the proof-object plumbing
    (reflection, fuel wrapper, mirror matching, tactic) on the minimal case.
  - S3+ — grow by tree complexity (exec-counterpart, congruence, induction/IH), each
    driven by a progressively larger hand-built then real parsed tree.

  Below are the GENERAL, tree-agnostic helpers (reflection, congruence-path emitter,
  chaining, goal-type builders) the recursion is built from.
-/
import ACL2Lean.Replay.EvalLemmas
import ACL2Lean.ProofTree
import ACL2Lean.ClauseTree
import Lean

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-! ## Reflection: SExpr → Lean Expr (framing-neutral; kept from the old producer) -/

def reflectInt : Int → Expr
  | .ofNat n => mkApp (mkConst ``Int.ofNat) (mkNatLit n)
  | .negSucc n => mkApp (mkConst ``Int.negSucc) (mkNatLit n)

def reflectSymbol (s : Symbol) : Expr :=
  mkApp2 (mkConst ``Symbol.mk) (mkStrLit s.package) (mkStrLit s.name)

def reflectNumber : Number → Expr
  | .int v => mkApp (mkConst ``Number.int) (reflectInt v)
  | .rational num den =>
    mkApp2 (mkConst ``Number.rational) (reflectInt num) (mkNatLit den)
  | .decimal m e =>
    mkApp2 (mkConst ``Number.decimal) (reflectInt m) (reflectInt e)

def reflectAtom : Atom → Expr
  | .symbol s => mkApp (mkConst ``Atom.symbol) (reflectSymbol s)
  | .keyword k => mkApp (mkConst ``Atom.keyword) (mkStrLit k)
  | .string s => mkApp (mkConst ``Atom.string) (mkStrLit s)
  | .number n => mkApp (mkConst ``Atom.number) (reflectNumber n)

def reflectSExpr : SExpr → Expr
  | .nil => mkConst ``SExpr.nil
  | .atom a => mkApp (mkConst ``SExpr.atom) (reflectAtom a)
  | .cons car cdr =>
    mkApp2 (mkConst ``SExpr.cons) (reflectSExpr car) (reflectSExpr cdr)

/-- Prove a decidable proposition `p` by **kernel decision** — deterministic ground
    computation (evaluate the `Decidable` instance via `whnf`, then `of_decide_eq_true`).
    NOT heuristic: no simp set, no search. The single side-condition discharger the
    driver uses for all ground facts (non-special symbols, world non-shadowing, …).
    Hard-fails if `p` does not reduce to `true`. -/
def proveByDecide (p : Expr) (label : String) : MetaM Expr := do
  let inst ← synthInstance (mkApp (mkConst ``Decidable) p)
  let reduced ← withTransparency .all <| whnf (mkApp2 (mkConst ``decide) p inst)
  unless reduced == mkConst ``Bool.true do
    throwError "proveByDecide ({label}): {← ppExpr p} did not reduce to true"
  return mkApp3 (mkConst ``of_decide_eq_true) p inst
    (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))

/-- Prove `fn.isNamed "quote" = false ∧ "if" = false ∧ "let" = false ∧ "let*" = false`
    — the `…_not_special` side-condition every congruence wants. -/
def proveNotSpecial (s : Symbol) : MetaM Expr := do
  let sExpr := reflectSymbol s
  let boolType := mkConst ``Bool
  let falseExpr := mkConst ``Bool.false
  let mkEqFalse (name : String) : Expr :=
    mkApp3 (mkConst ``Eq [1]) boolType
      (mkApp2 (mkConst ``Symbol.isNamed) sExpr (mkStrLit name)) falseExpr
  let mkAnd (a b : Expr) : Expr := mkApp2 (mkConst ``And) a b
  proveByDecide (mkAnd (mkEqFalse "quote")
    (mkAnd (mkEqFalse "if") (mkAnd (mkEqFalse "let") (mkEqFalse "let*")))) "not-special"

/-! ## Goal-type builders -/

/-- The fuel-robust eval-equality Prop `∃ N, ∀ f ≥ N, evalOpt f w e a = evalOpt f w e b`. -/
def mkEvalEqExist (w e : Expr) (a b : SExpr) : MetaM Expr := do
  let aE := reflectSExpr a; let bE := reflectSExpr b
  withLocalDeclD `N (mkConst ``Nat) fun nVar => do
    let body ← withLocalDeclD `f (mkConst ``Nat) fun fVar => do
      let ge ← mkAppM ``GE.ge #[fVar, nVar]
      let lhs := mkAppN (mkConst ``evalOpt) #[fVar, w, e, aE]
      let rhs := mkAppN (mkConst ``evalOpt) #[fVar, w, e, bE]
      mkForallFVars #[fVar] (← mkArrow ge (← mkEq lhs rhs))
    mkAppM ``Exists #[← mkLambdaFVars #[nVar] body]

/-- The fuel-robust convergence Prop `∃ N, ∀ f ≥ N, evalOpt f w e a = some v`
    where `v` is supplied as an `Expr` (e.g. `mkConst ``SExpr.t`). -/
def mkEvalSomeExist (w e : Expr) (a : SExpr) (v : Expr) : MetaM Expr := do
  let aE := reflectSExpr a
  withLocalDeclD `N (mkConst ``Nat) fun nVar => do
    let body ← withLocalDeclD `f (mkConst ``Nat) fun fVar => do
      let ge ← mkAppM ``GE.ge #[fVar, nVar]
      let lhs := mkAppN (mkConst ``evalOpt) #[fVar, w, e, aE]
      let rhs := mkApp2 (mkConst ``Option.some [0]) (mkConst ``SExpr) v
      mkForallFVars #[fVar] (← mkArrow ge (← mkEq lhs rhs))
    mkAppM ``Exists #[← mkLambdaFVars #[nVar] body]

/-! ## G2: the congruence-path emitter

A literal term is `(fn arg₀ … argₖ)`; a node rewrites a subterm `lhs ⇒ rhs` at the
position ACL2 recorded in the node's `:PATH`. We NAVIGATE the literal along that path
(no search) and wrap the node's eval-equality in the arity-specific congruences,
discharging each head's `…_not_special` by `decide`. Position comes from ACL2; the
sibling subterms come from the literal as we descend. -/

/-- One step on the path from a term down to the redex: the head symbol, its arity,
    the argument index we descend into, and the sibling args (unchanged). -/
private structure PathStep where
  fn : Symbol
  arity : Nat
  argIdx : Nat
  siblings : List SExpr   -- the OTHER args, in order, excluding `argIdx`
  deriving Inhabited

/-- View an SExpr as `(fn arg₀ … argₖ)`: head must be a symbol. -/
private def asApp (t : SExpr) : Option (Symbol × List SExpr) :=
  match t.toList? with
  | some (.atom (.symbol fn) :: args) => some (fn, args)
  | _ => none

/-- Build the congruence steps from the node's `:PATH` (`PathFrame`s, literal-root
    first) by NAVIGATING `term`: the head frame is the literal itself, and each later
    `.arg bkptr fn` frame descends into argument `bkptr`. Returns the steps outer→inner
    (whose composition lifts the redex to `term`), and verifies the navigated subterm
    is `lhs`. Position comes entirely from the path — no subterm search, no ambiguity.
    `.boundary` frames (child nodes inside an unfold) and arity > 2 are not yet
    supported — hard-fail. -/
private def pathStepsFromFrames (term : SExpr) (frames : List PathFrame) (lhs : SExpr)
    : Except String (List PathStep) := do
  let mut cur := term
  let mut steps : List PathStep := []
  for fr in frames.drop 1 do          -- drop the literal-root frame; descend the rest
    match fr with
    | .boundary k _ =>
      throw s!"pathStepsFromFrames: boundary frame {k.name} (child-node congruence unsupported)"
    | .arg idx _ =>
      match asApp cur with
      | none => throw s!"pathStepsFromFrames: path descends into non-application {repr cur}"
      | some (fn, args) =>
        if args.length > 2 then
          throw s!"pathStepsFromFrames: arity {args.length} application unsupported (only ≤ 2): {repr cur}"
        if idx < 1 || idx > args.length then
          throw s!"pathStepsFromFrames: arg index {idx} out of range for {repr cur}"
        let siblings := (args.zipIdx).filterMap (fun (a, i) => if i + 1 == idx then none else some a)
        steps := steps ++ [{ fn, arity := args.length, argIdx := idx - 1, siblings }]
        cur := args[idx - 1]!
  unless cur == lhs do
    throw s!"pathStepsFromFrames: navigated to {repr cur}, expected redex {repr lhs}"
  return steps

/-- Reconstruct the parent term `(fn …)` placing `sub` at `argIdx`, siblings elsewhere. -/
private def rebuild (fn : Symbol) (arity argIdx : Nat) (sub : SExpr) (siblings : List SExpr) : SExpr :=
  let args : List SExpr :=
    match arity, argIdx, siblings with
    | 1, 0, _ => [sub]
    | 2, 0, [s] => [sub, s]
    | 2, 1, [s] => [s, sub]
    | _, _, _ => panic! "rebuild: bad arity/argIdx"
  -- build (fn args...) as a proper s-expression list
  .cons (.atom (.symbol fn)) (args.foldr SExpr.cons .nil)

/-- Apply one congruence step. `inner : ∃N∀f≥N, eval (sub) = eval (sub')`; returns
    `∃N∀f≥N, eval (fn … sub …) = eval (fn … sub' …)`. -/
private def applyStep (w e : Expr) (st : PathStep) (sub sub' : SExpr) (inner : Expr) : MetaM Expr := do
  let ns ← proveNotSpecial st.fn
  let fnE := reflectSymbol st.fn
  match st.arity, st.argIdx, st.siblings with
  | 1, 0, _ =>
    return mkAppN (mkConst ``evalOpt_congr_unary)
      #[w, e, fnE, reflectSExpr sub, reflectSExpr sub', ns, inner]
  | 2, 0, [b] =>
    return mkAppN (mkConst ``evalOpt_congr_binary_left)
      #[w, e, fnE, reflectSExpr sub, reflectSExpr sub', reflectSExpr b, ns, inner]
  | 2, 1, [a] =>
    return mkAppN (mkConst ``evalOpt_congr_binary_right)
      #[w, e, fnE, reflectSExpr a, reflectSExpr sub, reflectSExpr sub', ns, inner]
  | _, _, _ => throwError "applyStep: unsupported arity/argIdx {st.arity}/{st.argIdx}"

/-- Lift a node proof `nodeProof : ∃N∀f≥N, eval lhs = eval rhs` to the whole literal
    `term`, DIRECTED by the node's `:PATH` (`frames`) — no subterm search. Returns the
    lifted proof and the rewritten term `term[lhs := rhs]`. -/
def emitCongruence (w e : Expr) (term : SExpr) (frames : List PathFrame)
    (lhs rhs : SExpr) (nodeProof : Expr) : MetaM (Expr × SExpr) := do
  let path ← ofExcept (pathStepsFromFrames term frames lhs)
  -- Fold from the innermost path step outward.
  let mut inner := nodeProof
  let mut curL := lhs
  let mut curR := rhs
  for st in path.reverse do
    inner ← applyStep w e st curL curR inner
    curL := rebuild st.fn st.arity st.argIdx curL st.siblings
    curR := rebuild st.fn st.arity st.argIdx curR st.siblings
  unless curL == term do
    throwError "emitCongruence: reconstructed outer term {repr curL} ≠ input {repr term}"
  return (inner, curR)

/-- Chain a non-empty list of fuel-robust equalities `[a=b, b=c, …]` with `fuel_chain_eq`. -/
def chainEqs (proofs : List Expr) : MetaM Expr := do
  match proofs with
  | [] => throwError "chainEqs: empty"
  | p :: ps => ps.foldlM (fun acc q => mkAppM ``fuel_chain_eq #[acc, q]) p

/-! ## The recursive driver (`replayClause` / `replayNode`).

A recursive function over the reconstructed tree, per
`docs/notes/2026-06-07_driver-design.md`. It reads every term/rune/subst/scheme FROM
the tree — nothing transcribed. FAIL-CLOSED: each `replay*` returns a real
kernel-checkable `Expr` or `throwError`s; NEVER `sorry`.

S1 (dummy) = every node `throwError`s. S2 adds the single `equal-self` terminal. -/

/-- Carried info for a defined (1-arg) function `fn`: its formal and body, plus the
    proof terms about the concrete world that `re_unfold1_conv` needs. Established once
    when the config is built (test harness now, `gen-world` later). -/
structure DefInfo where
  formal : Symbol
  body : SExpr
  /-- `w.defs.get? fn = some ([formal], body)`. -/
  defFact : Expr
  /-- `∀ s ∈ freeVars body, s ∈ [formal]`. -/
  closedFact : Expr
  /-- `NoLet body = true`. -/
  noLetFact : Expr

/-- Ambient config: the `World` (as both an `Expr` for proof terms and a `World` value
    so the driver can read formals/bodies) and the `Env` `Expr`. The structural world
    facts (`defs.get? fn = …`, builtin-not-shadowed, freeVars⊆formals, NoLet) are NOT
    carried — the driver **derives each one on demand by kernel decision**
    (`proveNoShadow` / `deriveDefInfo`), since `World.defs` is now a reduction-friendly
    `DefMap`. No hand-marshalled facts, no per-example config. This is NOT inference: a
    `decide` over a concrete map is evaluation, not search. -/
structure ReplayConfig where
  worldExpr : Expr
  envExpr : Expr
  worldVal : World := {}

/-- The proof context in scope at a node (design note). Grows as stages land; S1/S2
    populate none of it. -/
structure ReplayCtx where
  caseHyps : List Expr := []
  ih : Option Expr := none
  typeFacts : List Expr := []
  envBindings : List (Symbol × Expr) := []

def ReplayCtx.empty : ReplayCtx := {}

/-- `(quote t)`, the result an equal-self literal reduces to. -/
def quoteT : SExpr := .cons (.atom (.symbol { name := "quote" })) (.cons SExpr.t .nil)

/-- View `(equal X X)` as `X`. -/
def asEqualSelf : SExpr → Option SExpr
  | .cons (.atom (.symbol s)) (.cons x (.cons x' .nil)) =>
    if s.name == "equal" && x == x' then some x else none
  | _ => none

def runeOf : ProofNode → String × String | .node r _ _ _ _ => r
def nodeLhsRhs : ProofNode → SExpr × SExpr | .node _ lhs rhs _ _ => (lhs, rhs)
def nodePath : ProofNode → List PathFrame | .node _ _ _ _ p => p.path

/-- `worldExpr.defs.get? s` as an `Expr` (a `DefMap.get?` application). -/
private def mkDefsGet (cfg : ReplayConfig) (s : Symbol) : MetaM Expr := do
  mkAppM ``ACL2.DefMap.get? #[← mkAppM ``ACL2.World.defs #[cfg.worldExpr], reflectSymbol s]

/-- Derive `worldExpr.defs.get? s = none` (builtin `s` not shadowed by a defun) by kernel
    decision. Replaces the hand-carried `noShadow` fact: the lookup REDUCES on the concrete
    `DefMap`, so `decide` settles it. Hard-fails (via `proveByDecide`) if `s` IS defined. -/
def proveNoShadow (cfg : ReplayConfig) (s : Symbol) : MetaM Expr := do
  let lookup ← mkDefsGet cfg s
  let elemTy := (← inferType lookup).appArg!
  let noneE := mkApp (mkConst ``Option.none [0]) elemTy
  proveByDecide (← mkEq lookup noneE) s!"no-shadow {s.name}"

/-- Derive a defined (1-arg) function's `DefInfo` on demand from the World, with all three
    structural facts proved by kernel decision (no hand-written theorems):
    - `defFact`   : `worldExpr.defs.get? fn = some ([formal], body)`
    - `closedFact`: `∀ s ∈ freeVars body, s ∈ [formal]`
    - `noLetFact` : `NoLet body = true`
    `formal`/`body` are read from `cfg.worldVal` (the concrete World); `proveByDecide`
    re-checks each fact against `worldExpr`, so a `worldVal`/`worldExpr` mismatch hard-fails.
    Multi-arg / not-defined hard-fail (1-arg unfold is the current frontier). -/
def deriveDefInfo (cfg : ReplayConfig) (fn : Symbol) : MetaM DefInfo := do
  match cfg.worldVal.defs.get? fn with
  | none => throwError "deriveDefInfo: {fn.name} not defined in the world"
  | some (formals, body) =>
    let formal ← match formals with
      | [f] => pure f
      | _ => throwError "deriveDefInfo: {fn.name} has {formals.length} formals; only 1-arg \
                         definition-unfold is supported (frontier)"
    let formalsE ← mkListLit (mkConst ``Symbol) (formals.map reflectSymbol)
    let bodyE := reflectSExpr body
    -- defFact : worldExpr.defs.get? fn = some (formals, body)
    let someE ← mkAppM ``Option.some #[← mkAppM ``Prod.mk #[formalsE, bodyE]]
    let defFact ← proveByDecide (← mkEq (← mkDefsGet cfg fn) someE) s!"def {fn.name}"
    -- closedFact : ∀ s ∈ freeVars body, s ∈ formals
    let fvE ← mkAppM ``ACL2.Replay.freeVars #[bodyE]
    let closedProp ← withLocalDeclD `s (mkConst ``ACL2.Symbol) fun sv => do
      let memFv ← mkAppM ``Membership.mem #[fvE, sv]
      let memFm ← mkAppM ``Membership.mem #[formalsE, sv]
      mkForallFVars #[sv] (← mkArrow memFv memFm)
    let closedFact ← proveByDecide closedProp s!"closed {fn.name}"
    -- noLetFact : NoLet body = true
    let noLetFact ← proveByDecide
      (← mkEq (← mkAppM ``ACL2.Replay.NoLet #[bodyE]) (mkConst ``Bool.true)) s!"nolet {fn.name}"
    return { formal, body, defFact, closedFact, noLetFact }

/-- Prove `s.isNamed name = false` by kernel decision. -/
def proveIsNamedFalse (s : Symbol) (name : String) : MetaM Expr :=
  proveByDecide
    (mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
      (mkApp2 (mkConst ``Symbol.isNamed) (reflectSymbol s) (mkStrLit name)) (mkConst ``Bool.false))
    s!"{s.name}.isNamed {name} = false"

/-- Prove a term CONVERGES (v-fixed totality): `∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env t = some v`
    — a single definite value (`evalOpt` is fuel-monotone), so callers can `obtain` the
    witness and feed any value-specific lemma. The value may be env-dependent (a free
    variable) but is still fixed across fuel. S2 handles a free variable (via `re_conv_var`,
    valid for ALL `env`) and a `(quote v)` constant; any other shape is an unimplemented
    frontier → `throwError` (the full convergence analyzer, G1, lands in a later stage). -/
partial def proveConv (cfg : ReplayConfig) (envExpr : Expr) (ctx : ReplayCtx) (t : SExpr) :
    MetaM Expr := do
  match t with
  | .atom (.symbol s) =>
    let hNotT ← proveIsNamedFalse s "t"
    mkAppM ``re_conv_var #[cfg.worldExpr, envExpr, reflectSymbol s, hNotT]
  | .cons (.atom (.symbol qs)) (.cons v .nil) =>
    if qs.name == "quote" then
      mkAppM ``re_conv_quote #[cfg.worldExpr, envExpr, reflectSExpr v]
    else if qs.name == "car" || qs.name == "cdr" || qs.name == "consp" then
      -- unary builtin: recurse on the operand, apply that builtin's conv wrapper.
      let ha ← proveConv cfg envExpr ctx v
      let hNo ← proveNoShadow cfg qs
      let lem := match qs.name with
        | "car" => ``re_conv_car | "cdr" => ``re_conv_cdr | _ => ``re_conv_consp
      mkAppM lem #[cfg.worldExpr, envExpr, reflectSExpr v, hNo, ha]
    else throwError "proveConv: no convergence rule for unary {qs.name}: {repr t}"
  | .cons (.atom (.symbol bs)) (.cons a (.cons b .nil)) =>
    -- builtin application — recurse on operands, apply that builtin's conv wrapper.
    if bs.name == "cons" then
      let ha ← proveConv cfg envExpr ctx a
      let hb ← proveConv cfg envExpr ctx b
      let hNoCons ← proveNoShadow cfg { name := "cons" }
      mkAppM ``re_conv_cons #[cfg.worldExpr, envExpr, reflectSExpr a, reflectSExpr b, hNoCons, ha, hb]
    else if bs.name == "binary-*" then
      let ha ← proveConv cfg envExpr ctx a
      let hb ← proveConv cfg envExpr ctx b
      let hNoTimes ← proveNoShadow cfg { name := "binary-*" }
      mkAppM ``re_conv_times #[cfg.worldExpr, envExpr, reflectSExpr a, reflectSExpr b, hNoTimes, ha, hb]
    else if bs.name == "binary-+" then
      let ha ← proveConv cfg envExpr ctx a
      let hb ← proveConv cfg envExpr ctx b
      let hNoPlus ← proveNoShadow cfg { name := "binary-+" }
      mkAppM ``re_conv_plus #[cfg.worldExpr, envExpr, reflectSExpr a, reflectSExpr b, hNoPlus, ha, hb]
    else throwError "proveConv: no convergence rule for binary {bs.name}: {repr t}"
  | _ => throwError "proveConv: no convergence rule for {repr t}"

/-- Prove a term converges in EVERY environment: `∀ env', ∃ N, ∃ v, ∀ f ≥ N,
    evalOpt f w env' t = some v`. Runs `proveConv` under a quantified `env'` and
    λ-abstracts. (Used for a definition body, whose convergence `re_unfold1_conv` needs
    at the `bindArgs` env.) -/
def proveConvAllEnv (cfg : ReplayConfig) (ctx : ReplayCtx) (t : SExpr) : MetaM Expr := do
  withLocalDeclD `env' (mkConst ``Env) fun env' => do
    let p ← proveConv cfg env' ctx t
    mkLambdaFVars #[env'] p

/-- Replay one rewrite node to its eval-equality `∃N∀f≥N, eval lhs = eval rhs`, by
    applying that rune's combinator. (equal-self is the literal closer, handled in
    `replayLiteral`, not here.) Unhandled runes hard-fail (fail-closed). -/
def replayNode (cfg : ReplayConfig) (ctx : ReplayCtx) (n : ProofNode) : MetaM Expr := do
  let (rty, rname) := runeOf n
  let (lhs, rhs) := nodeLhsRhs n
  match rty, rname with
  | "rewrite", "cdr-cons" =>
    -- `(cdr (cons a b)) ⇒ b`.
    match lhs with
    | .cons (.atom (.symbol cdrS))
        (.cons (.cons (.atom (.symbol consS)) (.cons a (.cons b .nil))) .nil) =>
      unless cdrS.name == "cdr" && consS.name == "cons" do
        throwError "cdr-cons: lhs head not (cdr (cons …)): {repr lhs}"
      unless rhs == b do
        throwError "cdr-cons: rhs {repr rhs} ≠ the cons's cdr operand {repr b}"
      let ha ← proveConv cfg cfg.envExpr ctx a
      let hb ← proveConv cfg cfg.envExpr ctx b
      let hNoCdr ← proveNoShadow cfg { name := "cdr" }
      let hNoCons ← proveNoShadow cfg { name := "cons" }
      mkAppM ``re_cdr_cons_conv
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr a, reflectSExpr b, hNoCdr, hNoCons, ha, hb]
    | _ => throwError "cdr-cons: lhs not (cdr (cons a b)): {repr lhs}"
  | "definition", _ =>
    -- `(fn arg) ⇒ substTerm [formal] [arg] body`. DefInfo (def/closed/no-let facts) is
    -- DERIVED from the world on the fly — no carried config.
    match lhs with
    | .cons (.atom (.symbol fn)) (.cons arg .nil) =>
      let di ← deriveDefInfo cfg fn
      let hns ← proveNotSpecial fn
      let harg ← proveConv cfg cfg.envExpr ctx arg
      let hbodyAll ← proveConvAllEnv cfg ctx di.body
      mkAppM ``re_unfold1_conv
        #[cfg.worldExpr, cfg.envExpr, reflectSymbol fn, reflectSymbol di.formal,
          reflectSExpr di.body, reflectSExpr arg, hns,
          di.defFact, di.closedFact, di.noLetFact, harg, hbodyAll]
    | _ => throwError "definition: lhs not a 1-arg application (fn arg): {repr lhs}"
  | _, _ =>
    throwError "replayNode: no rule for rune ({rty}, {rname}) — unimplemented frontier"

/-- Replay a chain of rewrite nodes, lifting each through the literal context and
    chaining. Returns the composed `∃N∀f≥N, eval start = eval finalTerm` (or `none`
    if the chain is empty) and the final term. -/
partial def replayRewrites (cfg : ReplayConfig) (ctx : ReplayCtx) (start : SExpr) :
    List ProofNode → MetaM (Option Expr × SExpr)
  | [] => return (none, start)
  | n :: rest => do
    let (lhs, rhs) := nodeLhsRhs n
    let nodeEq ← replayNode cfg ctx n
    let (lifted, newTerm) ← emitCongruence cfg.worldExpr cfg.envExpr start (nodePath n) lhs rhs nodeEq
    let (restProof, finalTerm) ← replayRewrites cfg ctx newTerm rest
    match restProof with
    | none => return (some lifted, finalTerm)
    | some rp => return (some (← mkAppM ``fuel_chain_eq #[lifted, rp]), finalTerm)

/-- Replay a literal that closes to `t`: chain its rewrite nodes, then close with the
    terminal `equal-self` node. Returns `∃N∀f≥N, eval lp.literal = some t`. -/
def replayLiteral (cfg : ReplayConfig) (ctx : ReplayCtx) (lp : LiteralProof) : MetaM Expr := do
  match lp.nodes.reverse with
  | [] => throwError "replayLiteral: literal {repr lp.literal} has no proof nodes"
  | closer :: revRest =>
    match closer with
    | .node ("equal-self", _) clhs _ _ _ =>
      match asEqualSelf clhs with
      | none => throwError "replayLiteral: equal-self lhs is not (equal X X): {repr clhs}"
      | some X =>
        let (chainOpt, curTerm) ← replayRewrites cfg ctx lp.literal revRest.reverse
        unless curTerm == clhs do
          throwError "replayLiteral: rewrite chain reached {repr curTerm}, \
                      expected equal-self redex {repr clhs}"
        let hX ← proveConv cfg cfg.envExpr ctx X
        let hNoEqual ← proveNoShadow cfg { name := "equal" }
        let closeProof ← mkAppM ``re_equal_self
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr X, hX, hNoEqual]
        match chainOpt with
        | none => return closeProof
        | some ch => mkAppM ``fuel_chain_eq #[ch, closeProof]
    | _ => throwError "replayLiteral: terminal node is not equal-self (rune {repr (runeOf closer)})"

/-- The first literal in a clause's items that reduces to `(quote t)` (the disjunct
    that makes the clause true). -/
partial def findClosingLiteral : List ClauseItem → Option LiteralProof
  | [] => none
  | .literal lp :: rest => if lp.result == quoteT then some lp else findClosingLiteral rest
  | .step _ :: rest => findClosingLiteral rest
  | .branch _ items :: rest =>
    match findClosingLiteral items with
    | some lp => some lp
    | none => findClosingLiteral rest

/-- Replay a clause node: prove `∃N∀f≥N, eval clauseFormula = some t`. S2: no
    induction, no case-split children — find the literal that closes to `t` and
    replay it. Induction / multi-clause structure hard-fails (lands in S3+). -/
partial def replayClause (cfg : ReplayConfig) (ctx : ReplayCtx) (cn : ClauseNode) : MetaM Expr := do
  if cn.induction.isSome then
    throwError "replayClause: induction scheme not yet supported (clause {cn.idStr})"
  let allItems := cn.steps.flatMap (·.items)
  match findClosingLiteral allItems with
  | some lp => replayLiteral cfg ctx lp
  | none => throwError "replayClause: no literal closing to (quote t) in clause {cn.idStr}"

/-- Replay a whole theorem's proof tree to its mirror statement
    `∃N∀f≥N, eval cp.formula = some t`. -/
def replayProof (cfg : ReplayConfig) (cp : ClauseProof) : MetaM Expr := do
  match cp.root with
  | none => throwError "replayProof: theorem {cp.name} has no proof tree"
  | some root => replayClause cfg ReplayCtx.empty root

end ACL2.Replay.Driver
