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

/-- Reflect a concrete `DefMap` value to an `Expr` (`DefMap.mk [(s, (formals, body)), …]`).
    `mkAppM`/`mkListLit` infer the implicit type args. Used to emit a CONCRETE world def
    (fast-reducing under `decide`) projected from a parsed `Development` — see
    `Development.toWorld` / `reflectWorld`. -/
def reflectDefMap (m : DefMap) : MetaM Expr := do
  let symTy := mkConst ``Symbol
  let entryTy ← mkAppM ``Prod #[symTy, ← mkAppM ``Prod #[← mkAppM ``List #[symTy], mkConst ``SExpr]]
  let entries ← m.entries.mapM fun (s, formals, body) => do
    let formalsE ← mkListLit symTy (formals.map reflectSymbol)
    mkAppM ``Prod.mk #[reflectSymbol s, ← mkAppM ``Prod.mk #[formalsE, reflectSExpr body]]
  mkAppM ``ACL2.DefMap.mk #[← mkListLit entryTy entries]

/-- Reflect a concrete `World` to an `Expr` as `World.ofDefs <reflected defs>` — only `defs`
    matters to `evalOpt`. -/
def reflectWorld (w : World) : MetaM Expr := do
  mkAppM ``ACL2.World.ofDefs #[← reflectDefMap w.defs]

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

/-- Relativize a node's `:PATH` to its nesting depth: at depth 0 (a top-level chain
    node) drop the literal-root descriptor frame; at depth d > 0 (a child d unfold/
    rule boundaries deep) drop everything through the d-th `.boundary` frame — the
    remainder navigates within the chain's start term (the substituted body /
    rule rhs). -/
def relativizeFrames (frames : List PathFrame) (depth : Nat) : Except String (List PathFrame) :=
  if depth == 0 then pure (frames.drop 1)
  else go frames depth
where
  go : List PathFrame → Nat → Except String (List PathFrame)
    | fs, 0 => pure fs
    | [], d => throw s!"relativizeFrames: path exhausted with {d} boundaries still expected"
    | .boundary _ _ :: rest, d => go rest (d - 1)
    | _ :: rest, d => go rest d

private def pathStepsFromFrames (term : SExpr) (descentFrames : List PathFrame) (lhs : SExpr)
    : Except String (List PathStep) := do
  let mut cur := term
  let mut steps : List PathStep := []
  for fr in descentFrames do
    match fr with
    | .boundary k _ =>
      throw s!"pathStepsFromFrames: unexpected residual boundary frame {k.name} \
              (nesting deeper than the chain's depth)"
    | .arg idx _ =>
      match asApp cur with
      | none => throw s!"pathStepsFromFrames: path descends into non-application {repr cur}"
      | some (fn, args) =>
        if args.length == 3 then
          -- only the lazy `if`'s TEST position admits congruence
          unless fn.name == "if" && idx == 1 do
            throw s!"pathStepsFromFrames: arity-3 congruence only into an if's test \
                    (got {fn.name} arg {idx}): {repr cur}"
        else if args.length > 3 then
          throw s!"pathStepsFromFrames: arity {args.length} application unsupported: {repr cur}"
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
    | 3, 0, [t, e] => [sub, t, e]   -- if-test position
    | _, _, _ => panic! "rebuild: bad arity/argIdx"
  -- build (fn args...) as a proper s-expression list
  .cons (.atom (.symbol fn)) (args.foldr SExpr.cons .nil)

/-- Apply one congruence step. `inner : ∃N∀f≥N, eval (sub) = eval (sub')`; returns
    `∃N∀f≥N, eval (fn … sub …) = eval (fn … sub' …)`. -/
private def applyStep (w e : Expr) (st : PathStep) (sub sub' : SExpr) (inner : Expr) : MetaM Expr := do
  let fnE := reflectSymbol st.fn
  match st.arity, st.argIdx, st.siblings with
  | 1, 0, _ =>
    let ns ← proveNotSpecial st.fn
    return mkAppN (mkConst ``evalOpt_congr_unary)
      #[w, e, fnE, reflectSExpr sub, reflectSExpr sub', ns, inner]
  | 2, 0, [b] =>
    let ns ← proveNotSpecial st.fn
    return mkAppN (mkConst ``evalOpt_congr_binary_left)
      #[w, e, fnE, reflectSExpr sub, reflectSExpr sub', reflectSExpr b, ns, inner]
  | 2, 1, [a] =>
    let ns ← proveNotSpecial st.fn
    return mkAppN (mkConst ``evalOpt_congr_binary_right)
      #[w, e, fnE, reflectSExpr a, reflectSExpr sub, reflectSExpr sub', ns, inner]
  | 3, 0, [t, el] =>
    -- the lazy if's TEST position (the only sound arity-3 congruence)
    unless st.fn.name == "if" do
      throwError "applyStep: arity-3 congruence only for if (got {st.fn.name})"
    return mkAppN (mkConst ``evalOpt_congr_if_test)
      #[w, e, reflectSExpr sub, reflectSExpr sub', reflectSExpr t, reflectSExpr el, inner]
  | _, _, _ => throwError "applyStep: unsupported arity/argIdx {st.arity}/{st.argIdx}"

/-- Lift a node proof `nodeProof : ∃N∀f≥N, eval lhs = eval rhs` to the whole literal
    `term`, DIRECTED by the node's `:PATH` (`frames`) — no subterm search. Returns the
    lifted proof and the rewritten term `term[lhs := rhs]`.

    `strip`: branch frames already CONSUMED by earlier chain steps. ACL2's
    `rewrite-if` recurses into a resolved if's surviving branch with the if still
    on its gstack, so a node logged after an if-simplification carries the
    branch's `:PATH` frame even though the chain's current term no longer has the
    if — each `k ∈ strip` (in order) must match and is dropped.

    SCOPE: `strip` covers exactly the chain-ROOT if-simplification case (the only
    place `replayRewrites` records one); unfold/rule-RHS nesting is the SEPARATE
    `.boundary`/`depth` mechanism in `relativizeFrames`. Their composition
    (a branch frame interleaved between residual boundary frames) is NOT handled —
    and cannot mis-navigate silently: a strip/frame mismatch throws here, and any
    leftover misalignment fails `pathStepsFromFrames`' final redex check. -/
def emitCongruence (w e : Expr) (term : SExpr) (frames : List PathFrame)
    (lhs rhs : SExpr) (nodeProof : Expr) (depth : Nat := 0) (strip : List Nat := [])
    : MetaM (Expr × SExpr) := do
  let mut rel ← ofExcept (relativizeFrames frames depth)
  for k in strip do
    match rel with
    | .arg idx _ :: restF =>
      unless idx == k do
        throwError "emitCongruence: chain consumed branch frame {k}, but the node's \
                    path has arg {idx} there"
      rel := restF
    | _ =>
      throwError "emitCongruence: chain consumed branch frame {k}, but the node's \
                  path has no arg frame there"
  let path ← ofExcept (pathStepsFromFrames term rel lhs)
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

/-- The proof context in scope at a node. All entries are VALUE-CHARACTERIZED
    facts over the ambient env, established by the surrounding structure (the
    induction scaffold, the clause spine) and consumed by the node replays:

    - `varVals`: variable ↦ (value `Expr`, proof `∃N∀f≥N, eval (var s) = some value`).
      The induction scaffold binds the controller's value here (`xv`); unlisted
      variables are resolved on demand (`re_val_var`, value `(env.get? s).getD nil`).
    - `vals`: term ↦ (value, convergence proof) — opaque user-fn occurrences
      (obtained from totality hypotheses at clause entry) and any other term whose
      value is pinned in scope.
    - `nilFacts`: literal term ↦ (its value `Expr`, proof `value = .nil`) — the
      clause spine's accumulated "earlier literals are false" hypotheses; feeds
      recognizer/false nodes and the solidify IH bridge.
    - `ih`: the induction hypothesis (the scaffold's `P (cdr xv)` instance), when
      inside a step case. -/
structure ReplayCtx where
  varVals : List (Symbol × Expr × Expr) := []
  vals : List (SExpr × Expr × Expr) := []
  /-- The clause spine's accumulated falsity facts: (1-based literal index, the
      literal's current — post-rewrite — term, proof that its `dpValExpr` value
      `= .nil`). Solidify nodes consume by `equivSource` index; recognizer nodes
      by term (directly, or through a `(not …)` wrapper). -/
  litFacts : List (Nat × SExpr × Expr) := []
  /-- The bound CONDITIONAL hypotheses (the generic mirror's telescope):
      per defined fn, its totality hypothesis; and — when the development emitted
      a :TYPE-PRESCRIPTION — its lifted-corollary hypothesis (with the corollary
      term). The pinning step consumes these. -/
  totalHyps : List (String × Expr) := []
  tpHyps : List (String × SExpr × Expr) := []
  ih : Option Expr := none

def ReplayCtx.empty : ReplayCtx := {}

/-- Look up a pinned value fact for `t` in the context. -/
def ReplayCtx.val? (ctx : ReplayCtx) (t : SExpr) : Option (Expr × Expr) :=
  (ctx.vals.find? (fun (o, _, _) => o == t)).map fun (_, v, p) => (v, p)

/-- Look up a spine falsity fact by literal index / by term. -/
def ReplayCtx.litFact? (ctx : ReplayCtx) (idx : Nat) : Option (SExpr × Expr) :=
  (ctx.litFacts.find? (fun (i, _, _) => i == idx)).map fun (_, t, p) => (t, p)
def ReplayCtx.litFactByTerm? (ctx : ReplayCtx) (t : SExpr) : Option Expr :=
  (ctx.litFacts.find? (fun (_, lt, _) => lt == t)).map fun (_, _, p) => p

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

/-- DP-lift primitives (unary): ACL2 name → (Logic function, `callBuiltin` rfl lemma). -/
def dpUnary : List (String × Name × Name) :=
  [("not",      ``Logic.not,      ``callBuiltin_not),
   ("zp",       ``Logic.zp,       ``callBuiltin_zp),
   ("consp",    ``Logic.consp,    ``callBuiltin_consp),
   ("integerp", ``Logic.integerp, ``callBuiltin_integerp),
   ("acl2-numberp", ``Logic.acl2Numberp, ``callBuiltin_acl2_numberp),
   ("car",      ``Logic.car,      ``callBuiltin_car),
   ("cdr",      ``Logic.cdr,      ``callBuiltin_cdr)]

/-- DP-lift primitives (binary). -/
def dpBinary : List (String × Name × Name) :=
  [("equal",    ``Logic.equal,   ``callBuiltin_equal),
   ("<",        ``Logic.lt,      ``callBuiltin_lt),
   ("binary-+", ``Logic.plus,    ``callBuiltin_plus),
   ("binary-*", ``Logic.times,   ``callBuiltin_times),
   ("cons",     ``SExpr.cons,    ``callBuiltin_cons),
   ("implies",  ``Logic.implies, ``callBuiltin_implies),
   ("iff",      ``Logic.iff,     ``callBuiltin_iff)]

/-- Is this head a DP-lift special form or primitive? (Anything else with a symbol
    head is an OPAQUE user-fn application.) -/
def dpKnownHead (name : String) : Bool :=
  name == "quote" || name == "if" ||
  (dpUnary.lookup name).isSome || (dpBinary.lookup name).isSome


/-- Prove a term CONVERGES (v-fixed totality): `∃ N, ∃ v, ∀ f ≥ N, evalOpt f w env t = some v`
    — a single definite value (`evalOpt` is fuel-monotone), so callers can `obtain` the
    witness and feed any value-specific lemma. The value may be env-dependent (a free
    variable) but is still fixed across fuel. S2 handles a free variable (via `re_conv_var`,
    valid for ALL `env`) and a `(quote v)` constant; any other shape is an unimplemented
    frontier → `throwError` (the full convergence analyzer, G1, lands in a later stage). -/
partial def proveConv (cfg : ReplayConfig) (envExpr : Expr) (ctx : ReplayCtx) (t : SExpr) :
    MetaM Expr := do
  -- a pinned ctx fact covers any term (uniform with the value layer)
  if let some (_, p) := ctx.val? t then
    return ← mkAppM ``conv_vfix_of_val #[p]
  match t with
  | .atom (.symbol s) =>
    let hNotT ← proveIsNamedFalse s "t"
    mkAppM ``re_conv_var #[cfg.worldExpr, envExpr, reflectSymbol s, hNotT]
  | .cons (.atom (.symbol qs)) (.cons v .nil) =>
    if qs.name == "quote" then
      mkAppM ``re_conv_quote #[cfg.worldExpr, envExpr, reflectSExpr v]
    else match dpUnary.lookup qs.name with
      | some (fn, cbLemma) =>
        -- REGISTRY-GENERIC: any registered (total) builtin converges when its
        -- operand does; the registry equation supplies the value function.
        let ha ← proveConv cfg envExpr ctx v
        let hNs ← proveNotSpecial qs
        let hNo ← proveNoShadow cfg qs
        let hReg ← withLocalDeclD `av (mkConst ``SExpr) fun av => do
          mkLambdaFVars #[av] (← mkAppM cbLemma #[av])
        mkAppM ``re_conv_builtin1_reg
          #[cfg.worldExpr, envExpr, reflectSymbol qs, reflectSExpr v,
            mkConst fn, hNs, hNo, hReg, ha]
      | none => throwError "proveConv: unary {qs.name} not in the builtin registry \
                            (frontier): {repr t}"
  | .cons (.atom (.symbol bs)) (.cons a (.cons b .nil)) =>
    match dpBinary.lookup bs.name with
    | some (fn, cbLemma) =>
      let ha ← proveConv cfg envExpr ctx a
      let hb ← proveConv cfg envExpr ctx b
      let hNs ← proveNotSpecial bs
      let hNo ← proveNoShadow cfg bs
      let hReg ← withLocalDeclD `av (mkConst ``SExpr) fun av =>
        withLocalDeclD `bv (mkConst ``SExpr) fun bv => do
          mkLambdaFVars #[av, bv] (← mkAppM cbLemma #[av, bv])
      mkAppM ``re_conv_builtin2_reg
        #[cfg.worldExpr, envExpr, reflectSymbol bs, reflectSExpr a, reflectSExpr b,
          mkConst fn, hNs, hNo, hReg, ha, hb]
    | none => throwError "proveConv: binary {bs.name} not in the builtin registry \
                          (frontier): {repr t}"
  | .cons (.atom (.symbol fs)) (.cons c (.cons th (.cons e .nil))) =>
    if fs.name == "if" then
      let hc ← proveConv cfg envExpr ctx c
      let ht ← proveConv cfg envExpr ctx th
      let he ← proveConv cfg envExpr ctx e
      mkAppM ``re_conv_if
        #[cfg.worldExpr, envExpr, reflectSExpr c, reflectSExpr th, reflectSExpr e, hc, ht, he]
    else throwError "proveConv: ternary {fs.name} not supported (frontier): {repr t}"
  | _ => throwError "proveConv: no convergence rule for {repr t}"

/-- Prove a term converges in EVERY environment: `∀ env', ∃ N, ∃ v, ∀ f ≥ N,
    evalOpt f w env' t = some v`. Runs `proveConv` under a quantified `env'` and
    λ-abstracts. (Used for a definition body, whose convergence `re_unfold1_conv` needs
    at the `bindArgs` env.) -/
def proveConvAllEnv (cfg : ReplayConfig) (ctx : ReplayCtx) (t : SExpr) : MetaM Expr := do
  withLocalDeclD `env' (mkConst ``Env) fun env' => do
    let p ← proveConv cfg env' ctx t
    mkLambdaFVars #[env'] p

/-! ## Value characterization (shared by clause-spine replay and the DP lift)

The driver's value layer: every primitive-only term (with opaque user-fn
occurrences and scaffold-bound variables resolved through the `ReplayCtx`) has an
explicit `Logic`-primitive VALUE expression, and a proof that it evaluates to that
value. Moved here from `DischargeLeaf` and generalized with a variable override so
the induction scaffold can pin the controller's value (`xv`). -/

/-- Collect the MAXIMAL opaque subterms (user-fn applications) of a term, in
    first-occurrence order, deduplicated. -/
partial def collectOpaques (t : SExpr) : List SExpr :=
  go t |>.eraseDups
where
  go : SExpr → List SExpr
    | .cons (.atom (.symbol fs)) args =>
      if dpKnownHead fs.name then goSpine args
      else [.cons (.atom (.symbol fs)) args]
    | _ => []
  goSpine : SExpr → List SExpr
    | .cons a rest => go a ++ goSpine rest
    | _ => []

/-- The `Logic`-primitive VALUE of a term: opaque subterms via `opq` (term ↦ value
    expr), variables via `varVal`. -/
partial def dpValExpr (opq : List (SExpr × Expr)) (varVal : Symbol → MetaM Expr)
    (t : SExpr) : MetaM Expr := do
  if let some (_, v) := opq.find? (fun (o, _) => o == t) then return v
  match t with
  | .atom (.symbol s) => varVal s
  | .cons (.atom (.symbol fs)) (.cons a .nil) =>
    if fs.name == "quote" then return reflectSExpr a
    else match dpUnary.lookup fs.name with
      | some (fn, _) => return mkApp (mkConst fn) (← dpValExpr opq varVal a)
      | none => throwError "dpValExpr: unary {fs.name} is not a DP-lift primitive: {repr t}"
  | .cons (.atom (.symbol fs)) (.cons a (.cons b .nil)) =>
    match dpBinary.lookup fs.name with
    | some (fn, _) =>
      return mkApp2 (mkConst fn) (← dpValExpr opq varVal a) (← dpValExpr opq varVal b)
    | none => throwError "dpValExpr: binary {fs.name} is not a DP-lift primitive: {repr t}"
  | .cons (.atom (.symbol fs)) (.cons c (.cons th (.cons e .nil))) =>
    if fs.name == "if" then
      let vc ← dpValExpr opq varVal c
      let vt ← dpValExpr opq varVal th
      let ve ← dpValExpr opq varVal e
      mkAppM ``cond #[mkApp (mkConst ``Logic.toBool) vc, vt, ve]
    else throwError "dpValExpr: ternary {fs.name} is not a DP-lift primitive: {repr t}"
  | _ => throwError "dpValExpr: unsupported term shape: {repr t}"

/-- A clause variable's default concrete value: `(env.get? s).getD nil`. -/
def dpConcVar (envExpr : Expr) (s : Symbol) : MetaM Expr := do
  mkAppM ``Option.getD
    #[← mkAppM ``Env.get? #[envExpr, reflectSymbol s], mkConst ``SExpr.nil]

/-- Value-characterized convergence of a term:
    `∃N ∀f≥N, evalOpt f w env t = some (dpValExpr concrete t)`. Opaque subterms use
    their convergence proofs (`opqP`); variables use `varP` when bound (the
    scaffold's controller) else `re_val_var`. -/
partial def dpValProof (cfg : ReplayConfig) (envExpr : Expr)
    (opq : List (SExpr × Expr)) (opqP : List (SExpr × Expr))
    (varP : Symbol → Option (Expr × Expr) := fun _ => none)
    (t : SExpr) : MetaM Expr := do
  if let some (_, h) := opqP.find? (fun (o, _) => o == t) then return h
  match t with
  | .atom (.symbol s) =>
    match varP s with
    | some (_, h) => return h
    | none =>
      let hNotT ← proveIsNamedFalse s "t"
      mkAppM ``re_val_var #[cfg.worldExpr, envExpr, reflectSymbol s, hNotT]
  | .cons (.atom (.symbol fs)) (.cons a .nil) =>
    if fs.name == "quote" then
      mkAppM ``re_val_quote #[cfg.worldExpr, envExpr, reflectSExpr a]
    else match dpUnary.lookup fs.name with
      | some (fn, cbLemma) =>
        let pa ← dpValProof cfg envExpr opq opqP varP a
        let va ← dpValExpr opq (dpVarVal envExpr varP) a
        let rv := mkApp (mkConst fn) va
        let hNs ← proveNotSpecial fs
        let hNo ← proveNoShadow cfg fs
        let hr ← mkAppM cbLemma #[va]
        mkAppM ``conv_builtin1
          #[cfg.worldExpr, envExpr, reflectSymbol fs, reflectSExpr a, va, rv, hNs, hNo, pa, hr]
      | none => throwError "dpValProof: unary {fs.name} is not a DP-lift primitive"
  | .cons (.atom (.symbol fs)) (.cons a (.cons b .nil)) =>
    match dpBinary.lookup fs.name with
    | some (fn, cbLemma) =>
      let pa ← dpValProof cfg envExpr opq opqP varP a
      let pb ← dpValProof cfg envExpr opq opqP varP b
      let va ← dpValExpr opq (dpVarVal envExpr varP) a
      let vb ← dpValExpr opq (dpVarVal envExpr varP) b
      let rv := mkApp2 (mkConst fn) va vb
      let hNs ← proveNotSpecial fs
      let hNo ← proveNoShadow cfg fs
      let hr ← mkAppM cbLemma #[va, vb]
      mkAppM ``conv_builtin2
        #[cfg.worldExpr, envExpr, reflectSymbol fs, reflectSExpr a, reflectSExpr b,
          va, vb, rv, hNs, hNo, pa, pb, hr]
    | none =>
      if fs.name == "if" then throwError "dpValProof: malformed if (2 args): {repr t}"
      else throwError "dpValProof: binary {fs.name} is not a DP-lift primitive"
  | .cons (.atom (.symbol fs)) (.cons c (.cons th (.cons e .nil))) =>
    if fs.name == "if" then
      let pc ← dpValProof cfg envExpr opq opqP varP c
      let pt ← dpValProof cfg envExpr opq opqP varP th
      let pe ← dpValProof cfg envExpr opq opqP varP e
      let vc ← dpValExpr opq (dpVarVal envExpr varP) c
      let vt ← dpValExpr opq (dpVarVal envExpr varP) th
      let ve ← dpValExpr opq (dpVarVal envExpr varP) e
      mkAppM ``re_val_if
        #[cfg.worldExpr, envExpr, reflectSExpr c, reflectSExpr th, reflectSExpr e,
          vc, vt, ve, pc, pt, pe]
    else throwError "dpValProof: ternary {fs.name} is not a DP-lift primitive"
  | _ => throwError "dpValProof: unsupported term shape: {repr t}"
where
  /-- Variable values consistent with `varP` (fall back to the env lookup). -/
  dpVarVal (envExpr : Expr) (varP : Symbol → Option (Expr × Expr)) (s : Symbol) :
      MetaM Expr :=
    match varP s with
    | some (v, _) => pure v
    | none => dpConcVar envExpr s

/-- Ctx-driven value/proof for a term: ctx.vals as the opaque maps, ctx.varVals as
    the variable override. -/
def ctxValExpr (cfg : ReplayConfig) (ctx : ReplayCtx) (t : SExpr) : MetaM Expr :=
  dpValExpr (ctx.vals.map fun (o, v, _) => (o, v))
    (fun s => match ctx.varVals.find? (fun (v, _, _) => v == s) with
      | some (_, v, _) => pure v
      | none => dpConcVar cfg.envExpr s) t

def ctxValProof (cfg : ReplayConfig) (ctx : ReplayCtx) (t : SExpr) : MetaM Expr :=
  dpValProof cfg cfg.envExpr
    (ctx.vals.map fun (o, v, _) => (o, v))
    (ctx.vals.map fun (o, _, p) => (o, p))
    (fun s => (ctx.varVals.find? (fun (v, _, _) => v == s)).map fun (_, v, p) => (v, p))
    t


/-- N-ary definition info (the c3 generalization of `DefInfo`). -/
structure DefInfoN where
  formals : List Symbol
  body : SExpr
  defFact : Expr
  closedFact : Expr
  noLetFact : Expr

/-- Derive an n-ary defined function's facts on demand (kernel decision). -/
def deriveDefInfoN (cfg : ReplayConfig) (fn : Symbol) : MetaM DefInfoN := do
  match cfg.worldVal.defs.get? fn with
  | none => throwError "deriveDefInfoN: {fn.name} not defined in the world"
  | some (formals, body) =>
    let formalsE ← mkListLit (mkConst ``Symbol) (formals.map reflectSymbol)
    let bodyE := reflectSExpr body
    let someE ← mkAppM ``Option.some #[← mkAppM ``Prod.mk #[formalsE, bodyE]]
    let defFact ← proveByDecide (← mkEq (← mkDefsGet cfg fn) someE) s!"def {fn.name}"
    let fvE ← mkAppM ``ACL2.Replay.freeVars #[bodyE]
    let closedProp ← withLocalDeclD `s (mkConst ``ACL2.Symbol) fun sv => do
      let memFv ← mkAppM ``Membership.mem #[fvE, sv]
      let memFm ← mkAppM ``Membership.mem #[formalsE, sv]
      mkForallFVars #[sv] (← mkArrow memFv memFm)
    let closedFact ← proveByDecide closedProp s!"closed {fn.name}"
    let noLetFact ← proveByDecide
      (← mkEq (← mkAppM ``ACL2.Replay.NoLet #[bodyE]) (mkConst ``Bool.true)) s!"nolet {fn.name}"
    return { formals, body, defFact, closedFact, noLetFact }

/-- Destructure an int-atom value `Expr` (`SExpr.atom (Atom.number (Number.int k))`)
    into its `k`. Hard-fails on any other shape. -/
def intValExpr? (v : Expr) : MetaM Expr := do
  let v ← instantiateMVars v
  unless v.isAppOfArity ``SExpr.atom 1 do throwError "expected int-atom value, got {v}"
  let a := v.appArg!
  unless a.isAppOfArity ``Atom.number 1 do throwError "expected int-atom value, got {v}"
  let n := a.appArg!
  unless n.isAppOfArity ``Number.int 1 do throwError "expected int-atom value, got {v}"
  return n.appArg!

mutual

/-- Recognizer fact `∃N∀f≥N, eval term = some verdict` (verdict the node's recorded
    `(quote t)`/`(quote nil)` value). Sources, in order: a fact pinned in the ctx by
    the scaffold/spine (e.g. `(consp x)` under a case hypothesis); the
    `acl2-numberp`-of-pinned-int recipe (the TP bridge); a structurally-computing
    value (e.g. `consp (cons …) = t`, where the cast is definitional). -/
partial def replayRecognizer (cfg : ReplayConfig) (ctx : ReplayCtx)
    (term : SExpr) (verdict : SExpr) : MetaM Expr := do
  let verdictE := reflectSExpr verdict
  if let some (v, p) := ctx.val? term then
    unless ← isDefEq v verdictE do
      throwError "replayRecognizer: pinned value of {repr term} ≠ verdict {repr verdict}"
    return p
  -- spine falsity facts: the literal IS this recognizer (verdict nil), or wraps it
  -- in (not …) (the literal's falsity makes the recognizer non-nil → t, by its
  -- two-valued range).
  if let some hNil := ctx.litFactByTerm? term then
    unless verdict == SExpr.nil do
      throwError "replayRecognizer: spine says {repr term} is nil but verdict is {repr verdict}"
    let p ← ctxValProof cfg ctx term
    let v ← ctxValExpr cfg ctx term
    return ← mkAppM ``re_val_cast
      #[cfg.worldExpr, cfg.envExpr, reflectSExpr term, v, verdictE, p, hNil]
  let notTerm : SExpr :=
    .cons (.atom (.symbol { name := "not" })) (.cons term .nil)
  if let some hNil := ctx.litFactByTerm? notTerm then
    match term with
    | .cons (.atom (.symbol rs)) _ =>
      unless rs.name == "consp" && verdict == SExpr.t do
        throwError "replayRecognizer: not-literal elimination only for consp⇒t \
                    (got {rs.name} ⇒ {repr verdict}, frontier)"
      let v ← ctxValExpr cfg ctx term       -- Logic.consp xv
      unless v.isAppOfArity ``Logic.consp 1 do
        throwError "replayRecognizer: value of {repr term} is not (Logic.consp _)"
      let xv := v.appArg!
      let hne ← mkAppM ``logic_not_nil_ne #[v, hNil]
      let hT ← mkAppM ``logic_consp_ne_nil_t #[xv, hne]
      let p ← ctxValProof cfg ctx term
      return ← mkAppM ``re_val_cast
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr term, v, verdictE, p, hT]
    | _ => throwError "replayRecognizer: not-literal over a non-application"
  match term with
  | .cons (.atom (.symbol rs)) (.cons z .nil) =>
    if rs.name == "acl2-numberp" then
      let some (vz, pz) := ctx.val? z
        | throwError "replayRecognizer: acl2-numberp argument {repr z} has no pinned value"
      let k ← intValExpr? vz
      unless verdict == SExpr.t do
        throwError "replayRecognizer: acl2-numberp of a pinned int must have verdict t"
      let hNo ← proveNoShadow cfg { name := "acl2-numberp" }
      mkAppM ``re_acl2_numberp_int #[cfg.worldExpr, cfg.envExpr, reflectSExpr z, k, hNo, pz]
    else
      let p ← ctxValProof cfg ctx term
      let v ← ctxValExpr cfg ctx term
      unless ← isDefEq v verdictE do
        throwError "replayRecognizer: value of {repr term} does not reduce to {repr verdict}"
      let hv ← mkEqRefl verdictE
      mkAppM ``re_val_cast
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr term, v, verdictE, p, hv]
  | _ => throwError "replayRecognizer: not a recognizer application: {repr term}"

/-- The DEFINITION-node recipe, UNIFORM: unfold `(fn args) ⇒ substTerm formals args
    body`, then chain the node's children (recognizer / if-simplification / deeper
    rewrites) over the substituted body via the ordinary path-directed congruence
    machinery (`replayRewrites` at depth+1 — their `:PATH`s carry the boundary
    frame), checking the chain reaches the node's recorded rhs.

    The unfold's body-convergence side condition has two ordered evidence sources:
    the application's PINNED value (totality — required for recursive fns), else the
    ∀-env convergence analyzer (sufficient for non-recursive bodies: direct, builtin,
    or if-shaped). -/
partial def replayDefinition (cfg : ReplayConfig) (ctx : ReplayCtx) (n : ProofNode)
    (depth : Nat) : MetaM Expr := do
  let (lhs, rhs) := nodeLhsRhs n
  let .node _ _ _ children _ := n
  let .cons (.atom (.symbol fn)) argSpine := lhs
    | throwError "definition: lhs is not an application: {repr lhs}"
  let args := (argSpine.toList?).getD []
  let di ← deriveDefInfoN cfg fn
  unless di.formals.length == args.length do
    throwError "definition: {fn.name} arity {di.formals.length} ≠ {args.length} args"
  let hns ← proveNotSpecial fn
  -- the unfold: eval lhs = eval (substTerm formals args body), with the body
  -- convergence from the ordered evidence sources
  let unfold ←
    match ctx.val? lhs with
    | some (rv, papp) =>
      -- evidence 1: pinned application value (totality)
      let argVals ← args.mapM (ctxValExpr cfg ctx)
      let argConvs ← args.mapM (ctxValProof cfg ctx)
      match di.formals, args, argVals, argConvs with
      | [f1], [a1], [v1], [p1] =>
        let hbody ← mkAppM ``re_body_conv1
          #[cfg.worldExpr, cfg.envExpr, reflectSymbol fn, reflectSymbol f1,
            reflectSExpr di.body, reflectSExpr a1, v1, rv, hns, di.defFact, p1, papp]
        mkAppM ``evalOpt_unfold1_conv
          #[cfg.worldExpr, cfg.envExpr, reflectSymbol fn, reflectSymbol f1,
            reflectSExpr di.body, reflectSExpr a1, v1, rv, hns,
            di.defFact, di.closedFact, di.noLetFact, p1, hbody]
      | [f1, f2], [a1, a2], [v1, v2], [p1, p2] =>
        let hbody ← mkAppM ``re_body_conv2
          #[cfg.worldExpr, cfg.envExpr, reflectSymbol fn, reflectSymbol f1, reflectSymbol f2,
            reflectSExpr di.body, reflectSExpr a1, reflectSExpr a2, v1, v2, rv, hns,
            di.defFact, p1, p2, papp]
        mkAppM ``evalOpt_unfold2_conv
          #[cfg.worldExpr, cfg.envExpr, reflectSymbol fn, reflectSymbol f1, reflectSymbol f2,
            reflectSExpr di.body, reflectSExpr a1, reflectSExpr a2, v1, v2, rv, hns,
            di.defFact, di.closedFact, di.noLetFact, p1, p2, hbody]
      | _, _, _, _ => throwError "definition: only 1/2-arg unfolds supported (frontier)"
    | none =>
      -- evidence 2: the ∀-env convergence analyzer
      let hbodyAll ← proveConvAllEnv cfg ctx di.body
      match di.formals, args with
      | [f1], [a1] =>
        let harg ← proveConv cfg cfg.envExpr ctx a1
        mkAppM ``re_unfold1_conv
          #[cfg.worldExpr, cfg.envExpr, reflectSymbol fn, reflectSymbol f1,
            reflectSExpr di.body, reflectSExpr a1, hns,
            di.defFact, di.closedFact, di.noLetFact, harg, hbodyAll]
      | [f1, f2], [a1, a2] =>
        let h1 ← proveConv cfg cfg.envExpr ctx a1
        let h2 ← proveConv cfg cfg.envExpr ctx a2
        mkAppM ``re_unfold2_conv
          #[cfg.worldExpr, cfg.envExpr, reflectSymbol fn, reflectSymbol f1, reflectSymbol f2,
            reflectSExpr di.body, reflectSExpr a1, reflectSExpr a2, hns,
            di.defFact, di.closedFact, di.noLetFact, h1, h2, hbodyAll]
      | _, _ => throwError "definition: only 1/2-arg unfolds supported (frontier)"
  -- children chain over the substituted body (depth+1: their paths carry one more
  -- boundary frame), reaching the node's recorded rhs
  let substBody := ACL2.Replay.substTerm di.formals args di.body
  let (chainOpt, finalTerm) ← replayRewrites cfg ctx substBody children (depth + 1)
  unless finalTerm == rhs do
    throwError "definition: children chain reached {repr finalTerm}, node rhs is {repr rhs}"
  match chainOpt with
  | none => return unfold
  | some ch => mkAppM ``fuel_chain_eq #[unfold, ch]

/-- Replay one rewrite node to its eval-equality `∃N∀f≥N, eval lhs = eval rhs`, by
    applying that rune's recipe. (equal-self is the literal closer, handled in
    `replayLiteral`, not here.) `depth` = the number of unfold/rule boundaries
    above this node (relativizes child `:PATH`s). Unhandled runes hard-fail. -/
partial def replayNode (cfg : ReplayConfig) (ctx : ReplayCtx) (n : ProofNode)
    (depth : Nat := 0) : MetaM Expr := do
  let (rty, rname) := runeOf n
  let (lhs, rhs) := nodeLhsRhs n
  let .node _ _ _ children prov := n
  match rty, rname with
  | "rewriting-equivalence", _ =>
    -- SOLIDIFY: the rewrite `lhs ⇒ rhs` is justified by a clause hypothesis — the
    -- (post-rewrite) literal named by `equivSource`, whose falsity in the spine
    -- branch IS the equation. Value-level: the literal `(not (equal A B))` being
    -- nil gives `vA = vB`; the node's sides converge to those values.
    let some idx := prov.equivSource
      | throwError "solidify: node has no equivSource (unlinked rewriting-equivalence)"
    let some (litTerm, hNil) := ctx.litFact? idx
      | throwError "solidify: no spine fact for literal {idx} (clause context missing)"
    let .cons (.atom (.symbol notS))
        (.cons (.cons (.atom (.symbol eqS)) (.cons ta (.cons tb .nil))) .nil) := litTerm
      | throwError "solidify: source literal is not (not (equal A B)): {repr litTerm}"
    unless notS.name == "not" && eqS.name == "equal" do
      throwError "solidify: source literal heads {notS.name}/{eqS.name}"
    -- orientation: the node rewrites one side of the equation to the other
    let (flip : Bool) ←
      if lhs == tb && rhs == ta then pure true
      else if lhs == ta && rhs == tb then pure false
      else throwError "solidify: node sides {repr lhs} ⇒ {repr rhs} do not match the \
                       source equation ({repr ta} = {repr tb})"
    let va ← ctxValExpr cfg ctx ta
    let vb ← ctxValExpr cfg ctx tb
    -- hNil : Logic.not (Logic.equal va vb) = nil  (the spine built the literal's
    -- value with the same builder, so this is its exact type)
    let hEq ← mkAppM ``logic_not_equal_nil_eq #[va, vb, hNil]   -- va = vb
    let valueEq ← if flip then mkAppM ``Eq.symm #[hEq] else pure hEq
    let pl ← ctxValProof cfg ctx lhs
    let pr ← ctxValProof cfg ctx rhs
    mkAppM ``fuel_eq_of_conv #[pl, pr, valueEq]
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
  | "rewrite", "car-cons" =>
    -- `(car (cons a b)) ⇒ a`.
    match lhs with
    | .cons (.atom (.symbol carS))
        (.cons (.cons (.atom (.symbol consS)) (.cons a (.cons b .nil))) .nil) =>
      unless carS.name == "car" && consS.name == "cons" do
        throwError "car-cons: lhs head not (car (cons …)): {repr lhs}"
      unless rhs == a do
        throwError "car-cons: rhs {repr rhs} ≠ the cons's car operand {repr a}"
      let ha ← proveConv cfg cfg.envExpr ctx a
      let hb ← proveConv cfg cfg.envExpr ctx b
      let hNoCar ← proveNoShadow cfg { name := "car" }
      let hNoCons ← proveNoShadow cfg { name := "cons" }
      mkAppM ``re_car_cons_conv
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr a, reflectSExpr b, hNoCar, hNoCons, ha, hb]
    | _ => throwError "car-cons: lhs not (car (cons a b)): {repr lhs}"
  | "rewrite", "unicity-of-0" =>
    -- `(binary-+ '0 z) ⇒ z` via the REAL intermediate `(fix z)` (the def:fix child
    -- subtree is REPLAYED, not collapsed): (A) `(+ '0 z) ⇒ (fix z)` by both
    -- converging to z's pinned int value; (B) the child `(fix z) ⇒ z`.
    match lhs with
    | .cons (.atom (.symbol plusS)) (.cons q0 (.cons z .nil)) =>
      unless plusS.name == "binary-+" && rhs == z do
        throwError "unicity-of-0: unexpected shape {repr lhs} ⇒ {repr rhs}"
      let some (vz, pz) := ctx.val? z
        | throwError "unicity-of-0: {repr z} has no pinned value (need the TP int fact)"
      let k ← intValExpr? vz
      let some fixChild := children.find? (fun c => (runeOf c).1 == "definition")
        | throwError "unicity-of-0: missing the definition:fix child"
      let (_fixLhs, fixRhs) := nodeLhsRhs fixChild
      unless fixRhs == z do
        throwError "unicity-of-0: fix child rhs {repr fixRhs} ≠ {repr z}"
      let fixEq ← replayNode cfg ctx fixChild (depth + 1)
      let fixConv ← mkAppM ``fuel_conv_of_eq #[fixEq, pz]
      let hq0 ← ctxValProof cfg ctx q0
      let vq0 ← ctxValExpr cfg ctx q0
      let hNoPlus ← proveNoShadow cfg { name := "binary-+" }
      let hNsPlus ← proveNotSpecial { name := "binary-+" }
      let hr ← mkAppM ``callBuiltin_plus #[vq0, vz]
      let plusConvRaw ← mkAppM ``conv_builtin2
        #[cfg.worldExpr, cfg.envExpr, reflectSymbol { name := "binary-+" },
          reflectSExpr q0, reflectSExpr z, vq0, vz,
          mkApp2 (mkConst ``Logic.plus) vq0 vz, hNsPlus, hNoPlus, hq0, pz, hr]
      let hzero ← mkAppM ``logic_plus_zero_int #[k]
      let plusConv ← mkAppM ``re_val_cast
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr lhs,
          mkApp2 (mkConst ``Logic.plus) vq0 vz, vz, plusConvRaw, hzero]
      let stepA ← mkAppM ``fuel_eq_of_conv #[plusConv, fixConv, ← mkEqRefl vz]
      mkAppM ``fuel_chain_eq #[stepA, fixEq]
    | _ => throwError "unicity-of-0: lhs not (binary-+ '0 z): {repr lhs}"
  | "rewrite", "commutativity-of-+" =>
    -- `(+ a b) ⇒ (+ b a)`, then the node's children chain on the rule's rhs
    -- (their paths carry an `(RHS . …)` boundary frame — depth+1) to the recorded rhs.
    match lhs with
    | .cons (.atom (.symbol plusS)) (.cons a (.cons b .nil)) =>
      unless plusS.name == "binary-+" do
        throwError "commutativity-of-+: head {plusS.name}"
      let ha ← ctxValProof cfg ctx a
      let hb ← ctxValProof cfg ctx b
      let va ← ctxValExpr cfg ctx a
      let vb ← ctxValExpr cfg ctx b
      let hNoPlus ← proveNoShadow cfg { name := "binary-+" }
      let ruleEq ← mkAppM ``re_plus_comm
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr a, reflectSExpr b, va, vb, hNoPlus, ha, hb]
      let swapped : SExpr :=
        .cons (.atom (.symbol plusS)) (.cons b (.cons a .nil))
      let (chainOpt, finalTerm) ← replayRewrites cfg ctx swapped children (depth + 1)
      unless finalTerm == rhs do
        throwError "commutativity-of-+: children chain reached {repr finalTerm}, \
                    node rhs is {repr rhs}"
      match chainOpt with
      | none => return ruleEq
      | some ch => mkAppM ``fuel_chain_eq #[ruleEq, ch]
    | _ => throwError "commutativity-of-+: lhs not (binary-+ a b): {repr lhs}"
  | "rewrite", "commutativity-2-of-+" =>
    -- `(+ a (+ b c)) ⇒ (+ b (+ a c))`, then the children chain on the rule's rhs
    -- at depth+1 to the recorded rhs.
    match lhs with
    | .cons (.atom (.symbol plusS))
        (.cons a (.cons (.cons (.atom (.symbol plusS2)) (.cons b (.cons c .nil))) .nil)) =>
      unless plusS.name == "binary-+" && plusS2.name == "binary-+" do
        throwError "commutativity-2-of-+: heads"
      let ha ← ctxValProof cfg ctx a
      let hb ← ctxValProof cfg ctx b
      let hc ← ctxValProof cfg ctx c
      let va ← ctxValExpr cfg ctx a
      let vb ← ctxValExpr cfg ctx b
      let vc ← ctxValExpr cfg ctx c
      let hNoPlus ← proveNoShadow cfg { name := "binary-+" }
      let ruleEq ← mkAppM ``re_plus_comm2
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr a, reflectSExpr b, reflectSExpr c,
          va, vb, vc, hNoPlus, ha, hb, hc]
      let swapped : SExpr :=
        .cons (.atom (.symbol plusS))
          (.cons b (.cons (.cons (.atom (.symbol plusS2)) (.cons a (.cons c .nil))) .nil))
      let (chainOpt, finalTerm) ← replayRewrites cfg ctx swapped children (depth + 1)
      unless finalTerm == rhs do
        throwError "commutativity-2-of-+: children chain reached {repr finalTerm}, \
                    node rhs is {repr rhs}"
      match chainOpt with
      | none => return ruleEq
      | some ch => mkAppM ``fuel_chain_eq #[ruleEq, ch]
    | _ => throwError "commutativity-2-of-+: lhs not (+ a (+ b c)): {repr lhs}"
  | "definition", _ => replayDefinition cfg ctx n depth
  | "fake-rune-for-anonymous-enabled-rule", _ =>
    -- recognizer node: term-eq form (eval lhs = eval rhs, rhs the quoted verdict).
    let verdictV := match rhs with
      | .cons (.atom (.symbol q)) (.cons v .nil) => if q.name == "quote" then v else rhs
      | v => v
    let fact ← replayRecognizer cfg ctx lhs verdictV
    let hq ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr verdictV]
    mkAppM ``fuel_eq_of_conv #[fact, hq, ← mkEqRefl (reflectSExpr verdictV)]
  | "if-simplification", _ =>
    -- `(if 'c thn els) ⇒ branch` — the test is already a quoted constant (a
    -- preceding recognizer rewrote it via if-test congruence).
    match lhs with
    | .cons (.atom (.symbol ifS)) (.cons c (.cons thn (.cons els .nil))) =>
      unless ifS.name == "if" do
        throwError "if-simplification: head {ifS.name}"
      let .cons (.atom (.symbol q)) (.cons cv .nil) := c
        | throwError "if-simplification: test is not a quoted constant: {repr c}"
      unless q.name == "quote" do
        throwError "if-simplification: test is not a quoted constant: {repr c}"
      let hc ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr cv]
      if cv == SExpr.nil then
        unless rhs == els do
          throwError "if-simplification: nil test but rhs ≠ else branch"
        let pEls ← ctxValProof cfg ctx els
        let vEls ← ctxValExpr cfg ctx els
        mkAppM ``re_if_false
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr c, reflectSExpr thn, reflectSExpr els,
            vEls, hc, pEls]
      else
        unless rhs == thn do
          throwError "if-simplification: non-nil test but rhs ≠ then branch"
        let pThn ← ctxValProof cfg ctx thn
        let vThn ← ctxValExpr cfg ctx thn
        let hcv ← proveByDecide
          (← mkEq (mkApp (mkConst ``Logic.toBool) (reflectSExpr cv)) (mkConst ``Bool.true))
          "toBool verdict = true"
        mkAppM ``re_if_true
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr c, reflectSExpr thn, reflectSExpr els,
            reflectSExpr cv, vThn, hc, hcv, pThn]
    | _ => throwError "if-simplification: lhs not an if: {repr lhs}"
  | _, _ =>
    throwError "replayNode: no rule for rune ({rty}, {rname}) — unimplemented frontier"

/-- Replay a chain of rewrite nodes, lifting each through the chain's start term by
    path-directed congruence (paths relativized to `depth`) and chaining. Returns
    the composed `∃N∀f≥N, eval start = eval finalTerm` (or `none` if the chain is
    empty) and the final term. -/
partial def replayRewrites (cfg : ReplayConfig) (ctx : ReplayCtx) (start : SExpr) :
    List ProofNode → (depth : Nat := 0) → (strip : List Nat := []) →
    MetaM (Option Expr × SExpr)
  | [], _, _ => return (none, start)
  | n :: rest, depth, strip => do
    let (lhs, rhs) := nodeLhsRhs n
    let nodeEq ← replayNode cfg ctx n depth
    let (lifted, newTerm) ←
      emitCongruence cfg.worldExpr cfg.envExpr start (nodePath n) lhs rhs nodeEq depth strip
    -- an if-simplification AT THE CHAIN ROOT selects a branch; ACL2's rewrite-if
    -- keeps the if on the gstack while rewriting inside that branch, so the
    -- remaining nodes' paths carry the branch frame — record it for stripping.
    let strip' ←
      if (runeOf n).1 == "if-simplification" && lhs == start then
        match lhs with
        | .cons _ (.cons _ (.cons thn (.cons els .nil))) =>
          if rhs == thn then pure (strip ++ [2])
          else if rhs == els then pure (strip ++ [3])
          else throwError "replayRewrites: root if-simplification rhs is neither branch"
        | _ => throwError "replayRewrites: root if-simplification lhs not a 3-arg if"
      else pure strip
    let (restProof, finalTerm) ← replayRewrites cfg ctx newTerm rest depth strip'
    match restProof with
    | none => return (some lifted, finalTerm)
    | some rp => return (some (← mkAppM ``fuel_chain_eq #[lifted, rp]), finalTerm)

end


/-- Replay a literal's rewrite chain at the LITERAL level. ACL2's rewriter works on
    the literal's ATOM (`rewrite-atm`): for a `:NOT-FLG T` literal `(not atm)` the
    node `:PATH`s are atom-relative, so chain on the atom and lift the composed
    eval-equality back through the `not` wrapper by unary congruence. Returns the
    literal-level chain (if any) and the final literal. -/
def replayLiteralChain (cfg : ReplayConfig) (ctx : ReplayCtx) (lp : LiteralProof)
    : MetaM (Option Expr × SExpr) := do
  if lp.notFlg then
    let .cons (.atom (.symbol notS)) (.cons atm .nil) := lp.literal
      | throwError "replayLiteralChain: notFlg literal is not (not atm): {repr lp.literal}"
    unless notS.name == "not" do
      throwError "replayLiteralChain: notFlg literal head {notS.name} ≠ not"
    let (chainOpt, finalAtom) ← replayRewrites cfg ctx atm lp.nodes 0
    let finalLit := SExpr.cons (.atom (.symbol notS)) (.cons finalAtom .nil)
    match chainOpt with
    | none => return (none, finalLit)
    | some ch =>
      let ns ← proveNotSpecial notS
      let lifted := mkAppN (mkConst ``evalOpt_congr_unary)
        #[cfg.worldExpr, cfg.envExpr, reflectSymbol notS, reflectSExpr atm,
          reflectSExpr finalAtom, ns, ch]
      return (some lifted, finalLit)
  else
    replayRewrites cfg ctx lp.literal lp.nodes 0

/-- Replay a literal that closes to `t`: chain its rewrite nodes, then close with the
    terminal `equal-self` node. Returns `∃N∀f≥N, eval lp.literal = some t`. -/
def replayLiteral (cfg : ReplayConfig) (ctx : ReplayCtx) (lp : LiteralProof) : MetaM Expr := do
  if lp.notFlg then
    throwError "replayLiteral: notFlg closing literal unsupported (frontier) — \
                {repr lp.literal}"
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

/-- The clause's literal items in order, with their 1-based indices, descending
    into case branches (a branch's items continue the same clause's literals). -/
partial def flattenLiterals : List ClauseItem → List (Nat × LiteralProof)
  | [] => []
  | .literal lp :: rest => (lp.index, lp) :: flattenLiterals rest
  | .step _ :: rest => flattenLiterals rest
  | .clausify _ :: rest => flattenLiterals rest
  | .branch _ items :: rest => flattenLiterals items ++ flattenLiterals rest

/-- ACL2's `disjoin` of a literal list: `(if l₁ 't (if l₂ 't … lₖ))`; a singleton
    is the literal itself; the empty clause is `'nil` (false). -/
def disjoinTerm : List SExpr → SExpr
  | [] => .cons (.atom (.symbol { name := "quote" })) (.cons .nil .nil)
  | [l] => l
  | l :: rest =>
    .cons (.atom (.symbol { name := "if" }))
      (.cons l (.cons quoteT (.cons (disjoinTerm rest) .nil)))

/-- Replay a clause as its LITERAL SPINE: prove
    `∃N∀f≥N, eval (disjoinTerm lits) = some t`. Each non-closing literal splits
    via `re_dp_if_split` — its truth closes the clause outright; its falsity
    descends with the value fact accumulated in `ctx.litFacts` (bridged across the
    literal's own rewrite chain to the post-rewrite form — what recognizer and
    solidify nodes downstream consume). The CLOSING literal (result `'t`) replays
    its chain under the accumulated context. The spine's own split IS the case
    hypothesis — no external case facts are needed for the clause itself. -/
partial def replayClauseSpine (cfg : ReplayConfig) (ctx : ReplayCtx)
    (lits : List (Nat × LiteralProof)) : MetaM Expr := do
  match lits with
  | [] => throwError "replayClauseSpine: ran out of literals with no closer"
  | (idx, lp) :: rest =>
    if lp.result == quoteT then
      -- the closer: its chain proves it `t`; any later literals are short-circuited.
      let pclose ← replayLiteral cfg ctx lp
      if rest.isEmpty then
        return pclose
      else
        -- `(if litᵢ 't rest)` with the test KNOWN `t`
        let restTerm := disjoinTerm (rest.map (·.2.literal))
        let hq ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr SExpr.t]
        let hcv ← proveByDecide
          (← mkEq (mkApp (mkConst ``Logic.toBool) (mkConst ``SExpr.t)) (mkConst ``Bool.true))
          "toBool t"
        let hIf ← mkAppM ``conv_if_true
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr lp.literal, reflectSExpr quoteT,
            reflectSExpr restTerm, mkConst ``SExpr.t, mkConst ``SExpr.t, pclose, hcv, hq]
        return hIf
    else
      -- a non-closing literal: split on its value
      let vLit ← ctxValExpr cfg ctx lp.literal
      let pLit ← ctxValProof cfg ctx lp.literal
      -- its rewrite chain (if any): literal ⇒ result, and the falsity fact bridges
      let (chainOpt, finalT) ← replayLiteralChain cfg ctx lp
      unless finalT == lp.result do
        throwError "replayClauseSpine: literal {idx} chain reached {repr finalT}, \
                    recorded result is {repr lp.result}"
      let restTerm := disjoinTerm (rest.map (·.2.literal))
      let neTy ← mkAppM ``Ne #[vLit, mkConst ``SExpr.nil]
      let hthen ← withLocalDeclD `h neTy fun h => do
        let hq ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr SExpr.t]
        let p ← mkAppM ``re_val_cast
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr quoteT, reflectSExpr SExpr.t,
            mkConst ``SExpr.t, hq, ← mkEqRefl (mkConst ``SExpr.t)]
        let _ := h
        mkLambdaFVars #[h] p
      let eqTy ← mkEq vLit (mkConst ``SExpr.nil)
      let helse ← withLocalDeclD `h eqTy fun h => do
        let (factTerm, factProof) ←
          match chainOpt with
          | none => pure (lp.literal, h)
          | some ch => do
            -- bridge the falsity to the post-rewrite literal
            let _vLit' ← ctxValExpr cfg ctx lp.result
            let pLit' ← ctxValProof cfg ctx lp.result
            let vEq ← mkAppM ``val_eq_of_eval_eq #[ch, pLit, pLit']
            pure (lp.result, ← mkAppM ``Eq.trans #[← mkAppM ``Eq.symm #[vEq], h])
        let ctx' := { ctx with litFacts := ctx.litFacts ++ [(idx, factTerm, factProof)] }
        let p ← replayClauseSpine cfg ctx' rest
        mkLambdaFVars #[h] p
      mkAppM ``re_dp_if_split
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr lp.literal, reflectSExpr quoteT,
          reflectSExpr restTerm, vLit, pLit, hthen, helse]

/-! ## Decision-procedure discharge leaves (c1 + c2) — the ratified carve-out

A clause ACL2 closed by a verdict-only decision procedure (tau / type-set
forward-chain) carries an emitted DISCHARGE NODE `(disjoin clause) ⇒ t` with no
internal step record — ACL2 itself has only the verdict — so the replay
discharges the leaf's precisely-stated obligation with a kernel-checked decision
procedure (CLAUDE.md, ratified 2026-06-09): lift the clause to the Logic
primitives, prove the DP FACT by the fixed simp/split_ifs/omega tactic, and fold
it back through the clause spine. Opaque user-fn subterms take their values from
totality/TP hypotheses. Two entry points:
- `replayDischargeLeaf` — the STANDALONE (harness) form: quantifies the opaque
  values + hypotheses into a telescope; with `assumeFact` an unclosable DP fact
  becomes a further bound hypothesis (conditional proof, no `sorryAx`).
- `replayDischargeNode` — the COMPOSED form used inside `replayClause`/
  preprocess chains: opaque values come from the ambient `ReplayCtx` PINS, TP
  facts from the bound TP hypotheses; an unclosable fact is a frontier error. -/

/-- Discharge-node origins (the verdict-only sites instrumented in ACL2's
    preprocess; see the emission plan). -/
def dischargeOrigins : List String :=
  ["preprocess/tau", "preprocess/tau-contradiction", "preprocess/type-set-fc",
   "preprocess/trivial-clause", "preprocess/built-in-clause"]

/-- Split a disjoined clause's if-spine `(if l₁ 't (if l₂ 't … lₖ))` into
    `([l₁ … l_{k-1}], lₖ)`. A non-spine term is a singleton clause `([], l)`. -/
partial def dpSpine : SExpr → List SExpr × SExpr
  | t@(.cons (.atom (.symbol fs)) (.cons c (.cons th (.cons e .nil)))) =>
    if fs.name == "if" && th == quoteT then
      let (lits, last) := dpSpine e
      (c :: lits, last)
    else ([], t)
  | t => ([], t)

/-- The fixed leaf-closing tactic of the carved-out decision procedure: `simp_all`
    with the Logic definitions, then `omega` on any arithmetic residue. -/
def dpLeafTactic : MetaM (TSyntax `tactic) :=
  `(tactic| first
      | (simp_all [Logic.zp, Logic.lt, Logic.plus, Logic.equal, Logic.not,
                   Logic.integerp, Logic.consp, Logic.toBool, Logic.toRat,
                   Logic.toInt, Logic.mkNumber, Logic.car, Logic.cdr,
                   Logic.implies, Logic.iff, beq_iff_eq, Bool.cond_eq_ite,
                   SExpr.t] <;>
          omega)
      | (simp_all [Logic.zp, Logic.lt, Logic.plus, Logic.equal, Logic.not,
                   Logic.integerp, Logic.consp, Logic.toBool, Logic.toRat,
                   Logic.toInt, Logic.mkNumber, Logic.car, Logic.cdr,
                   Logic.implies, Logic.iff, beq_iff_eq, Bool.cond_eq_ite,
                   SExpr.t] <;>
          (try split_ifs) <;> simp_all <;> try omega)
      | omega)

/-- Recursively case-split every `Atom`/`Number` hypothesis (the components a
    value's one-level `SExpr` split introduced), then return the leaves. -/
partial def dpSplitAtoms (g : MVarId) : MetaM (List MVarId) := do
  let target? ← g.withContext do
    (← getLCtx).findDeclM? fun d => do
      if d.isImplementationDetail then return none
      let ty ← instantiateMVars d.type
      if ty.isConstOf ``Atom || ty.isConstOf ``Number then return some d.fvarId
      else return none
  match target? with
  | none => return [g]
  | some fv =>
    let subs ← g.cases fv
    subs.toList.flatMapM (dpSplitAtoms ·.mvarId)

/-- Case one level of each quantified value (`SExpr`: nil/atom/cons — cons
    components are NOT recursed into; only the `dpv*`-named intro'd values are
    split), then split the atoms. -/
partial def dpSplitVars (g : MVarId) (n : Nat) : MetaM (List MVarId) := do
  if n == 0 then dpSplitAtoms g
  else
    let target? ← g.withContext do
      (← getLCtx).findDeclM? fun d => do
        if d.isImplementationDetail then return none
        let ty ← instantiateMVars d.type
        if ty.isConstOf ``SExpr && (d.userName.toString.startsWith "dpv") then
          return some d.fvarId
        else return none
    match target? with
    | none => throwError "dpSplitVars: expected {n} more values to split"
    | some fv =>
      let subs ← g.cases fv
      subs.toList.flatMapM (fun s => dpSplitVars s.mvarId (n - 1))

/-- Build the DP fact statement
    `∀ vars vops, tp₁ = t → … → v₁ = nil → … → v_{k-1} = nil → vₖ = t`
    — the discharged clause's truth over all variable AND opaque values, under the
    emitted type-prescription hypotheses. -/
def dpFactStmt (tests : List SExpr) (last : SExpr) (vars : List Symbol)
    (opaques : List SExpr) (tpCors : List SExpr) : MetaM Expr := do
  let total := vars.length + opaques.length
  let decls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
    (Array.range total).map fun i =>
      (Name.mkSimple s!"dpv{i}", .default, fun _ => pure (mkConst ``SExpr))
  withLocalDecls decls fun fvars => do
    let varMap := vars.zip fvars.toList
    let opqMap := opaques.zip (fvars.toList.drop vars.length)
    let absVal := dpValExpr opqMap fun s =>
      match varMap.find? (fun (v, _) => v == s) with
      | some (_, fv) => pure fv
      | none => throwError "dpFactStmt: unmapped variable {s.name}"
    let tpTys ← tpCors.mapM fun c => do mkEq (← absVal c) (mkConst ``SExpr.t)
    let hypTys ← tests.mapM fun t => do mkEq (← absVal t) (mkConst ``SExpr.nil)
    let conclTy ← do mkEq (← absVal last) (mkConst ``SExpr.t)
    let body ← (tpTys ++ hypTys).foldrM (fun h acc => mkArrow h acc) conclTy
    mkForallFVars fvars body

/-- PROVE the DP fact by the carved-out decision procedure: the fixed tactic on
    the unsplit goal first, else a one-level value split (policy-bounded) and the
    fixed tactic per leaf. Hard-fails if any case survives. -/
def proveDpFact (stmt : Expr) (total : Nat) : MetaM Expr := do
  let tac ← dpLeafTactic
  -- Each attempt uses a FRESH metavariable (a failed attempt may leave its mvar
  -- half-assigned).
  let direct? ←
    tryCatchRuntimeEx
      (try
        let mv ← mkFreshExprMVar stmt
        let (_, g) ← mv.mvarId!.intros
        let remaining ← Lean.Elab.runTactic g tac
        if remaining.1.isEmpty then pure (some (← instantiateMVars mv)) else pure none
      catch _ => pure none)
      (fun _ => pure none)
  if let some p := direct? then return p
  -- The split fallback is exponential in the quantified values (≈9 cases each).
  -- Past 3 values it is impractical whether or not the fact is true — fail fast
  -- with an honest frontier error instead of grinding (a fixed policy, not a
  -- heuristic: 9⁴ ≈ 6500 leaf goals × simp_all is not a viable check).
  if total > 3 then
    throwError "proveDpFact: direct tactic failed and {total} quantified values \
                exceed the split-fallback bound (3) — DP-fact frontier \
                (fact: {stmt})"
  let mv ← mkFreshExprMVar stmt
  let (_, g) ← mv.mvarId!.intros
  let leaves ← dpSplitVars g total
  for leaf in leaves do
    let remaining ← Lean.Elab.runTactic leaf tac
    unless remaining.1.isEmpty do
      throwError "proveDpFact: the DP leaf tactic left {remaining.1.length} goal(s) — \
                  the discharged clause's lift is not closable by simp+omega \
                  (clause fact: {stmt})"
  instantiateMVars mv

mutual
/-- Fold `re_dp_if_split` over the discharge clause's spine, feeding
    nil-hypotheses to the partially-applied DP fact. -/
partial def dischargeSpine (cfg : ReplayConfig) (opqMap opqP : List (SExpr × Expr))
    (t : SExpr) (fPartial : Expr) : MetaM Expr := do
  match t with
  | .cons (.atom (.symbol fs)) (.cons c (.cons th (.cons e .nil))) =>
    if fs.name == "if" && th == quoteT then
      let pc ← dpValProof cfg cfg.envExpr opqMap opqP (t := c)
      let vc ← dpValExpr opqMap (dpConcVar cfg.envExpr) c
      -- hthen : vc ≠ nil → eval 't ⇒ some SExpr.t
      let neTy ← mkAppM ``Ne #[vc, mkConst ``SExpr.nil]
      let hthen ← withLocalDeclD `h neTy fun h => do
        let pq ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr SExpr.t]
        -- cast the quoted value to SExpr.t (decidable equality, robust to symbol pkg)
        let hv ← proveByDecide
          (← mkEq (reflectSExpr SExpr.t) (mkConst ``SExpr.t)) "quote-t is SExpr.t"
        let p ← mkAppM ``re_val_cast
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr th, reflectSExpr SExpr.t,
            mkConst ``SExpr.t, pq, hv]
        mkLambdaFVars #[h] p
      -- helse : vc = nil → eval e ⇒ some SExpr.t   (descend, feeding the hyp to F)
      let fTy ← whnf (← inferType fPartial)
      let .forallE _ dom _ _ := fTy
        | throwError "dischargeSpine: DP fact arity mismatch at {repr c}"
      let helse ← withLocalDeclD `h dom fun h => do
        let p ← dischargeSpine cfg opqMap opqP e (mkApp fPartial h)
        mkLambdaFVars #[h] p
      mkAppM ``re_dp_if_split
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr c, reflectSExpr th, reflectSExpr e,
          vc, pc, hthen, helse]
    else dischargeClose cfg opqMap opqP t fPartial
  | _ => dischargeClose cfg opqMap opqP t fPartial

/-- Close the spine's last literal: cast its value-characterized convergence by
    the DP fact's conclusion `concVal(t) = SExpr.t`. -/
partial def dischargeClose (cfg : ReplayConfig) (opqMap opqP : List (SExpr × Expr))
    (t : SExpr) (fPartial : Expr) : MetaM Expr := do
  let pt ← dpValProof cfg cfg.envExpr opqMap opqP (t := t)
  let vt ← dpValExpr opqMap (dpConcVar cfg.envExpr) t
  mkAppM ``re_val_cast
    #[cfg.worldExpr, cfg.envExpr, reflectSExpr t, vt, mkConst ``SExpr.t, pt, fPartial]
end

/-- Replay a decision-procedure DISCHARGE LEAF standalone: prove the discharge
    node's claim `∃N ∀f≥N, evalOpt f w env (disjoin clause) = some t`,
    CONDITIONAL on, per opaque user-fn subterm: its convergence (totality) and —
    when the development carries one — its emitted type-prescription corollary.
    `tps` maps fn name ↦ corollary (from the parsed `:TYPE-PRESCRIPTION` events).
    Returns the (lambda-abstracted) proof and the list of assumed conditions.
    With `assumeFact`, an unclosable DP fact is NOT sorried: it becomes a further
    bound hypothesis (`hfact : <the fact>`) — the proof is CONDITIONAL, its type
    states the exact missing obligation, no `sorryAx` anywhere. -/
def replayDischargeLeaf (cfg : ReplayConfig) (clauseTerm : SExpr)
    (tps : List (String × SExpr) := []) (assumeFact : Bool := false) :
    MetaM (Expr × List String) := do
  let (tests, last) := dpSpine clauseTerm
  let lits := tests ++ [last]
  let vars := (lits.flatMap ACL2.Replay.freeVars).eraseDups
  let opaques := (lits.flatMap collectOpaques).eraseDups
  -- per-opaque: the instantiated TP corollary (formals ↦ the occurrence's actuals)
  let opCors : List (SExpr × Option SExpr) ← opaques.mapM fun op => do
    let .cons (.atom (.symbol fs)) argsSpine := op
      | throwError "replayDischargeLeaf: opaque is not an application: {repr op}"
    match tps.lookup fs.name with
    | none => return (op, none)
    | some cor =>
      let some (formals, _) := cfg.worldVal.defs.get? fs
        | return (op, none)  -- TP names a fn not in this world: skip the hypothesis
      let args := (argsSpine.toList?).getD []
      unless formals.length == args.length do
        throwError "replayDischargeLeaf: arity mismatch instantiating TP of {fs.name}"
      return (op, some (ACL2.Replay.substTerm formals args cor))
  let conds :=
    opaques.map (fun op => s!"total:{op}") ++
    (opCors.filterMap fun (op, c?) => c?.map fun _ =>
      s!"tp:{(op.toList?.getD []).head?.getD .nil}")
  -- quantify the opaque values, their convergence hypotheses, and TP hypotheses
  let vopDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
    (Array.range opaques.length).map fun i =>
      (Name.mkSimple s!"vop{i}", .default, fun _ => pure (mkConst ``SExpr))
  let (p, assumed) ← withLocalDecls vopDecls fun vops => do
    let opqMap := opaques.zip vops.toList
    let hConvDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
      (List.range opaques.length).toArray.map fun i =>
        (Name.mkSimple s!"hconv{i}", .default, fun _ => do
          mkEvalSomeExist cfg.worldExpr cfg.envExpr opaques[i]! vops[i]!)
    withLocalDecls hConvDecls fun hconvs => do
      let opqP := opaques.zip hconvs.toList
      -- TP hypothesis types: instantiated corollary lifted CONCRETELY, = t
      let tpCorsPresent := opCors.filterMap (·.2)
      let tpDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
        (List.range tpCorsPresent.length).toArray.map fun i =>
          (Name.mkSimple s!"htp{i}", .default, fun _ => do
            mkEq (← dpValExpr opqMap (dpConcVar cfg.envExpr) tpCorsPresent[i]!)
                 (mkConst ``SExpr.t))
      withLocalDecls tpDecls fun htps => do
        let stmt ← dpFactStmt tests last vars opaques tpCorsPresent
        let total := vars.length + opaques.length
        let fact? ←
          tryCatchRuntimeEx
            (try
              pure (some (← proveDpFact stmt total))
            catch e =>
              if assumeFact then pure none else throw e)
            (fun e =>
              if assumeFact then pure none else throw e)
        let concArgs ← vars.mapM (fun s => dpConcVar cfg.envExpr s)
        match fact? with
        | some fact =>
          -- instantiate the fact: concrete var values, opaque value fvars, TP hyps
          let factConc := mkAppN fact (concArgs.toArray ++ vops ++ htps)
          let prf ← dischargeSpine cfg opqMap opqP clauseTerm factConc
          return (← mkLambdaFVars (vops ++ hconvs ++ htps) prf, false)
        | none =>
          withLocalDeclD `hfact stmt fun hFact => do
            let factConc := mkAppN hFact (concArgs.toArray ++ vops ++ htps)
            let prf ← dischargeSpine cfg opqMap opqP clauseTerm factConc
            return (← mkLambdaFVars (vops ++ hconvs ++ htps ++ #[hFact]) prf, true)
  return (p, if assumed then conds ++ ["ASSUMED:dp-fact"] else conds)

/-- COMPOSE a verdict-only discharge node into a clause/preprocess replay: prove
    `∃N∀f≥N, eval (disjoin clause) = some t` under the AMBIENT `ReplayCtx` —
    opaque user-fn values come from the ctx PINS (placed there by
    `replayClause`'s uniform pinning), TP facts from the bound TP hypotheses.
    An unclosable DP fact is a frontier error here (the standalone harness
    reports such leaves ◌; conditional COMPOSITION needs condition threading —
    tracked in TODO). -/
def replayDischargeNode (cfg : ReplayConfig) (ctx : ReplayCtx) (clauseTerm : SExpr) :
    MetaM Expr := do
  let (tests, last) := dpSpine clauseTerm
  let lits := tests ++ [last]
  let vars := (lits.flatMap ACL2.Replay.freeVars).eraseDups
  let opaques := (lits.flatMap collectOpaques).eraseDups
  let pinned ← opaques.mapM fun op => do
    let some (v, p) := ctx.val? op
      | throwError "replayDischargeNode: opaque {repr op} has no pinned value \
                    (totality hypothesis missing? frontier)"
    pure (op, v, p)
  let opqMap := pinned.map fun (op, v, _) => (op, v)
  let opqP := pinned.map fun (op, _, p) => (op, p)
  -- TP facts at the pinned values, from the bound TP hypotheses
  let tpData ← opaques.filterMapM fun op => do
    let .cons (.atom (.symbol fs)) argsSpine := op
      | throwError "replayDischargeNode: opaque is not an application: {repr op}"
    match ctx.tpHyps.find? (fun (n, _, _) => n == fs.name) with
    | none => return none
    | some (_, cor, tpHyp) =>
      let some (formals, _) := cfg.worldVal.defs.get? fs | return none
      let args := (argsSpine.toList?).getD []
      unless formals.length == args.length do
        throwError "replayDischargeNode: arity mismatch instantiating TP of {fs.name}"
      let instCor := ACL2.Replay.substTerm formals args cor
      let some (v, conv) := ctx.val? op
        | throwError "replayDischargeNode: unpinned TP opaque {repr op}"
      let fact := mkAppN tpHyp ((#[cfg.envExpr] : Array Expr)
        ++ (args.map reflectSExpr).toArray ++ #[v, conv])
      return some (instCor, fact)
  let stmt ← dpFactStmt tests last vars opaques (tpData.map (·.1))
  let fact ← proveDpFact stmt (vars.length + opaques.length)
  let concArgs ← vars.mapM (dpConcVar cfg.envExpr)
  let factConc := mkAppN fact (concArgs.toArray ++ (opqMap.map (·.2)).toArray
    ++ (tpData.map (·.2)).toArray)
  dischargeSpine cfg opqMap opqP clauseTerm factConc

/-! ## Preprocess-chain replay (a clause discharged at PREPROCESS, formula → 't)

ACL2's preprocess (`final-implies/eval`, `preprocess/eval`, abbreviation
expansion, const-fold, equal-self) logs clause-level `:REWRITE-STEP`s with NO
`:PATH` — preprocess has no rewriter gstack. Each step's position is therefore
reconstructed DETERMINISTICALLY: the node's lhs must occur EXACTLY ONCE in the
current term; zero or multiple occurrences hard-fail (nothing is guessed — the
same inverse-discipline standard as clause-id lineage). -/

/-- All occurrences of `lhs` in `cur`, as congruence path-step descents.
    Quoted subterms are opaque (no descent). -/
partial def findOccurrences (cur lhs : SExpr) : List (List PathStep) :=
  let here : List (List PathStep) := if cur == lhs then [[]] else []
  let inside : List (List PathStep) :=
    match asApp cur with
    | some (fn, args) =>
      if fn.name == "quote" then []
      else
        (args.zipIdx).flatMap fun (a, i) =>
          (findOccurrences a lhs).map fun p =>
            ({ fn, arity := args.length, argIdx := i,
               siblings := (args.zipIdx).filterMap fun (b, j) =>
                 if j == i then none else some b } : PathStep) :: p
    | none => []
  here ++ inside

/-- Replay one PREPROCESS node to its eval-equality `∃N∀f≥N, eval lhs = eval rhs`.
    `executable-counterpart` steps are GROUND computations: ACL2 ran the
    executable counterpart; the kernel re-checks the SAME computation by
    reduction of `evalOpt` at a sufficient concrete fuel (found by running the
    evaluator), lifted by fuel monotonicity. Other runes use their ordinary
    node recipes. -/
def replayPreprocessNode (cfg : ReplayConfig) (ctx : ReplayCtx) (n : ProofNode) :
    MetaM Expr := do
  let (rty, _) := runeOf n
  let (lhs, rhs) := nodeLhsRhs n
  -- a verdict-only DISCHARGE node (keyed by ORIGIN, not rune): the carved-out
  -- decision-procedure replay, composed from the ambient ctx pins
  let .node _ _ _ _ prov := n
  if dischargeOrigins.contains prov.origin then
    unless rhs == quoteT do
      throwError "discharge node: rhs {repr rhs} ≠ (quote t)"
    let conv ← replayDischargeNode cfg ctx lhs
    let hq ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr SExpr.t]
    return ← mkAppM ``fuel_eq_of_conv #[conv, hq, ← mkEqRefl (reflectSExpr SExpr.t)]
  match rty with
  | "executable-counterpart" =>
    unless (ACL2.Replay.freeVars lhs).isEmpty do
      throwError "executable-counterpart: lhs {repr lhs} has free variables"
    let .cons (.atom (.symbol q)) (.cons v .nil) := rhs
      | throwError "executable-counterpart: rhs {repr rhs} is not a quoted constant"
    unless q.name == "quote" do
      throwError "executable-counterpart: rhs {repr rhs} is not a quoted constant"
    -- find a sufficient fuel by running the SAME evaluator the theorem is about
    -- (ground term: the env is never consulted, so any env works)
    let mut F := 8
    let mut v? : Option SExpr := none
    while v?.isNone && F ≤ 65536 do
      v? := ACL2.evalOpt F cfg.worldVal {} lhs
      if v?.isNone then F := F * 2
    let some vComputed := v?
      | throwError "executable-counterpart: {repr lhs} does not converge by fuel 65536"
    unless vComputed == v do
      throwError "executable-counterpart: evalOpt computes {repr vComputed}, \
                  the recorded result is {repr v} — evaluator/ACL2 divergence on {repr lhs}"
    let lhsApp := mkApp4 (mkConst ``evalOpt) (mkNatLit F) cfg.worldExpr cfg.envExpr
      (reflectSExpr lhs)
    let someV ← mkAppM ``Option.some #[reflectSExpr v]
    unless ← isDefEq lhsApp someV do
      throwError "executable-counterpart: evalOpt {F} … {repr lhs} does not REDUCE \
                  to {repr v} (env-dependence or reflected-world mismatch?)"
    let hAt ← mkExpectedTypeHint (← mkEqRefl someV) (← mkEq lhsApp someV)
    let convLhs ← mkAppM ``conv_of_eval_at
      #[mkNatLit F, cfg.worldExpr, cfg.envExpr, reflectSExpr lhs, reflectSExpr v, hAt]
    let hq ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr v]
    mkAppM ``fuel_eq_of_conv #[convLhs, hq, ← mkEqRefl (reflectSExpr v)]
  | "equal-self" =>
    let some X := asEqualSelf lhs
      | throwError "preprocess equal-self: lhs is not (equal X X): {repr lhs}"
    unless rhs == quoteT do
      throwError "preprocess equal-self: rhs {repr rhs} ≠ (quote t)"
    let hX ← proveConv cfg cfg.envExpr ctx X
    let hNoEqual ← proveNoShadow cfg { name := "equal" }
    let closeProof ← mkAppM ``re_equal_self
      #[cfg.worldExpr, cfg.envExpr, reflectSExpr X, hX, hNoEqual]
    let hq ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr SExpr.t]
    mkAppM ``fuel_eq_of_conv #[closeProof, hq, ← mkEqRefl (reflectSExpr SExpr.t)]
  | _ => replayNode cfg ctx n 0

/-- Replay a clause discharged by PREPROCESS: the clause-level step nodes chain
    the single-literal clause's formula to `(quote t)`. Returns
    `∃N∀f≥N, eval formula = some t`. -/
def replayPreprocessChain (cfg : ReplayConfig) (ctx : ReplayCtx)
    (formula : SExpr) (nodes : List ProofNode) : MetaM Expr := do
  let mut cur := formula
  let mut acc : Option Expr := none
  for n in nodes do
    let (lhs, rhs) := nodeLhsRhs n
    let nodeEq ← replayPreprocessNode cfg ctx n
    let path ← match findOccurrences cur lhs with
      | [p] => pure p
      | [] => throwError "replayPreprocessChain: node lhs {repr lhs} does not occur \
                          in the current term {repr cur}"
      | ps => throwError "replayPreprocessChain: node lhs {repr lhs} occurs \
                          {ps.length} times in {repr cur} — ambiguous position \
                          (needs :PATH emission at the preprocess site)"
    -- lift innermost-out (the same congruence fold as emitCongruence)
    let mut inner := nodeEq
    let mut curL := lhs
    let mut curR := rhs
    for st in path.reverse do
      inner ← applyStep cfg.worldExpr cfg.envExpr st curL curR inner
      curL := rebuild st.fn st.arity st.argIdx curL st.siblings
      curR := rebuild st.fn st.arity st.argIdx curR st.siblings
    unless curL == cur do
      throwError "replayPreprocessChain: reconstructed {repr curL} ≠ current {repr cur}"
    acc := some (← match acc with
      | none => pure inner
      | some a => mkAppM ``fuel_chain_eq #[a, inner])
    cur := curR
  unless cur == quoteT do
    throwError "replayPreprocessChain: chain ended at {repr cur}, expected (quote t)"
  let some chain := acc
    | throwError "replayPreprocessChain: no step nodes"
  let hq ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr SExpr.t]
  mkAppM ``fuel_conv_of_eq #[chain, hq]

/-! ## The c3 induction scaffold + the conditional-mirror harness

The WF-induction scaffold consumes the EMITTED justification (measure / rel /
controllers / per-case tests + IH substitutions — the measure-emission track's
output) and instantiates `acl2_induction_consp` (strong induction on
`SExpr.acl2Count` — the well-foundedness construction Lean owns; everything else
is read off the tree). Case children are SELF-CONTAINED clause proofs (the spine's
split is the case hypothesis); the scaffold only peels the case literals
(`re_extract_else`) and bridges the IH (`evalOpt_substTerm_subst1`).

Opaque user-fn values are PINNED from the bound totality hypotheses (`pinVal` —
choice-based, no Exists.elim plumbing), refined to int-atom shape when the fn's
emitted `:TYPE-PRESCRIPTION` corollary has the standard `(IF (INTEGERP …) … 'NIL)`
shape. The hypotheses themselves are machine-generated from the development
(`replayProofConditional`) — the c2 conditional-proof pattern: the obligations are
explicit in the returned proof's type, reported as conditions. -/

/-- Expr-level SExpr application `(fn a₁ … aₙ)` from argument `Expr`s. -/
def mkAppListExpr (fn : Symbol) (args : Array Expr) : Expr :=
  let spine := args.foldr (fun a acc => mkApp2 (mkConst ``SExpr.cons) a acc)
    (mkConst ``SExpr.nil)
  mkApp2 (mkConst ``SExpr.cons)
    (mkApp (mkConst ``SExpr.atom) (mkApp (mkConst ``Atom.symbol) (reflectSymbol fn)))
    spine

/-- `∃ N, ∃ v, ∀ f ≥ N, evalOpt f w e t = some v` with the term as an `Expr`. -/
def mkConvPropEx (w e tE : Expr) : MetaM Expr := do
  withLocalDeclD `N (mkConst ``Nat) fun nV => do
    let inner ← withLocalDeclD `v (mkConst ``SExpr) fun vV => do
      let body ← withLocalDeclD `f (mkConst ``Nat) fun fV => do
        let ge ← mkAppM ``GE.ge #[fV, nV]
        let lhs := mkAppN (mkConst ``evalOpt) #[fV, w, e, tE]
        let rhs := mkApp2 (mkConst ``Option.some [0]) (mkConst ``SExpr) vV
        mkForallFVars #[fV] (← mkArrow ge (← mkEq lhs rhs))
      mkAppM ``Exists #[← mkLambdaFVars #[vV] body]
    mkAppM ``Exists #[← mkLambdaFVars #[nV] inner]

/-- `∃ N, ∀ f ≥ N, evalOpt f w e t = some v` with term and value as `Expr`s. -/
def mkValConvPropEx (w e tE vE : Expr) : MetaM Expr := do
  withLocalDeclD `N (mkConst ``Nat) fun nV => do
    let body ← withLocalDeclD `f (mkConst ``Nat) fun fV => do
      let ge ← mkAppM ``GE.ge #[fV, nV]
      let lhs := mkAppN (mkConst ``evalOpt) #[fV, w, e, tE]
      let rhs := mkApp2 (mkConst ``Option.some [0]) (mkConst ``SExpr) vE
      mkForallFVars #[fV] (← mkArrow ge (← mkEq lhs rhs))
    mkAppM ``Exists #[← mkLambdaFVars #[nV] body]

/-- The totality-hypothesis TYPE for an n-ary defined fn:
    `∀ env' (a₁…aₙ : SExpr), conv a₁ → … → ∃N ∃v ∀f≥N, eval env' (fn a…) = some v`. -/
def mkTotalityHypType (cfg : ReplayConfig) (fn : Symbol) (arity : Nat) : MetaM Expr := do
  let _ := cfg
  withLocalDeclD `env' (mkConst ``ACL2.Env) fun envV => do
    let decls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
      (Array.range arity).map fun i =>
        (Name.mkSimple s!"a{i}", .default, fun _ => pure (mkConst ``SExpr))
    withLocalDecls decls fun argVs => do
      let appT := mkAppListExpr fn argVs
      let prems ← argVs.toList.mapM (fun a => mkConvPropEx cfg.worldExpr envV a)
      let concl ← mkConvPropEx cfg.worldExpr envV appT
      let body ← prems.foldrM (fun h acc => mkArrow h acc) concl
      mkForallFVars (#[envV] ++ argVs) body

/-- The TP-corollary hypothesis TYPE: `∀ env' args… (v : SExpr),
    (∃N∀f≥N, eval env' (fn args) = some v) → <corollary lifted, (fn formals) ↦ v> = t`.
    The lift hard-fails if the corollary mentions anything but the application
    (the supported corollary shape — frontier otherwise). -/
def mkTpHypType (cfg : ReplayConfig) (fn : Symbol) (formals : List Symbol)
    (cor : SExpr) : MetaM Expr := do
  withLocalDeclD `env' (mkConst ``ACL2.Env) fun envV => do
    let decls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
      (Array.range formals.length).map fun i =>
        (Name.mkSimple s!"a{i}", .default, fun _ => pure (mkConst ``SExpr))
    withLocalDecls decls fun argVs => do
      withLocalDeclD `v (mkConst ``SExpr) fun vV => do
        let appT := mkAppListExpr fn argVs
        let prem ← mkValConvPropEx cfg.worldExpr envV appT vV
        -- the corollary's application pattern: (fn formals…)
        let appPat : SExpr :=
          .cons (.atom (.symbol fn))
            ((formals.map (SExpr.atom ∘ Atom.symbol)).foldr SExpr.cons .nil)
        let lifted ← dpValExpr [(appPat, vV)]
          (fun s => throwError "mkTpHypType: corollary of {fn.name} has a free \
                                variable {s.name} outside the application (frontier)")
          cor
        let concl ← mkEq lifted (mkConst ``SExpr.t)
        mkForallFVars (#[envV] ++ argVs ++ #[vV]) (← mkArrow prem concl)

/-- PIN the value of every user-fn application occurring in `t` (bottom-up) from
    the bound totality hypotheses, refining to the int-atom shape when the fn's
    emitted TP corollary has the standard `(IF (INTEGERP app) … 'NIL)` shape. -/
partial def pinTermOpaques (cfg : ReplayConfig) (envExpr : Expr) (ctx : ReplayCtx)
    (t : SExpr) : MetaM ReplayCtx := do
  match t with
  | .cons (.atom (.symbol fs)) argSpine =>
    if fs.name == "quote" then return ctx
    let args := (argSpine.toList?).getD []
    let mut ctx := ctx
    for a in args do
      ctx ← pinTermOpaques cfg envExpr ctx a
    if (cfg.worldVal.defs.get? fs).isNone then return ctx
    if (ctx.val? t).isSome then return ctx
    -- PROVISIONING, not consumption: with no totality hypothesis bound (the
    -- unconditional harness) the value is simply not offered — a replay that
    -- NEEDS it hard-fails at the use site (`dpValExpr`), never silently.
    let some hyp := ctx.totalHyps.lookup fs.name
      | return ctx
    let argConvs ← args.mapM (fun a => proveConv cfg envExpr ctx a)
    let exConv := mkAppN hyp
      ((#[envExpr] : Array Expr) ++ (args.map reflectSExpr).toArray ++ argConvs.toArray)
    let value ← mkAppM ``pinVal #[exConv]
    let conv ← mkAppM ``pinVal_spec #[exConv]
    match ctx.tpHyps.find? (fun (n, _, _) => n == fs.name) with
    | some (_, cor, tpHyp) =>
      match cor with
      | .cons (.atom (.symbol ifS))
          (.cons (.cons (.atom (.symbol intS)) (.cons _ .nil))
            (.cons thenC (.cons _ .nil))) =>
        unless ifS.name == "if" && intS.name == "integerp" do
          -- unsupported corollary shape: pin unrefined
          return { ctx with vals := ctx.vals ++ [(t, value, conv)] }
        -- fact : lifted-corollary(value) = t
        let fact := mkAppN tpHyp
          ((#[envExpr] : Array Expr) ++ (args.map reflectSExpr).toArray ++ #[value, conv])
        -- X = the lifted then-branch at `value` (for the extraction lemma);
        -- the application pattern is the corollary's integerp argument
        let .cons _ (.cons (.cons _ (.cons appPat2 .nil)) _) := cor
          | throwError "pinTermOpaques: corollary destructure failed: {repr cor}"
        let xLift ← dpValExpr [(appPat2, value)]
          (fun s => throwError "pinTermOpaques: corollary free var {s.name}") thenC
        let hInt ← mkAppM ``tp_cond_integerp_t #[value, xLift, fact]
        let hkEx ← mkAppM ``logic_integerp_int #[value, hInt]
        let k ← mkAppM ``Exists.choose #[hkEx]
        let hvk ← mkAppM ``Exists.choose_spec #[hkEx]
        let value' := mkApp (mkConst ``SExpr.atom)
          (mkApp (mkConst ``Atom.number) (mkApp (mkConst ``Number.int) k))
        let conv' ← mkAppM ``re_val_cast
          #[cfg.worldExpr, envExpr, reflectSExpr t, value, value', conv, hvk]
        return { ctx with vals := ctx.vals ++ [(t, value', conv')] }
      | _ => return { ctx with vals := ctx.vals ++ [(t, value, conv)] }
    | none => return { ctx with vals := ctx.vals ++ [(t, value, conv)] }
  | _ => return ctx

/-- Every term mentioned in a clause subtree (input clauses, node lhs/rhs, literal
    results) — the pin-collection universe for a case child. -/
partial def clauseSubtreeTerms (cn : ClauseNode) : List SExpr :=
  let nodeTerms : ProofNode → List SExpr := fun n =>
    let rec go : ProofNode → List SExpr
      | .node _ lhs rhs cs _ => lhs :: rhs :: cs.flatMap go
    go n
  let itemTerms : ClauseItem → List SExpr := fun it =>
    let rec goI : ClauseItem → List SExpr
      | .literal lp => lp.literal :: lp.result :: lp.nodes.flatMap nodeTerms
      | .step n => nodeTerms n
      | .clausify info =>
          info.input :: (info.negClause ++ info.splits.flatMap (fun (l, c) => l :: c)
            ++ info.out.flatMap id)
      | .branch _ items => items.flatMap goI
    goI it
  cn.inputClause ++ cn.steps.flatMap (·.items.flatMap itemTerms)
    ++ cn.children.flatMap clauseSubtreeTerms


mutual

/-- Replay a clause node: prove `∃N∀f≥N, eval (disjoinTerm inputClause) = some t`
    (for a single-literal clause this IS the literal/formula statement).
    Induction nodes hard-fail (the scaffold lands next); a pushed clause delegates
    to its pool-root child when the clauses coincide. -/
partial def replayClause (cfg : ReplayConfig) (ctx : ReplayCtx) (cn : ClauseNode) : MetaM Expr := do
  if cn.induction.isSome then
    return ← replayInduction cfg ctx cn
  -- a push-clause node defers to its pool-root child (same clause)
  if cn.steps.any (fun s => s.processor.toLower == "push-clause") then
    match cn.children with
    | [child] =>
      unless child.inputClause == cn.inputClause do
        throwError "replayClause: pushed clause ≠ pool-root clause at {cn.idStr}"
      return ← replayClause cfg ctx child
    | _ => throwError "replayClause: push-clause with {cn.children.length} children at {cn.idStr}"
  -- pin every user-fn application in this clause's subtree from the totality/TP
  -- hypotheses (idempotent — already-pinned terms are skipped), so the value
  -- layer can lift opaque subterms under a quantified env
  let mut ctx := ctx
  for tm in (clauseSubtreeTerms cn).eraseDups do
    ctx ← pinTermOpaques cfg cfg.envExpr ctx tm
  let lits := flattenLiterals (cn.steps.flatMap (·.items))
  if lits.isEmpty then
    -- a clause discharged entirely at PREPROCESS: clause-level step nodes chain
    -- the formula to 't (no literal bracketing is emitted at preprocess sites)
    let stepNodes := (cn.steps.flatMap (·.items)).filterMap fun
      | .step n => some n | _ => none
    if stepNodes.isEmpty then
      throwError "replayClause: no literal or step items in clause {cn.idStr} \
                  (discharge composition frontier)"
    unless cn.children.isEmpty do
      throwError "replayClause: preprocess chain with child clauses at {cn.idStr} \
                  (clausify-split frontier)"
    let [formula] := cn.inputClause
      | throwError "replayClause: preprocess chain on a multi-literal clause at \
                    {cn.idStr} (frontier)"
    return ← replayPreprocessChain cfg ctx formula stepNodes
  replayClauseSpine cfg ctx lits


/-- Replay an INDUCTION pool-root from its EMITTED justification. v1 shape:
    measure `(acl2-count v)` under `o<`, one controller, step case `[(consp v)]`
    with IH `v := (cdr v)` (other variables identity), base `[(not (consp v))]`,
    single-literal pushed clause. Anything else hard-fails (frontier). -/
partial def replayInduction (cfg : ReplayConfig) (ctx : ReplayCtx) (cn : ClauseNode) :
    MetaM Expr := do
  let some ind := cn.induction | throwError "replayInduction: no induction"
  -- 1. validate the justification shape
  let .cons (.atom (.symbol acS)) (.cons (.atom (.symbol cvar)) .nil) := ind.measure
    | throwError "replayInduction: measure {repr ind.measure} is not (acl2-count v) (frontier)"
  unless acS.name == "acl2-count" do
    throwError "replayInduction: measure head {acS.name} (frontier)"
  let relOk := match ind.rel with
    | .atom (.symbol r) => r.name == "o<"
    | _ => false
  unless relOk do throwError "replayInduction: rel {repr ind.rel} ≠ o< (frontier)"
  unless ind.controllers == [cvar] do
    throwError "replayInduction: controllers {repr ind.controllers} ≠ [{cvar.name}] (frontier)"
  let cvarT : SExpr := .atom (.symbol cvar)
  let consT : SExpr := .cons (.atom (.symbol { name := "consp" })) (.cons cvarT .nil)
  let notConsT : SExpr := .cons (.atom (.symbol { name := "not" })) (.cons consT .nil)
  let cdrT : SExpr := .cons (.atom (.symbol { name := "cdr" })) (.cons cvarT .nil)
  let some stepCase := ind.cases.find? (·.tests == [consT])
    | throwError "replayInduction: no step case with tests [(consp {cvar.name})] (frontier)"
  unless ind.cases.any (·.tests == [notConsT]) do
    throwError "replayInduction: no base case with tests [(not (consp {cvar.name}))] (frontier)"
  let [alist] := stepCase.alists
    | throwError "replayInduction: step case has {stepCase.alists.length} IHs (frontier: exactly 1)"
  for (v, tm) in alist do
    if v == cvar then
      unless tm == cdrT do
        throwError "replayInduction: IH maps {v.name} to {repr tm}, expected (cdr {cvar.name})"
    else
      unless tm == .atom (.symbol v) do
        throwError "replayInduction: IH maps non-controller {v.name} to {repr tm} (frontier)"
  -- 2. the pushed clause (v1: single literal) and IH instantiation
  let [pushedLit] := cn.inputClause
    | throwError "replayInduction: multi-literal pushed clause (frontier)"
  let ihInst := ACL2.Replay.substTerm [cvar] [cdrT] pushedLit
  let notIhInst : SExpr := .cons (.atom (.symbol { name := "not" })) (.cons ihInst .nil)
  -- 3. link children by their first literal
  let some stepChild := cn.children.find? (·.inputClause.head? == some notConsT)
    | throwError "replayInduction: no step child (first literal (not (consp {cvar.name})))"
  let some baseChild := cn.children.find? (·.inputClause.head? == some consT)
    | throwError "replayInduction: no base child (first literal (consp {cvar.name}))"
  unless cn.children.length == 2 do
    throwError "replayInduction: {cn.children.length} children (frontier: exactly 2)"
  unless baseChild.inputClause == [consT, pushedLit] do
    throwError "replayInduction: base child clause {repr baseChild.inputClause} ≠ \
                [(consp v), pushed]"
  unless stepChild.inputClause == [notConsT, notIhInst, pushedLit] do
    throwError "replayInduction: step child clause {repr stepChild.inputClause} ≠ \
                [(not (consp v)), (not IH), pushed]"
  let w := cfg.worldExpr
  let pushedE := reflectSExpr pushedLit
  let tC := mkConst ``SExpr.t
  let nilC := mkConst ``SExpr.nil
  -- 4. P : SExpr → Prop
  let P ← withLocalDeclD `xv (mkConst ``SExpr) fun xvV => do
    let body ← withLocalDeclD `e (mkConst ``ACL2.Env) fun eV => do
      let hxTy ← mkValConvPropEx w eV (reflectSExpr cvarT) xvV
      let goal ← mkValConvPropEx w eV pushedE tC
      mkForallFVars #[eV] (← mkArrow hxTy goal)
    mkLambdaFVars #[xvV] body
  let conspOf := fun (v : Expr) => mkApp (mkConst ``Logic.consp) v
  -- 5. the BASE lambda: ∀ v, consp v = nil → P v
  let base ← withLocalDeclD `v (mkConst ``SExpr) fun vV => do
    let hcTy ← mkEq (conspOf vV) nilC
    let inner ← withLocalDeclD `hc hcTy fun hC => do
      let inner2 ← withLocalDeclD `e (mkConst ``ACL2.Env) fun eV => do
        let hxTy ← mkValConvPropEx w eV (reflectSExpr cvarT) vV
        let inner3 ← withLocalDeclD `hx hxTy fun hX => do
          let cfg' := { cfg with envExpr := eV }
          -- opaque pinning happens inside replayClause (under THIS case env)
          let ctxB : ReplayCtx :=
            { ctx with varVals := [(cvar, vV, hX)], vals := [], litFacts := [] }
          let pCl ← replayClause cfg' ctxB baseChild
          -- peel the case literal: eval (consp v-term) = some nil (cast by hc)
          let pTest ← ctxValProof cfg' ctxB consT
          let pTestNil ← mkAppM ``re_val_cast
            #[w, eV, reflectSExpr consT, conspOf vV, nilC, pTest, hC]
          let pPushed ← mkAppM ``re_extract_else
            #[w, eV, reflectSExpr consT, reflectSExpr quoteT, pushedE, tC, pCl, pTestNil]
          mkLambdaFVars #[hX] pPushed
        mkLambdaFVars #[eV] inner3
      mkLambdaFVars #[hC] inner2
    mkLambdaFVars #[vV] inner
  -- 6. the STEP lambda: ∀ v, consp v ≠ nil → P (cdr v) → P v
  let step ← withLocalDeclD `v (mkConst ``SExpr) fun vV => do
    let hneTy ← mkAppM ``Ne #[conspOf vV, nilC]
    let inner ← withLocalDeclD `hne hneTy fun hNe => do
      let ihTy := (mkApp P (mkApp (mkConst ``Logic.cdr) vV)).headBeta
      let inner2 ← withLocalDeclD `ihp ihTy fun ihV => do
        let inner3 ← withLocalDeclD `e (mkConst ``ACL2.Env) fun eV => do
          let hxTy ← mkValConvPropEx w eV (reflectSExpr cvarT) vV
          let inner4 ← withLocalDeclD `hx hxTy fun hX => do
            let cfg' := { cfg with envExpr := eV }
            -- opaque pinning happens inside replayClause (under THIS case env)
            let ctxS : ReplayCtx :=
              { ctx with varVals := [(cvar, vV, hX)], vals := [], litFacts := [] }
            let pCl ← replayClause cfg' ctxS stepChild
            -- peel literal 1: (not (consp v-term)) value = Logic.not t = nil
            let conspT ← mkAppM ``logic_consp_ne_nil_t #[vV, hNe]
            let pNotC ← ctxValProof cfg' ctxS notConsT
            let valEq ← mkAppM ``Eq.trans
              #[← mkAppM ``congrArg #[mkConst ``Logic.not, conspT],
                mkConst ``logic_not_t_nil]
            let pNotCnil ← mkAppM ``re_val_cast
              #[w, eV, reflectSExpr notConsT,
                mkApp (mkConst ``Logic.not) (conspOf vV), nilC, pNotC, valEq]
            let restTerm := disjoinTerm [notIhInst, pushedLit]
            let p2 ← mkAppM ``re_extract_else
              #[w, eV, reflectSExpr notConsT, reflectSExpr quoteT,
                reflectSExpr restTerm, tC, pCl, pNotCnil]
            -- the IH at e' = e.insert cvar (cdr v), bridged to e
            let cdrVal := mkApp (mkConst ``Logic.cdr) vV
            let e' ← mkAppM ``Env.insert #[eV, reflectSymbol cvar, cdrVal]
            let hx' ← mkAppM ``re_val_var_insert #[w, eV, reflectSymbol cvar, cdrVal]
            let pIH' := mkAppN ihV #[e', hx']
            let hCdrConv ← ctxValProof cfg' ctxS cdrT
            let hNoLet ← proveByDecide
              (← mkEq (← mkAppM ``ACL2.Replay.NoLet #[pushedE]) (mkConst ``Bool.true))
              "NoLet pushed"
            let pBridge ← mkAppM ``evalOpt_substTerm_subst1
              #[w, eV, reflectSymbol cvar, reflectSExpr cdrT, cdrVal, pushedE,
                hNoLet, hCdrConv]
            let pIHe ← mkAppM ``fuel_conv_of_eq #[pBridge, pIH']
            -- (not ihInst) ⇒ some nil
            let hNsNot ← proveNotSpecial { name := "not" }
            let hNoNot ← proveNoShadow cfg { name := "not" }
            let hrNot ← mkAppM ``callBuiltin_not #[tC]
            let pNotIH ← mkAppM ``conv_builtin1
              #[w, eV, reflectSymbol { name := "not" }, reflectSExpr ihInst, tC,
                mkApp (mkConst ``Logic.not) tC, hNsNot, hNoNot, pIHe, hrNot]
            let pNotIHnil ← mkAppM ``re_val_cast
              #[w, eV, reflectSExpr notIhInst, mkApp (mkConst ``Logic.not) tC, nilC,
                pNotIH, mkConst ``logic_not_t_nil]
            let p3 ← mkAppM ``re_extract_else
              #[w, eV, reflectSExpr notIhInst, reflectSExpr quoteT, pushedE, tC,
                p2, pNotIHnil]
            mkLambdaFVars #[hX] p3
          mkLambdaFVars #[eV] inner4
        mkLambdaFVars #[ihV] inner3
      mkLambdaFVars #[hNe] inner2
    mkLambdaFVars #[vV] inner
  -- 7. apply the induction and instantiate at the ambient env's controller value
  let indP ← mkAppM ``acl2_induction_consp #[P, base, step]
  let hNotT ← proveIsNamedFalse cvar "t"
  let hxv ← mkAppM ``re_val_var #[w, cfg.envExpr, reflectSymbol cvar, hNotT]
  let xv0 ← dpConcVar cfg.envExpr cvar
  return mkAppN indP #[xv0, cfg.envExpr, ← pure hxv] |>.headBeta

end

/-- Replay a whole theorem's proof tree to its mirror statement
    `∃N∀f≥N, eval cp.formula = some t`. -/
def replayProof (cfg : ReplayConfig) (cp : ClauseProof) : MetaM Expr := do
  match cp.root with
  | none => throwError "replayProof: theorem {cp.name} has no proof tree"
  | some root => replayClause cfg ReplayCtx.empty root


/-- The CONDITIONAL generic mirror: bind the machine-generated hypothesis
    telescope (per defined fn: totality; plus the lifted TP corollary when one was
    emitted), replay the theorem under it, and λ-abstract. Returns the proof and
    the condition descriptions (the c2 pattern — obligations explicit in the
    type, discharged later by termination emission / Driver Stage 5). -/
def replayProofConditional (cfg : ReplayConfig) (tps : List (String × SExpr))
    (cp : ClauseProof) : MetaM (Expr × List String) := do
  let fns := cfg.worldVal.defs.entries
  -- hypothesis declarations: totality for every defined fn, TP where emitted
  let totalDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
    (fns.map fun (s, formals, _) =>
      (Name.mkSimple s!"htotal_{s.name}", BinderInfo.default,
       fun (_ : Array Expr) => mkTotalityHypType cfg s formals.length)).toArray
  -- only LIFTABLE corollaries become hypotheses: every variable occurrence must be
  -- inside the (fn formals) application (the value-only hypothesis shape). An
  -- unliftable corollary (e.g. my-app's (EQUAL (MY-APP X Y) Y), which mentions Y
  -- bare) is SKIPPED — the fact is simply not offered, never mis-stated.
  let liftable := fun (fn : Symbol) (formals : List Symbol) (cor : SExpr) =>
    let appPat : SExpr :=
      .cons (.atom (.symbol fn))
        ((formals.map (SExpr.atom ∘ Atom.symbol)).foldr SExpr.cons .nil)
    let rec scrub : SExpr → SExpr := fun t =>
      if t == appPat then .nil
      else match t with
        | .cons a b => .cons (scrub a) (scrub b)
        | t => t
    (ACL2.Replay.freeVars (scrub cor)).isEmpty
  let tpFns := fns.filterMap fun (s, formals, _) =>
    (tps.lookup s.name).bind fun cor =>
      if liftable s formals cor then some (s, formals, cor) else none
  let tpDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
    (tpFns.map fun (s, formals, cor) =>
      (Name.mkSimple s!"htp_{s.name}", BinderInfo.default,
       fun (_ : Array Expr) => mkTpHypType cfg s formals cor)).toArray
  let condsAll :=
    fns.map (fun (s, _, _) => s!"total:{s.name}") ++
    tpFns.map (fun (s, _, _) => s!"tp:{s.name}")
  withLocalDecls totalDecls fun totalVs => do
    withLocalDecls tpDecls fun tpVs => do
      let ctx : ReplayCtx :=
        { totalHyps := (fns.map (fun (s, _, _) => s.name)).zip totalVs.toList,
          tpHyps := (tpFns.zip tpVs.toList).map fun ((s, _, cor), h) => (s.name, cor, h) }
      let some root := cp.root
        | throwError "replayProofConditional: theorem {cp.name} has no proof tree"
      let prf ← instantiateMVars (← replayClause cfg ctx root)
      -- bind only the hypotheses the replay ACTUALLY USED: an unconsumed offer must
      -- not weaken the statement (hypothesis types are mutually independent, so
      -- dropping unused ones is well-formed).
      let used := (condsAll.zip (totalVs ++ tpVs).toList).filter
        fun (_, v) => prf.containsFVar v.fvarId!
      let p ← mkLambdaFVars (used.map (·.2)).toArray prf
      return (p, used.map (·.1))


end ACL2.Replay.Driver
