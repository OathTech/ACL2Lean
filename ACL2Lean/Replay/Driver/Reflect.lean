/-
  Driver/Reflect — split from the monolithic Driver.lean (WP2 Stage 1,
  2026-07-17; see docs/plans/2026-07-18_driver-modular-refactor.md).

  Reflection kit, goal-type builders, and the G2 congruence-path emitter.
-/
import ACL2Lean.Replay.EvalLemmas
import ACL2Lean.Replay.DpLift
import ACL2Lean.Replay.ClausifyBridge
import ACL2Lean.Replay.GzRules
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
  -- canonical Symbol (BUG-013): the runtime value carries its canonicity,
  -- and the reflected literal re-proves it by kernel computation (defeq
  -- `rfl : true = true` against `canonSym pkg name = true`).
  mkApp3 (mkConst ``Symbol.mk) (mkStrLit s.package) (mkStrLit s.name)
    (mkApp2 (mkConst ``rfl [levelOne]) (mkConst ``Bool) (mkConst ``Bool.true))

def reflectNumber : Number → Expr
  | .int v => mkApp (mkConst ``Number.int) (reflectInt v)
  | .rational num den _ =>
    -- canonical Number (BUG-012): the runtime value carries its canonicity,
    -- and the reflected literal re-proves it by kernel computation —
    -- `canonRat <num> <den>` whnf-reduces to `true`, so a defeq-cast `rfl`
    -- (of type `true = true`) checks against `canonRat num den = true`.
    mkApp3 (mkConst ``Number.rational) (reflectInt num) (mkNatLit den)
      (mkApp2 (mkConst ``rfl [levelOne]) (mkConst ``Bool) (mkConst ``Bool.true))

def reflectAtom : Atom → Expr
  | .symbol s => mkApp (mkConst ``Atom.symbol) (reflectSymbol s)
  | .keyword k => mkApp (mkConst ``Atom.keyword) (mkStrLit k)
  | .string s => mkApp (mkConst ``Atom.string) (mkStrLit s)
  | .number n => mkApp (mkConst ``Atom.number) (reflectNumber n)
  | .char c => mkApp (mkConst ``Atom.char)
      (mkApp (mkConst ``UInt8.ofNat) (mkNatLit c.toNat))

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

/-- Tag marking a DELIBERATE frontier-class failure (fail-closed audit N1):
    "this is a genuine replay frontier — keep the hypothesis visible (D6)".
    Catch sites that demote failures to kept hypotheses classify by THIS tag,
    never by message-string prefix (a prefix is a shared namespace a real
    defect's message could accidentally inhabit — a masked bug would hide
    behind a `cond[…]` label on the scoreboard). -/
def frontierTag : Name := `ACL2Lean.replayFrontier

/-- Throw a TAGGED frontier-class error (see `frontierTag`). Use only where
    the failure is a known, named frontier whose fail-safe handling is the
    kept hypothesis; internal invariant violations stay `throwError` so they
    SURFACE. -/
def throwFrontier (msg : MessageData) : MetaM α := do
  throw <| Exception.error (← getRef) (.tagged frontierTag (← addMessageContext msg))

/-- Is this exception a deliberate frontier throw (tagged `frontierTag`)? -/
def isFrontierErr : Exception → Bool
  | .error _ md => md.hasTag (· == frontierTag)
  | _ => false

/-- Memo cache for `proveByDecide` (quality pass P1, measured 2026-07-21:
    3869 calls / ~3.4 s on HOW-MANY-APPEND alone — the same small Prop set
    recurs constantly). Keyed by the WHOLE Prop `Expr` (structural `==` with
    the pointer-eq fast path; the reflected world subterm is shared, so keys
    embedding different worlds never collide and lookups stay cheap).
    Only SUCCESSFUL proofs are cached — failures still hard-fail live. -/
initialize proveByDecideCache : IO.Ref (Array (Expr × Expr)) ←
  IO.mkRef #[]

/-- Prove a decidable proposition `p` by **kernel decision** — deterministic ground
    computation (evaluate the `Decidable` instance via `whnf`, then `of_decide_eq_true`).
    NOT heuristic: no simp set, no search. The single side-condition discharger the
    driver uses for all ground facts (non-special symbols, world non-shadowing, …).
    Hard-fails if `p` does not reduce to `true`. Successful results are memoized
    (`proveByDecideCache`). -/
def proveByDecide (p : Expr) (label : String) : MetaM Expr := do
  if let some (_, prf) := (← proveByDecideCache.get).find? (·.1 == p) then
    return prf
  let prf ← proveByDecideCore p label
  proveByDecideCache.modify (·.push (p, prf))
  return prf
where proveByDecideCore (p : Expr) (label : String) : MetaM Expr := do
  let inst ← synthInstance (mkApp (mkConst ``Decidable) p)
  let reduced ← withTransparency .all <| whnf (mkApp2 (mkConst ``decide) p inst)
  unless reduced == mkConst ``Bool.true do
    throwError "proveByDecide ({label}): {← ppExpr p} did not reduce to true"
  return mkApp3 (mkConst ``of_decide_eq_true) p inst
    (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))

/-- Prove `fn.isNamed "QUOTE" = false ∧ "if" = false ∧ "let" = false ∧ "let*" = false`
    — the `…_not_special` side-condition every congruence wants. -/
def proveNotSpecial (s : Symbol) : MetaM Expr := do
  let sExpr := reflectSymbol s
  let boolType := mkConst ``Bool
  let falseExpr := mkConst ``Bool.false
  let mkEqFalse (name : String) : Expr :=
    mkApp3 (mkConst ``Eq [1]) boolType
      (mkApp2 (mkConst ``Symbol.isNamed) sExpr (mkStrLit name)) falseExpr
  let mkAnd (a b : Expr) : Expr := mkApp2 (mkConst ``And) a b
  -- UPPERCASE literals: symbol NAMES are uppercase on the identity path
  -- (BUG-002 invariant) and the congruence lemmas' h_ns states them so; a
  -- lowercase literal here "proves" a different Prop that only coincides
  -- by defeq when both sides are false (audit 2026-07-19 N1)
  proveByDecide (mkAnd (mkEqFalse "QUOTE")
    (mkAnd (mkEqFalse "IF") (mkAnd (mkEqFalse "LET") (mkEqFalse "LET*")))) "not-special"

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
structure PathStep where
  fn : Symbol
  arity : Nat
  argIdx : Nat
  siblings : List SExpr   -- the OTHER args, in order, excluding `argIdx`
  /-- Set when the step's head is a translated `let` (S2 2026-07-24): the whole
      `(LAMBDA formals body)` term standing where a function symbol would.
      `rebuild`/`applyStep` DISPATCH on this field; `fn` then carries only the
      binder's `LAMBDA` symbol and is not used to name a function. -/
  lamHead : Option SExpr := none
  deriving Inhabited, BEq

/-- View an SExpr as `(fn arg₀ … argₖ)`: head must be a symbol. -/
def asApp (t : SExpr) : Option (Symbol × List SExpr) :=
  match t.toList? with
  | some (.atom (.symbol fn) :: args) => some (fn, args)
  | _ => none

/-- View an SExpr as a translated `let` `((LAMBDA formals body) actual₀ …)`:
    the head term, the binder's symbol, and the actuals. -/
def asLamApp (t : SExpr) : Option (SExpr × Symbol × List SExpr) :=
  match t with
  | .cons (.cons (.atom (.symbol lam)) (.cons formalsE (.cons lamBody .nil))) argsE =>
    -- reject a non-LAMBDA cons head (S2 audit, 2026-07-25): callers treat a
    -- `some` as a translated `let`; anything else must fall through to their
    -- non-application hard-fail
    if lam.isNamed "LAMBDA" then
      match argsE.toList? with
      | some args => some (.cons (.atom (.symbol lam)) (.cons formalsE (.cons lamBody .nil)), lam, args)
      | none => none
    else none
  | _ => none

/-- Destructure a `(LAMBDA formals body)` head term. -/
def asLamHead (t : SExpr) : Option (Symbol × SExpr × SExpr) :=
  match t with
  | .cons (.atom (.symbol lam)) (.cons formalsE (.cons lamBody .nil)) => some (lam, formalsE, lamBody)
  | _ => none

/-- Relativize a node's `:PATH` (path-emission Phase 1 — WINDOW-LOCAL
    paths): every path begins with exactly ONE descriptor frame — the
    literal-root frame for a top-level chain node, or the enclosing
    window's ENTRY frame for a windowed node (`(BODY . IF)`, `(2 . fn)`
    for an if-left branch, …) — regardless of nesting depth, because the
    fork emits frames only down to the INNERMOST window boundary. Drop it;
    the remainder navigates within the chain's start term.
    `pathStepsFromFrames`' final redex check is the fail-closed backstop
    for any residual misalignment. -/
def relativizeFrames (frames : List PathFrame) : List PathFrame :=
  frames.drop 1

/-- Navigate `descentFrames` (already relativized/stripped) from `term`,
    returning the path steps and the subterm reached — the redex-check-free
    core of `pathStepsFromFrames` (the if-finish recipe navigates to the
    node's position to learn the REAL redex, since the recorded lhs is
    display-folded). -/
def navigateFrames (term : SExpr) (descentFrames : List PathFrame)
    : Except String (List PathStep × SExpr) := do
  let mut cur := term
  let mut steps : List PathStep := []
  for fr in descentFrames do
    -- both descent frames say the same thing — "go to argument `idx`"; the
    -- `.argLam` variant additionally records that the TARGET is a translated
    -- `let`, which matters only for the NEXT frame (handled by `asLamApp`)
    let idx ← match fr with
      | .boundary k _ =>
        throw s!"pathStepsFromFrames: unexpected residual boundary frame {k.name} \
                (nesting deeper than the chain's depth)"
      | .arg idx _ => pure idx
      | .argLam idx _ => pure idx
    -- the head we descend FROM: a function symbol, or a lambda application
    let (lamHead?, fn, args) ←
      match asApp cur, asLamApp cur with
      | some (fn, args), _ => pure ((none : Option SExpr), fn, args)
      | none, some (head, lam, args) => pure (some head, lam, args)
      | none, none =>
        throw s!"pathStepsFromFrames: path descends into non-application {repr cur}"
    -- arity 3 is either the lazy `if` (branch congruences in `applyStep`,
    -- sound for the UNCONDITIONAL eval-equalities the chain carries) or a
    -- STRICT ternary user fn (generic argument congruence)
    if args.length > 3 then
      throw s!"pathStepsFromFrames: arity {args.length} application unsupported: {repr cur}"
    if idx < 1 || idx > args.length then
      throw s!"pathStepsFromFrames: arg index {idx} out of range for {repr cur}"
    let siblings := (args.zipIdx).filterMap (fun (a, i) => if i + 1 == idx then none else some a)
    steps := steps ++ [{ fn, arity := args.length, argIdx := idx - 1, siblings,
                         lamHead := lamHead? }]
    cur := args[idx - 1]!
  return (steps, cur)

def pathStepsFromFrames (term : SExpr) (descentFrames : List PathFrame) (lhs : SExpr)
    : Except String (List PathStep) := do
  let (steps, cur) ← navigateFrames term descentFrames
  unless cur == lhs do
    throw s!"pathStepsFromFrames: navigated to {repr cur}, expected redex {repr lhs} \
             (frames {repr descentFrames})"
  return steps

/-- Reconstruct the parent term placing `sub` at `argIdx`, siblings elsewhere.
    The head is the step's function symbol, or its LAMBDA term for a
    translated `let`. -/
def rebuild (st : PathStep) (sub : SExpr) : SExpr :=
  let args : List SExpr :=
    match st.arity, st.argIdx, st.siblings with
    | 1, 0, _ => [sub]
    | 2, 0, [s] => [sub, s]
    | 2, 1, [s] => [s, sub]
    | 3, 0, [t, e] => [sub, t, e]   -- if-test position
    | 3, 1, [c, e] => [c, sub, e]   -- if-then position (iff congruence path)
    | 3, 2, [c, t] => [c, t, sub]   -- if-else position (iff congruence path)
    | _, _, _ => panic! "rebuild: bad arity/argIdx"
  let head := match st.lamHead with
    | some h => h
    | none => .atom (.symbol st.fn)
  -- build (head args...) as a proper s-expression list
  .cons head (args.foldr SExpr.cons .nil)

/-- Apply one congruence step. `inner : ∃N∀f≥N, eval (sub) = eval (sub')`; returns
    `∃N∀f≥N, eval (fn … sub …) = eval (fn … sub' …)`. -/
def applyStep (w e : Expr) (st : PathStep) (sub sub' : SExpr) (inner : Expr) : MetaM Expr := do
  let fnE := reflectSymbol st.fn
  -- a translated `let`: congruence in the lambda application's ACTUALS
  if let some head := st.lamHead then
    let some (lam, formalsE, lamBody) := asLamHead head
      | throwError "applyStep: malformed LAMBDA head {repr head}"
    let lamE := reflectSymbol lam
    let fE := reflectSExpr formalsE
    let bE := reflectSExpr lamBody
    match st.arity, st.argIdx, st.siblings with
    | 1, 0, _ =>
      return mkAppN (mkConst ``evalOpt_congr_lam1)
        #[w, e, lamE, fE, bE, reflectSExpr sub, reflectSExpr sub', inner]
    | 2, 0, [b] =>
      return mkAppN (mkConst ``evalOpt_congr_lam2_left)
        #[w, e, lamE, fE, bE, reflectSExpr sub, reflectSExpr sub', reflectSExpr b, inner]
    | 2, 1, [a] =>
      return mkAppN (mkConst ``evalOpt_congr_lam2_right)
        #[w, e, lamE, fE, bE, reflectSExpr a, reflectSExpr sub, reflectSExpr sub', inner]
    | _, _, _ =>
      throwError "applyStep: LAMBDA binder of arity {st.arity} (arg {st.argIdx}) is a \
                  frontier — only 1- and 2-actual translated lets are emitted"
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
    -- the lazy if's TEST position; a non-IF ternary head takes the STRICT
    -- arg-1 congruence
    if st.fn.name == "IF" then
      return mkAppN (mkConst ``evalOpt_congr_if_test)
        #[w, e, reflectSExpr sub, reflectSExpr sub', reflectSExpr t, reflectSExpr el, inner]
    let ns ← proveNotSpecial st.fn
    return mkAppN (mkConst ``evalOpt_congr_ternary1)
      #[w, e, fnE, reflectSExpr sub, reflectSExpr sub', reflectSExpr t,
        reflectSExpr el, ns, inner]
  | 3, 1, [c, el] =>
    -- the if's THEN branch — sound under the UNCONDITIONAL eval-equality `inner`
    -- carries (if the test is false the branch is irrelevant; else t = t');
    -- a non-IF ternary head takes the STRICT arg-2 congruence
    if st.fn.name == "IF" then
      return mkAppN (mkConst ``evalOpt_congr_if_then)
        #[w, e, reflectSExpr c, reflectSExpr sub, reflectSExpr sub', reflectSExpr el, inner]
    let ns ← proveNotSpecial st.fn
    return mkAppN (mkConst ``evalOpt_congr_ternary2)
      #[w, e, fnE, reflectSExpr c, reflectSExpr sub, reflectSExpr sub',
        reflectSExpr el, ns, inner]
  | 3, 2, [c, t] =>
    -- the if's ELSE branch (the clause-disjunction TAIL) — sound under the
    -- unconditional eval-equality `inner`; a non-IF ternary head takes the
    -- STRICT arg-3 congruence
    if st.fn.name == "IF" then
      return mkAppN (mkConst ``evalOpt_congr_if_else)
        #[w, e, reflectSExpr c, reflectSExpr t, reflectSExpr sub, reflectSExpr sub', inner]
    let ns ← proveNotSpecial st.fn
    return mkAppN (mkConst ``evalOpt_congr_ternary3)
      #[w, e, fnE, reflectSExpr c, reflectSExpr t, reflectSExpr sub,
        reflectSExpr sub', ns, inner]
  | _, _, _ => throwError "applyStep: unsupported arity/argIdx {st.arity}/{st.argIdx}"

def emitCongruence (w e : Expr) (term : SExpr) (frames : List PathFrame)
    (lhs rhs : SExpr) (nodeProof : Expr)
    : MetaM (Expr × SExpr) := do
  let path ← ofExcept (pathStepsFromFrames term (relativizeFrames frames) lhs)
  -- Fold from the innermost path step outward.
  let mut inner := nodeProof
  let mut curL := lhs
  let mut curR := rhs
  for st in path.reverse do
    inner ← applyStep w e st curL curR inner
    curL := rebuild st curL
    curR := rebuild st curR
  unless curL == term do
    throwError "emitCongruence: reconstructed outer term {repr curL} ≠ input {repr term}"
  return (inner, curR)

/-- Chain a non-empty list of fuel-robust equalities `[a=b, b=c, …]` with `fuel_chain_eq`. -/
def chainEqs (proofs : List Expr) : MetaM Expr := do
  match proofs with
  | [] => throwError "chainEqs: empty"
  | p :: ps => ps.foldlM (fun acc q => mkAppM ``fuel_chain_eq #[acc, q]) p

/-- Structural diff-collapse (the destructor-elimination bridge's last leg):
    a fuel-robust eval-equality `eval cur = eval target` where `cur` and
    `target` differ EXACTLY at occurrences of `vT` (in `cur`) vs `uT` (in
    `target`), each occurrence discharged by `nodeEq : eval vT ≡ eval uT`
    lifted through positional congruence (`applyStep`, innermost-out; sibling
    positions taken from the RUNNING term so multiple diffs in one spine
    compose left-to-right). Any structural difference that is not exactly
    `vT` vs `uT` hard-fails. Returns `none` when the terms are identical. -/
partial def diffCollapse (w e : Expr) (vT uT : SExpr) (nodeEq : Expr) :
    (cur target : SExpr) → MetaM (Option Expr)
  | cur, target => do
    if cur == target then return none
    if cur == vT && target == uT then return some nodeEq
    let some (f, args) := asApp cur
      | throwError "diffCollapse: diff at non-application {repr cur} vs \
                    {repr target} is not the eliminated variable (frontier)"
    let some (g, brgs) := asApp target
      | throwError "diffCollapse: target diff {repr target} is not an \
                    application (frontier)"
    unless f == g && args.length == brgs.length do
      throwError "diffCollapse: head/arity mismatch {repr cur} vs {repr target} \
                  (frontier)"
    let mut curArgs := args.toArray
    let mut acc : Option Expr := none
    for i in [0:args.length] do
      let a := curArgs[i]!
      let b := brgs[i]!
      if a != b then
        let some inner ← diffCollapse w e vT uT nodeEq a b
          | throwError "diffCollapse: internal — unequal args produced no chain"
        let siblings := (curArgs.toList.zipIdx.filterMap fun (x, j) =>
          if j == i then none else some x)
        let st : PathStep := { fn := f, arity := args.length, argIdx := i, siblings }
        let lifted ← applyStep w e st a b inner
        acc ← match acc with
          | none => pure (some lifted)
          | some c => pure (some (← mkAppM ``fuel_chain_eq #[c, lifted]))
        curArgs := curArgs.set! i b
    return acc

end ACL2.Replay.Driver
