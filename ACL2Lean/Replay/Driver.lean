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
import ACL2Lean.Replay.DpLift
import ACL2Lean.Replay.ClausifyBridge
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

/-- Navigate `descentFrames` (already relativized/stripped) from `term`,
    returning the path steps and the subterm reached — the redex-check-free
    core of `pathStepsFromFrames` (the if-finish recipe navigates to the
    node's position to learn the REAL redex, since the recorded lhs is
    display-folded). -/
private def navigateFrames (term : SExpr) (descentFrames : List PathFrame)
    : Except String (List PathStep × SExpr) := do
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
          -- lazy-`if` descent: test, then, or else — `applyStep`'s branch
          -- congruences are sound for the UNCONDITIONAL eval-equalities the
          -- chain carries (a false test makes the branch irrelevant)
          unless fn.name == "if" do
            throw s!"pathStepsFromFrames: arity-3 congruence only for if \
                    (got {fn.name} arg {idx}): {repr cur}"
        else if args.length > 3 then
          throw s!"pathStepsFromFrames: arity {args.length} application unsupported: {repr cur}"
        if idx < 1 || idx > args.length then
          throw s!"pathStepsFromFrames: arg index {idx} out of range for {repr cur}"
        let siblings := (args.zipIdx).filterMap (fun (a, i) => if i + 1 == idx then none else some a)
        steps := steps ++ [{ fn, arity := args.length, argIdx := idx - 1, siblings }]
        cur := args[idx - 1]!
  return (steps, cur)

private def pathStepsFromFrames (term : SExpr) (descentFrames : List PathFrame) (lhs : SExpr)
    : Except String (List PathStep) := do
  let (steps, cur) ← navigateFrames term descentFrames
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
    | 3, 1, [c, e] => [c, sub, e]   -- if-then position (iff congruence path)
    | 3, 2, [c, t] => [c, t, sub]   -- if-else position (iff congruence path)
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
    -- the lazy if's TEST position
    unless st.fn.name == "if" do
      throwError "applyStep: arity-3 congruence only for if (got {st.fn.name})"
    return mkAppN (mkConst ``evalOpt_congr_if_test)
      #[w, e, reflectSExpr sub, reflectSExpr sub', reflectSExpr t, reflectSExpr el, inner]
  | 3, 1, [c, el] =>
    -- the if's THEN branch — sound under the UNCONDITIONAL eval-equality `inner`
    -- carries (if the test is false the branch is irrelevant; else t = t')
    unless st.fn.name == "if" do
      throwError "applyStep: arity-3 then-congruence only for if (got {st.fn.name})"
    return mkAppN (mkConst ``evalOpt_congr_if_then)
      #[w, e, reflectSExpr c, reflectSExpr sub, reflectSExpr sub', reflectSExpr el, inner]
  | 3, 2, [c, t] =>
    -- the if's ELSE branch (the clause-disjunction TAIL) — sound under the
    -- unconditional eval-equality `inner`
    unless st.fn.name == "if" do
      throwError "applyStep: arity-3 else-congruence only for if (got {st.fn.name})"
    return mkAppN (mkConst ``evalOpt_congr_if_else)
      #[w, e, reflectSExpr c, reflectSExpr t, reflectSExpr sub, reflectSExpr sub', inner]
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
def relativizeAndStrip (frames : List PathFrame) (depth : Nat) (strip : List Nat) :
    MetaM (List PathFrame) := do
  let mut rel ← ofExcept (relativizeFrames frames depth)
  for k in strip do
    match rel with
    | .arg idx _ :: restF =>
      unless idx == k do
        throwError "relativizeAndStrip: chain consumed branch frame {k}, but the \
                    node's path has arg {idx} there"
      rel := restF
    | _ =>
      throwError "relativizeAndStrip: chain consumed branch frame {k}, but the \
                  node's path has no arg frame there"
  return rel

def emitCongruence (w e : Expr) (term : SExpr) (frames : List PathFrame)
    (lhs rhs : SExpr) (nodeProof : Expr) (depth : Nat := 0) (strip : List Nat := [])
    : MetaM (Expr × SExpr) := do
  let rel ← relativizeAndStrip frames depth strip
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
  /-- ENCLOSING UNRESOLVED-IF test facts (the if-finish branch context,
      ACL2's assume-true-false): the test term, its value expr, the branch
      sign (`true` = then-branch, value `≠ nil`; `false` = else-branch, value
      `= nil`), and the value fact. Solidify `.branchTest` nodes consume
      these. -/
  branchFacts : List (SExpr × Expr × Bool × Expr) := []
  /-- ENCLOSING CLAUSIFY-BRANCH segment facts (the branch-split composer,
      W3): each entered branch's segment literal with the proof that its
      `dpValExpr` value `= .nil` (assumed false in the branch's continuation).
      Consumed by `litFactByTerm?` (recognizer/type-alist nodes) and by
      solidify `.segment` nodes (ACL2's `:CONTEXT-SUBST` hypotheses). -/
  segFacts : List (SExpr × Expr) := []
  /-- The bound CONDITIONAL hypotheses (the generic mirror's telescope):
      per defined fn, its totality hypothesis; and — when the development emitted
      a :TYPE-PRESCRIPTION — its lifted-corollary hypothesis (with the corollary
      term). The pinning step consumes these. -/
  totalHyps : List (String × Expr) := []
  tpHyps : List (String × SExpr × Expr) := []
  /-- Theorem-dependency hypotheses (`rule:<thm>`, the third telescope
      species): per emitted STORED rewrite rule, the spec and the bound
      hypothesis stating its mirror (`mkRuleHypType`). Consumed by the
      with-lemma node recipe; discharged lazily from the dependency's own
      replayed mirror (docs/plans/2026-07-05_theorem-dependency-hypotheses.md). -/
  ruleHyps : List (RuleSpec × Expr) := []
  ih : Option Expr := none

def ReplayCtx.empty : ReplayCtx := {}

/-- Look up a pinned value fact for `t` in the context. -/
def ReplayCtx.val? (ctx : ReplayCtx) (t : SExpr) : Option (Expr × Expr) :=
  (ctx.vals.find? (fun (o, _, _) => o == t)).map fun (_, v, p) => (v, p)

/-- Look up a spine falsity fact by literal index / by term. -/
def ReplayCtx.litFact? (ctx : ReplayCtx) (idx : Nat) : Option (SExpr × Expr) :=
  (ctx.litFacts.find? (fun (i, _, _) => i == idx)).map fun (_, t, p) => (t, p)
def ReplayCtx.litFactByTerm? (ctx : ReplayCtx) (t : SExpr) : Option Expr :=
  ((ctx.litFacts.find? (fun (_, lt, _) => lt == t)).map fun (_, _, p) => p).orElse
    fun _ => (ctx.segFacts.find? (fun (st, _) => st == t)).map (·.2)

/-- View `(equal X X)` as `X`. -/
def asEqualSelf : SExpr → Option SExpr
  | .cons (.atom (.symbol s)) (.cons x (.cons x' .nil)) =>
    if s.name == "equal" && x == x' then some x else none
  | _ => none

def runeOf : ProofNode → String × String | .node r _ _ _ _ => r
def nodeLhsRhs : ProofNode → SExpr × SExpr | .node _ lhs rhs _ _ => (lhs, rhs)
def nodePath : ProofNode → List PathFrame | .node _ _ _ _ p => p.path
def nodeOrigin : ProofNode → String | .node _ _ _ _ p => p.origin

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
   ("true-listp", ``Logic.trueListp, ``callBuiltin_true_listp),
   ("car",      ``Logic.car,      ``callBuiltin_car),
   ("cdr",      ``Logic.cdr,      ``callBuiltin_cdr),
   ("symbolp",  ``Logic.symbolp,  ``callBuiltin_symbolp),
   ("nfix",     ``Logic.nfix,     ``callBuiltin_nfix),
   ("len",      ``Logic.len,      ``callBuiltin_len)]

/-- DP-lift primitives (binary). -/
def dpBinary : List (String × Name × Name) :=
  [("equal",    ``Logic.equal,   ``callBuiltin_equal),
   ("<",        ``Logic.lt,      ``callBuiltin_lt),
   ("binary-+", ``Logic.plus,    ``callBuiltin_plus),
   ("binary-*", ``Logic.times,   ``callBuiltin_times),
   ("cons",     ``SExpr.cons,    ``callBuiltin_cons),
   ("implies",  ``Logic.implies, ``callBuiltin_implies),
   ("iff",      ``Logic.iff,     ``callBuiltin_iff)]

-- INVARIANT (load-bearing — the G3 audit's dpOpqKeyOk↔collectOpaques matrix):
-- `dpLiftHeads` must be EXACTLY the names of `dpUnary ++ dpBinary`. The meta
-- walkers (`dpValExpr`, `collectOpaques` via `dpKnownHead`) dispatch off the
-- registries, while the verified lift (`dpLiftF`, `dpOpqKeyOk`) dispatches off
-- `dpLiftHeads`; extending one side without the other silently desynchronizes
-- the lift premise from the collected opaque set. Set equality, both directions:
#guard dpLiftHeads.all (fun n => (dpUnary.lookup n).isSome || (dpBinary.lookup n).isSome)
#guard (dpUnary.map (·.1) ++ dpBinary.map (·.1)).all (dpLiftHeads.contains ·)

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

/-- The `(:DEFINITION implies)` GROUND-ZERO recipe: `(implies A B) ⇒
    (if A (if B 't 'nil) 't)` — ACL2's bootstrap defun unfold, proved against
    the BUILTIN semantics (`Logic.implies` + `logic_implies_cond`), because
    `evalOpt` models `implies` as a builtin; adding it to the world would
    shadow the `callBuiltin`/no-shadow facts. The recorded rhs must be EXACTLY
    the unfold body instance. -/
def replayImpliesDef (cfg : ReplayConfig) (ctx : ReplayCtx) (n : ProofNode) :
    MetaM Expr := do
  let (lhs, rhs) := nodeLhsRhs n
  let .node _ _ _ children _ := n
  unless children.isEmpty do
    throwError "definition:implies — children on the ground-zero unfold (frontier)"
  let .cons (.atom (.symbol impS)) (.cons A (.cons B .nil)) := lhs
    | throwError "definition:implies — lhs is not (implies A B): {repr lhs}"
  unless impS.name == "implies" do
    throwError "definition:implies — lhs head {impS.name}"
  let expectedRhs : SExpr :=
    .cons (.atom (.symbol { name := "if" }))
      (.cons A (.cons (.cons (.atom (.symbol { name := "if" }))
        (.cons B (.cons quoteT (.cons quoteNil .nil))))
        (.cons quoteT .nil)))
  unless rhs == expectedRhs do
    throwError "definition:implies — rhs {repr rhs} is not the unfold body instance"
  let vA ← ctxValExpr cfg ctx A
  let vB ← ctxValExpr cfg ctx B
  let pA ← ctxValProof cfg ctx A
  let pB ← ctxValProof cfg ctx B
  let hNs ← proveNotSpecial { name := "implies" }
  let hNo ← proveNoShadow cfg { name := "implies" }
  let hr ← mkAppM ``callBuiltin_implies #[vA, vB]
  let pL ← mkAppM ``conv_builtin2
    #[cfg.worldExpr, cfg.envExpr, reflectSymbol { name := "implies" },
      reflectSExpr A, reflectSExpr B, vA, vB,
      mkApp2 (mkConst ``Logic.implies) vA vB, hNs, hNo, pA, pB, hr]
  let pR ← ctxValProof cfg ctx rhs
  let valueEq ← mkAppM ``logic_implies_cond #[vA, vB]
  mkAppM ``fuel_eq_of_conv #[pL, pR, valueEq]

/-- Ground `executable-counterpart` computation: ACL2 ran the executable
    counterpart of a CLOSED term `lhs`, recording the result `v`. The kernel
    re-checks the SAME computation by reducing `evalOpt` at a concrete fuel
    (found by running the evaluator) and lifts by fuel monotonicity. Returns
    `∃N∀f≥N, eval lhs = some v`. Hard-fails if `lhs` is open or the evaluator
    diverges from ACL2's recorded result — this is the carve-out's faithful
    mirror (ACL2 records only a verdict; we re-run the same closed computation),
    NOT a license to compute through open terms. -/
def replayExecGround (cfg : ReplayConfig) (lhs v : SExpr) : MetaM Expr := do
  unless (ACL2.Replay.freeVars lhs).isEmpty do
    throwError "executable-counterpart: lhs {repr lhs} has free variables"
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
  mkAppM ``conv_of_eval_at
    #[mkNatLit F, cfg.worldExpr, cfg.envExpr, reflectSExpr lhs, reflectSExpr v, hAt]

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

/-- `∃ N, ∀ f ≥ N, evalOpt f w e a = evalOpt f w e b` (the chain Prop) with
    both terms as `Expr`s. -/
def mkEvalEqPropEx (w e aE bE : Expr) : MetaM Expr := do
  withLocalDeclD `N (mkConst ``Nat) fun nV => do
    let body ← withLocalDeclD `f (mkConst ``Nat) fun fV => do
      let ge ← mkAppM ``GE.ge #[fV, nV]
      let lhs := mkAppN (mkConst ``evalOpt) #[fV, w, e, aE]
      let rhs := mkAppN (mkConst ``evalOpt) #[fV, w, e, bE]
      mkForallFVars #[fV] (← mkArrow ge (← mkEq lhs rhs))
    mkAppM ``Exists #[← mkLambdaFVars #[nV] body]

/-- `∃N∀f≥N, eval (quote t) = some SExpr.t` (the constant, not the reflection). -/
def quoteTFact (cfg : ReplayConfig) : MetaM Expr := do
  let pq ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr SExpr.t]
  let hv ← proveByDecide
    (← mkEq (reflectSExpr SExpr.t) (mkConst ``SExpr.t)) "quote-t is SExpr.t"
  mkAppM ``re_val_cast
    #[cfg.worldExpr, cfg.envExpr, reflectSExpr quoteT, reflectSExpr SExpr.t,
      mkConst ``SExpr.t, pq, hv]

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

/-- ONE-WAY term match: extend `σ` so that `pat`σ `== t` (`pat`'s variables
    drawn from `vars`; quoted subterms match only literally). Deterministic —
    the pool-subsumption witness recompute (validated by the caller,
    recompute-and-check; never a proof search). -/
partial def termMatch (vars : List Symbol) (pat t : SExpr)
    (σ : List (Symbol × SExpr)) : Option (List (Symbol × SExpr)) :=
  match pat with
  | .atom (.symbol sy) =>
    if vars.contains sy then
      match σ.lookup sy with
      | some b => if b == t then some σ else none
      | none => some (σ ++ [(sy, t)])
    else if pat == t then some σ else none
  | .cons (.atom (.symbol q)) rest =>
    if q.name == "quote" then (if pat == t then some σ else none)
    else match t with
      | .cons t1 t2 =>
        (termMatch vars (.atom (.symbol q)) t1 σ).bind (termMatch vars rest t2 ·)
      | _ => none
  | .cons p1 p2 =>
    match t with
    | .cons t1 t2 => (termMatch vars p1 t1 σ).bind (termMatch vars p2 t2 ·)
    | _ => none
  | _ => if pat == t then some σ else none

/-- CLAUSE-subsumption witness: a σ under which every literal of `G` (the
    general clause) σ-instantiates to SOME literal of `C` — first witness in
    canonical order (G-literal order × C-literal order, backtracking). The
    caller VALIDATES the result against `C` (fail-closed). -/
partial def subsumeWitness (vars : List Symbol) (G C : List SExpr)
    (σ : List (Symbol × SExpr)) : Option (List (Symbol × SExpr)) :=
  match G with
  | [] => some σ
  | g :: rest =>
    C.findSome? fun c =>
      (termMatch vars g c σ).bind (subsumeWitness vars rest C ·)

/-- Fold per-entry proofs into a reflected list + its `∀ x ∈ list, P x`
    proof (`forall_mem_nil`/`forall_mem_cons` chain). -/
private def mkForallMemProof (entryTy P : Expr) (entries : List (Expr × Expr)) :
    MetaM (Expr × Expr) := do
  match entries with
  | [] =>
    let listE ← mkAppOptM ``List.nil #[some entryTy]
    let prf ← mkAppOptM ``List.forall_mem_nil #[some entryTy, some P]
    return (listE, prf)
  | (e, h) :: rest =>
    let (restE, restP) ← mkForallMemProof entryTy P rest
    let listE ← mkAppM ``List.cons #[e, restE]
    let andP ← mkAppM ``And.intro #[h, restP]
    let consIff ← mkAppOptM ``List.forall_mem_cons
      #[some entryTy, some P, some e, some restE]
    return (listE, ← mkAppM ``Iff.mpr #[consIff, andP])

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
  -- a non-EQUAL rule application is IFF/user-equivalence rewriting — it must
  -- route through the R-parameterized judgment, not the eval-equality recipes
  unless prov.equiv == "equal" do
    throwError "replayNode: rune ({rty}, {rname}) applied under equivalence \
                {prov.equiv} — R-parameterized recipe pending (G1 frontier)"
  match rty, rname with
  | "rewriting-equivalence", _ =>
    -- SOLIDIFY: the rewrite `lhs ⇒ rhs` is justified by a clause hypothesis — the
    -- (post-rewrite) literal named by `equivSource`, whose falsity in the spine
    -- branch IS the equation. Value-level: the literal `(not (equal A B))` being
    -- nil gives `vA = vB`; the node's sides converge to those values.
    let some src := prov.equivSource
      | throwError "solidify: node has no equivSource (unlinked rewriting-equivalence)"
    let idx ← match src with
      | .literal idx => pure idx
      | .branchTest =>
        -- the equivalence IS an enclosing unresolved-if's test, assumed TRUE
        -- in the then-branch the node's path descends through (ACL2's
        -- assume-true-false) — the if-finish recipe put the test's truth in
        -- scope as a branch fact.
        let some eqTerm := prov.equivTerm
          | throwError "solidify: branchTest node has no :EQUIV-TERM"
        let some (_, _, sign, hFact) :=
            ctx.branchFacts.find? (fun (t, _, _, _) => t == eqTerm)
          | throwError "solidify: no in-scope branch fact for test \
                        {repr eqTerm} (frontier)"
        unless sign do
          throwError "solidify: branch fact for {repr eqTerm} is the FALSE \
                      branch — equation unavailable (frontier)"
        let .cons (.atom (.symbol eqS)) (.cons ta (.cons tb .nil)) := eqTerm
          | throwError "solidify: branch test {repr eqTerm} is not (equal A B)"
        unless eqS.name == "equal" do
          throwError "solidify: branch test head {eqS.name} ≠ equal (frontier)"
        -- hFact : (Logic.equal va vb) ≠ nil — decode to va = vb
        let hEq ← mkAppM ``Logic.eq_of_equal_ne_nil #[hFact]
        let (flip : Bool) ←
          if lhs == tb && rhs == ta then pure true
          else if lhs == ta && rhs == tb then pure false
          else throwError "solidify: node sides {repr lhs} ⇒ {repr rhs} do not \
                           match the branch test ({repr ta} = {repr tb})"
        let valueEq ← if flip then mkAppM ``Eq.symm #[hEq] else pure hEq
        let pl ← ctxValProof cfg ctx lhs
        let pr ← ctxValProof cfg ctx rhs
        return ← mkAppM ``fuel_eq_of_conv #[pl, pr, valueEq]
      | .segment =>
        -- the equivalence IS an enclosing clausify-branch SEGMENT hypothesis
        -- (ACL2's :CONTEXT-SUBST): the segment literal `(not (equal A B))`,
        -- assumed false in the branch, gives the equation. The branch-split
        -- composer put its falsity in scope as a segFact; match the node's
        -- equiv term against it modulo `equal`'s argument order.
        let some eqTerm := prov.equivTerm
          | throwError "solidify: segment node has no :EQUIV-TERM"
        let .cons (.atom (.symbol eqS)) (.cons ta (.cons tb .nil)) := eqTerm
          | throwError "solidify: segment equiv {repr eqTerm} is not (equal A B)"
        unless eqS.name == "equal" do
          throwError "solidify: segment equiv head {eqS.name} ≠ equal (frontier)"
        let mkNotEq (x y : SExpr) : SExpr :=
          .cons (.atom (.symbol { name := "not" }))
            (.cons (.cons (.atom (.symbol { name := "equal" }))
              (.cons x (.cons y .nil))) .nil)
        -- the segment literal, in either argument order
        let (segLit, (flipArgs : Bool)) ←
          match ctx.segFacts.find? (fun (st, _) => st == mkNotEq ta tb) with
          | some f => pure (f, false)
          | none =>
            match ctx.segFacts.find? (fun (st, _) => st == mkNotEq tb ta) with
            | some f => pure (f, true)
            | none =>
              throwError "solidify: no in-scope segment fact for \
                          (not {repr eqTerm}) (frontier)"
        let (a', b') := if flipArgs then (tb, ta) else (ta, tb)
        let va ← ctxValExpr cfg ctx a'
        let vb ← ctxValExpr cfg ctx b'
        -- segLit.2 : Logic.not (Logic.equal va vb) = nil → va = vb
        let hEq0 ← mkAppM ``logic_not_equal_nil_eq #[va, vb, segLit.2]
        -- orient to (ta = tb), then to the node's lhs ⇒ rhs
        let hEq ← if flipArgs then mkAppM ``Eq.symm #[hEq0] else pure hEq0
        let (flip : Bool) ←
          if lhs == tb && rhs == ta then pure true
          else if lhs == ta && rhs == tb then pure false
          else throwError "solidify: node sides {repr lhs} ⇒ {repr rhs} do not \
                           match the segment equation ({repr ta} = {repr tb})"
        let valueEq ← if flip then mkAppM ``Eq.symm #[hEq] else pure hEq
        let pl ← ctxValProof cfg ctx lhs
        let pr ← ctxValProof cfg ctx rhs
        return ← mkAppM ``fuel_eq_of_conv #[pl, pr, valueEq]
    let some (litTerm0, hNil0) := ctx.litFact? idx
      | throwError "solidify: no spine fact for literal {idx} (clause context missing)"
    -- when the source literal's recorded form is NOT a bare (not (equal A B))
    -- — e.g. an implies-expanded IH whose equation was clausified out — the
    -- equation reaches the chain as a BRANCH SEGMENT fact: fall back to the
    -- segFacts by the node's equiv term (either argument order)
    let (litTerm, hNil) ←
      match litTerm0 with
      | .cons (.atom (.symbol ns))
          (.cons (.cons (.atom (.symbol es)) (.cons _ (.cons _ .nil))) .nil) =>
        if ns.name == "not" && es.name == "equal" then pure (litTerm0, hNil0)
        else pure (litTerm0, hNil0)
      | _ =>
        match prov.equivTerm with
        | some (.cons (.atom (.symbol eqS')) (.cons a' (.cons b' .nil))) => do
          unless eqS'.name == "equal" do
            throwError "solidify: source literal is not (not (equal A B)) and \
                        equiv {repr prov.equivTerm} is not an equal equation: \
                        {repr litTerm0}"
          let mk (x y : SExpr) : SExpr :=
            .cons (.atom (.symbol { name := "not" }))
              (.cons (.cons (.atom (.symbol { name := "equal" }))
                (.cons x (.cons y .nil))) .nil)
          match ctx.segFacts.find? (fun (st, _) => st == mk a' b') with
          | some (st, h) => pure (st, h)
          | none =>
            match ctx.segFacts.find? (fun (st, _) => st == mk b' a') with
            | some (st, h) => pure (st, h)
            | none =>
              throwError "solidify: source literal is not (not (equal A B)) \
                          and no segment fact matches {repr prov.equivTerm}: \
                          {repr litTerm0}"
        | _ =>
          throwError "solidify: source literal is not (not (equal A B)): \
                      {repr litTerm0}"
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
      let ha ← proveConv cfg cfg.envExpr ctx a
      let hb ← proveConv cfg cfg.envExpr ctx b
      let hNoCdr ← proveNoShadow cfg { name := "cdr" }
      let hNoCons ← proveNoShadow cfg { name := "cons" }
      let ruleEq ← mkAppM ``re_cdr_cons_conv
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr a, reflectSExpr b, hNoCdr, hNoCons, ha, hb]
      -- children may rewrite the rule's result further (see car-cons)
      let (chainOpt, finalTerm) ← replayRewrites cfg ctx b children (depth + 1)
      unless finalTerm == rhs do
        throwError "cdr-cons: children chain reached {repr finalTerm}, \
                    node rhs is {repr rhs}"
      match chainOpt with
      | none => return ruleEq
      | some ch => mkAppM ``fuel_chain_eq #[ruleEq, ch]
    | _ => throwError "cdr-cons: lhs not (cdr (cons a b)): {repr lhs}"
  | "rewrite", "car-cons" =>
    -- `(car (cons a b)) ⇒ a`.
    match lhs with
    | .cons (.atom (.symbol carS))
        (.cons (.cons (.atom (.symbol consS)) (.cons a (.cons b .nil))) .nil) =>
      unless carS.name == "car" && consS.name == "cons" do
        throwError "car-cons: lhs head not (car (cons …)): {repr lhs}"
      let ha ← proveConv cfg cfg.envExpr ctx a
      let hb ← proveConv cfg cfg.envExpr ctx b
      let hNoCar ← proveNoShadow cfg { name := "car" }
      let hNoCons ← proveNoShadow cfg { name := "cons" }
      let ruleEq ← mkAppM ``re_car_cons_conv
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr a, reflectSExpr b, hNoCar, hNoCons, ha, hb]
      -- the rule's result may be FURTHER rewritten by children (e.g. a
      -- solidify inside the rule's RHS — their paths carry the (RHS . _)
      -- boundary, consumed at depth+1); the node's rhs is the NET result.
      let (chainOpt, finalTerm) ← replayRewrites cfg ctx a children (depth + 1)
      unless finalTerm == rhs do
        throwError "car-cons: children chain reached {repr finalTerm}, \
                    node rhs is {repr rhs}"
      match chainOpt with
      | none => return ruleEq
      | some ch => mkAppM ``fuel_chain_eq #[ruleEq, ch]
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
  | "definition", dname =>
    -- `implies` is an evalOpt BUILTIN modeled by `callBuiltin`, not a world
    -- definition — its :DEFINITION rune gets the ground-zero recipe.
    if dname == "implies" && (cfg.worldVal.defs.get? { name := "implies" }).isNone then
      replayImpliesDef cfg ctx n
    else replayDefinition cfg ctx n depth
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
    -- preceding recognizer rewrote it via if-test congruence). The
    -- `if1/boolean` origin instead collapses `(if tst 't 'nil) ⇒ tst` for a
    -- BOOLEAN-valued symbolic test (ACL2 justifies it by type-set; the replay
    -- discharges the same claim by the test value's two-valuedness).
    match lhs with
    | .cons (.atom (.symbol ifS)) (.cons c (.cons thn (.cons els .nil))) =>
      unless ifS.name == "if" do
        throwError "if-simplification: head {ifS.name}"
      if prov.origin == "if1/boolean" then
        unless thn == quoteT && els == quoteNil && rhs == c do
          throwError "if1/boolean: node is not (if tst 't 'nil) ⇒ tst: \
                      {repr lhs} ⇒ {repr rhs}"
        let vC ← ctxValExpr cfg ctx c
        let hBool ←
          if vC.isAppOfArity ``Logic.equal 2 then
            mkAppM ``cond_toBool_equal #[vC.appFn!.appArg!, vC.appArg!]
          else do
            -- USER-FN test: two-valuedness from the fn's EMITTED
            -- :TYPE-PRESCRIPTION hypothesis (the boolean corollary shape),
            -- instantiated at the test's pinned value — consumed, not
            -- inferred (same source as the type-alist truthy verdict)
            let .cons (.atom (.symbol fs)) argsSpine := c
              | throwError "if1/boolean: test {repr c} is neither a \
                            Logic.equal value nor a fn application \
                            (two-valuedness source, frontier)"
            let some (_, _, tpHyp) := ctx.tpHyps.find? (fun (nm, _, _) => nm == fs.name)
              | throwError "if1/boolean: no :TYPE-PRESCRIPTION hypothesis for \
                            {fs.name} (emit more, frontier)"
            let some (formals, _) := cfg.worldVal.defs.get? fs
              | throwError "if1/boolean: {fs.name} not defined in the world"
            let args := (argsSpine.toList?).getD []
            unless formals.length == args.length do
              throwError "if1/boolean: arity mismatch instantiating the TP \
                          of {fs.name}"
            let some (v, conv) := ctx.val? c
              | throwError "if1/boolean: {repr c} has no pinned value (frontier)"
            let fact := mkAppN tpHyp ((#[cfg.envExpr] : Array Expr)
              ++ (args.map reflectSExpr).toArray ++ #[v, conv])
            mkAppM ``cond_toBool_of_tp_boolean #[v, fact]
        let pl ← ctxValProof cfg ctx lhs
        let pr ← ctxValProof cfg ctx c
        return ← mkAppM ``fuel_eq_of_conv #[pl, pr, hBool]
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
  | "if-same-branches", _ =>
    -- `(if c a a) ⇒ a` (if1/same-branches): the branch value is the if value
    -- whichever way the test goes; the test's convergence is the only premise.
    match lhs with
    | .cons (.atom (.symbol ifS)) (.cons c (.cons thn (.cons els .nil))) =>
      unless ifS.name == "if" do
        throwError "if-same-branches: head {ifS.name}"
      unless thn == els && rhs == thn do
        throwError "if-same-branches: node is not (if c a a) ⇒ a: \
                    {repr lhs} ⇒ {repr rhs}"
      let pc ← ctxValProof cfg ctx c
      let pa ← ctxValProof cfg ctx thn
      mkAppM ``re_if_same
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr c, reflectSExpr thn,
          ← ctxValExpr cfg ctx c, ← ctxValExpr cfg ctx thn, pc, pa]
    | _ => throwError "if-same-branches: lhs not an if: {repr lhs}"
  | "equal-self", _ =>
    -- `(equal X X) ⇒ 't` as a MID-CHAIN node (reflexivity of `equal`; the
    -- closing-literal form lives in `replayLiteral`).
    match asEqualSelf lhs with
    | none => throwError "equal-self: lhs is not (equal X X): {repr lhs}"
    | some X =>
      unless rhs == quoteT do
        throwError "equal-self: rhs {repr rhs} ≠ (quote t)"
      let hX ← proveConv cfg cfg.envExpr ctx X
      let hNoEqual ← proveNoShadow cfg { name := "equal" }
      let pEq ← mkAppM ``re_equal_self
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr X, hX, hNoEqual]
      let pQ ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr SExpr.t]
      mkAppM ``fuel_eq_of_conv #[pEq, pQ, ← mkEqRefl (mkConst ``SExpr.t)]
  | "type-alist", _ =>
    -- SOLIDIFY from the type-alist: the clause context — a spine literal's
    -- falsity — pins the term's value; the node rewrites the term to that
    -- constant. Only the direct-falsity/nil form is supported (a truthy or
    -- derived type-alist entry is a named frontier).
    let .cons (.atom (.symbol q)) (.cons cv .nil) := rhs
      | throwError "type-alist: rhs {repr rhs} is not a quoted constant"
    unless q.name == "quote" do
      throwError "type-alist: rhs {repr rhs} is not a quoted constant"
    if cv == SExpr.nil then
      let some hNil := ctx.litFactByTerm? lhs
        | throwError "type-alist: no spine falsity fact for {repr lhs} (frontier)"
      let pl ← ctxValProof cfg ctx lhs
      let pr ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr cv]
      mkAppM ``fuel_eq_of_conv #[pl, pr, hNil]
    else if cv == SExpr.t then
      -- TRUTHY verdict: the spine's `(not lhs)`-false fact gives ≠ nil; the
      -- fn's EMITTED :TYPE-PRESCRIPTION (the rune is on the node) pins the
      -- non-nil value to exactly `t` (two-valuedness — consumed, not inferred)
      let notLhs : SExpr := .cons (.atom (.symbol { name := "not" }))
        (.cons lhs .nil)
      let some hNotNil := ctx.litFactByTerm? notLhs
        | throwError "type-alist: no spine (not …)-falsity fact for \
                      {repr lhs} (frontier)"
      let vL ← ctxValExpr cfg ctx lhs
      let hne ← mkAppM ``logic_not_nil_ne #[vL, hNotNil]
      let .cons (.atom (.symbol fs)) argsSpine := lhs
        | throwError "type-alist: truthy verdict on a non-application \
                      {repr lhs} (frontier)"
      let some (_, _, tpHyp) := ctx.tpHyps.find? (fun (nm, _, _) => nm == fs.name)
        | throwError "type-alist: no :TYPE-PRESCRIPTION hypothesis for \
                      {fs.name} (emit more, frontier)"
      let some (formals, _) := cfg.worldVal.defs.get? fs
        | throwError "type-alist: {fs.name} not defined in the world"
      let args := (argsSpine.toList?).getD []
      unless formals.length == args.length do
        throwError "type-alist: arity mismatch instantiating the TP of {fs.name}"
      let some (v, conv) := ctx.val? lhs
        | throwError "type-alist: {repr lhs} has no pinned value (frontier)"
      let fact := mkAppN tpHyp ((#[cfg.envExpr] : Array Expr)
        ++ (args.map reflectSExpr).toArray ++ #[v, conv])
      let hT ← mkAppM ``tp_cond_boolean_t #[v, fact, hne]
      let pl ← ctxValProof cfg ctx lhs
      let pr ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr cv]
      mkAppM ``fuel_eq_of_conv #[pl, pr, hT]
    else
      throwError "type-alist: verdict {repr rhs} is neither nil nor t (frontier)"
  | "executable-counterpart", _ =>
    -- a GROUND computation step within a rewrite chain (e.g. `(consp 'nil) ⇒ 'nil`):
    -- ACL2 ran the executable counterpart; re-run the SAME closed computation and
    -- lift to the node-equality `eval lhs = eval rhs` (rhs the recorded constant).
    let .cons (.atom (.symbol q)) (.cons v .nil) := rhs
      | throwError "executable-counterpart: rhs {repr rhs} is not a quoted constant"
    unless q.name == "quote" do
      throwError "executable-counterpart: rhs {repr rhs} is not a quoted constant"
    let convLhs ← replayExecGround cfg lhs v
    let hq ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr v]
    mkAppM ``fuel_eq_of_conv #[convLhs, hq, ← mkEqRefl (reflectSExpr v)]
  | "rewrite", _ =>
    -- USER rewrite rule (with-lemma): the THEOREM-DEPENDENCY recipe
    -- (docs/plans/2026-07-05_theorem-dependency-hypotheses.md). The node
    -- consumes the bound `rule:<thm>` hypothesis — the STORED rule's mirror —
    -- instantiated strictly by the emitted :SUBST; hypothesis relief comes
    -- from the recorded :KIND HYP chain or the clause context, never
    -- re-searched. (The built-in-axiom runes above keep their hand recipes —
    -- their formulas are in no log.)
    unless prov.origin == "with-lemma" do
      throwError "rewrite rune ({rname}): origin {prov.origin} is not \
                  with-lemma (frontier)"
    let σvars ← prov.subst.mapM fun (v, _) => do
      let .atom (.symbol s) := v
        | throwError "rule {rname}: :SUBST binds a non-variable {repr v}"
      pure s
    let σterms := prov.subst.map (·.2)
    -- the matching stored rule: recompute-and-check joint —
    -- substTerm(:SUBST, rule lhs) must BE the node's lhs
    let candidates := ctx.ruleHyps.filter fun (r, _) => r.name == rname
    if candidates.isEmpty then
      throwError "rule {rname}: no stored-rule hypothesis in scope (no \
                  (:RULES …) entry — emission gap or missing telescope)"
    let matched := candidates.filter fun (r, _) =>
      ACL2.Replay.substTerm σvars σterms r.lhs == lhs
    let [(spec, hypV)] := matched
      | throwError "rule {rname}: {matched.length} stored rules match \
                    substTerm(:SUBST, lhs) == {repr lhs} (need exactly 1)"
    let innerKindOf : ProofNode → String := fun
      | .node _ _ _ _ p => p.innerKind
    let hypKids := children.filter fun c => innerKindOf c == "hyp"
    let rhsKids := children.filter fun c => innerKindOf c == "rhs"
    let otherKids := children.filter fun c =>
      innerKindOf c != "hyp" && innerKindOf c != "rhs"
    unless otherKids.isEmpty do
      throwError "rule {rname}: {otherKids.length} child(ren) outside the \
                  HYP/RHS blocks — unconsumed record (frontier)"
    -- rhs joint: the node's rhs is the instantiated rule rhs, possibly
    -- rewritten FURTHER by the recorded RHS-block chain (with-lemma rewrites
    -- the instantiated rhs before returning). The chain is replayed below and
    -- must land exactly on the node's rhs; a mismatch with NO recorded chain
    -- is a hard-fail.
    let rhsσ := ACL2.Replay.substTerm σvars σterms spec.rhs
    if rhsσ != rhs && rhsKids.isEmpty then
      throwError "rule {rname}: node rhs {repr rhs} ≠ substTerm(:SUBST, \
                  rule rhs {repr spec.rhs}) and no RHS chain recorded \
                  (emission gap)"
    -- partition the HYP block: silent-relief MARKERS (emit/relieve-hyp/*)
    -- vs an actual relief rewrite chain
    let (reliefMarkers, chainKids) := hypKids.partition
      fun c => (runeOf c).1 == "hyp-relief"
    -- coverage: every rule variable must be bound by σ (free-var hyps extend
    -- σ at emission; a gap means the emission is incomplete)
    let ruleFrees := ACL2.Replay.freeVars spec.lhs ++
      spec.hyps.flatMap ACL2.Replay.freeVars ++ ACL2.Replay.freeVars spec.rhs
    for s in ruleFrees do
      unless σvars.contains s do
        throwError "rule {rname}: rule variable {s.name} not bound by the \
                    emitted :SUBST (emission gap)"
    -- σ-term values and the substN bridge scaffold (shared by hyps/lhs/rhs)
    let w := cfg.worldExpr
    let env := cfg.envExpr
    let vals ← σterms.mapM (ctxValExpr cfg ctx)
    let convs ← σterms.mapM (ctxValProof cfg ctx)
    let formalsE ← mkListLit (mkConst ``Symbol) (σvars.map reflectSymbol)
    let argsE ← mkListLit (mkConst ``SExpr) (σterms.map reflectSExpr)
    let valsE ← mkListLit (mkConst ``SExpr) vals
    let env' ← mkAppM ``envUpdate #[env, formalsE, valsE]
    let hlenPf ← proveByDecide
      (← mkEq (← mkAppM ``List.length #[argsE]) (← mkAppM ``List.length #[valsE]))
      s!"substN lengths ({rname})"
    let prodTy ← mkAppM ``Prod #[mkConst ``SExpr, mkConst ``SExpr]
    let pFn ← withLocalDeclD `pr prodTy fun prV => do
      let fst ← mkAppM ``Prod.fst #[prV]
      let snd ← mkAppM ``Prod.snd #[prV]
      mkLambdaFVars #[prV] (← mkValConvPropEx w env fst snd)
    let entries ← (σterms.zip vals).mapM fun (t, v) =>
      mkAppM ``Prod.mk #[reflectSExpr t, v]
    let (_, hargsRaw) ← mkForallMemProof prodTy pFn (entries.zip convs)
    let zipE ← mkAppM ``List.zip #[argsE, valsE]
    let hargsTy ← withLocalDeclD `pr prodTy fun prV => do
      let mem ← mkAppM ``Membership.mem #[zipE, prV]
      mkForallFVars #[prV] (← mkArrow mem (mkApp pFn prV).headBeta)
    let hargs ← mkExpectedTypeHint hargsRaw hargsTy
    -- bridge t : eval env (substTerm σ t) ≡ eval env' t, for any rule-side term
    let bridge : SExpr → MetaM Expr := fun t => do
      let hNoLet ← proveByDecide
        (← mkEq (← mkAppM ``ACL2.Replay.NoLet #[reflectSExpr t]) (mkConst ``Bool.true))
        s!"NoLet rule term ({rname})"
      mkAppM ``evalOpt_substTerm_substN
        #[w, env, formalsE, argsE, valsE, reflectSExpr t, hNoLet, hlenPf, hargs]
    -- premises: EvTrue w env' hᵢ from the recorded relief. Sources, per hyp:
    -- a silent-relief MARKER whose hyp matches hσ (recompute-and-check) —
    -- clause-context lookup; else the recorded relief chain (v1: one hyp
    -- with a chain; multi-hyp chains need per-hyp bracketing — hard-fail
    -- until a real tree shows the shape).
    if !chainKids.isEmpty && spec.hyps.length != reliefMarkers.length + 1 then
      throwError "rule {rname}: {spec.hyps.length} hyps with one recorded \
                  relief chain and {reliefMarkers.length} markers — per-hyp \
                  partition (frontier)"
    let tNeNil ← proveByDecide
      (← mkAppM ``Ne #[mkConst ``SExpr.t, mkConst ``SExpr.nil]) "t ≠ nil"
    let mut prems : Array Expr := #[]
    for h in spec.hyps do
      let hσ := ACL2.Replay.substTerm σvars σterms h
      let hasMarker := reliefMarkers.any fun c => (nodeLhsRhs c).1 == hσ
      -- EVERY hyp must have an emitted relief RECORD — a silent-relief marker
      -- or a rewrite chain. No record at all is an emission gap (audit
      -- 2026-07-06 finding A): the clause context may well justify the hyp,
      -- but nothing in the tree says ACL2 relieved it that way — hard-fail
      -- and emit more, never paper over.
      if !hasMarker && chainKids.isEmpty then
        throwError "rule {rname}: hyp {repr hσ} has NO emitted relief record \
                    (no relieve-hyp marker, no relief chain) — emission gap \
                    (frontier)"
      let evTrueEnv ←
        if hasMarker then do
          -- relieved SILENTLY from the clause context (the emitted marker
          -- names the instantiated hyp): the spine's (not hσ)-falsity fact
          -- (the type-alist source the type-alist recipe also consumes)
          let notH : SExpr := .cons (.atom (.symbol { name := "not" }))
            (.cons hσ .nil)
          let some hNotNil := ctx.litFactByTerm? notH
            | throwError "rule {rname}: marker-relieved hyp {repr hσ} has no \
                          (not …)-falsity fact in scope (frontier)"
          let vH ← ctxValExpr cfg ctx hσ
          let hne ← mkAppM ``logic_not_nil_ne #[vH, hNotNil]
          mkAppM ``evtrue_of_conv_ne_nil #[← ctxValProof cfg ctx hσ, hne]
        else do
          -- the recorded HYP chain rewrites hσ ⇒ … ⇒ 't (paths carry one
          -- more boundary frame, as definition-body children do)
          let (chainOpt, finalT) ← replayRewrites cfg ctx hσ chainKids (depth + 1)
          unless finalT == quoteT do
            throwError "rule {rname}: relief chain for {repr hσ} ends at \
                        {repr finalT}, not (quote t)"
          let some chain := chainOpt
            | throwError "rule {rname}: relief chain for {repr hσ} \
                          composed to no steps"
          let hconv ← mkAppM ``fuel_conv_of_eq #[chain, ← quoteTFact cfg]
          mkAppM ``evtrue_of_conv_ne_nil #[hconv, tNeNil]
      -- transport to env': eval env' h ≡ eval env hσ (the bridge, reversed)
      let pB ← bridge h
      prems := prems.push
        (← mkAppM ``evtrue_of_fuel_eq #[← mkAppM ``fuel_eq_symm #[pB], evTrueEnv])
    -- the rule's mirror at env', premises applied, bridged back to the node:
    -- eval env lhs ≡ eval env' rule.lhs ≡ eval env' rule.rhs ≡ eval env rhsσ
    -- [≡ eval env rhs, by the recorded RHS-block chain when one exists]
    let hRule := mkAppN (mkApp hypV env') prems
    let pL ← bridge spec.lhs
    let pR ← bridge spec.rhs
    let pCore ← mkAppM ``fuel_chain_eq
      #[pL, ← mkAppM ``fuel_chain_eq #[hRule, ← mkAppM ``fuel_eq_symm #[pR]]]
    if rhsKids.isEmpty then
      unless rhsσ == rhs do
        throwError "rule {rname}: internal — rhs mismatch with no RHS chain"
      return pCore
    -- the RHS continuation: replay the recorded chain from rhsσ; it must land
    -- exactly on the node's recorded rhs (fail-closed)
    let ctx ← pinTermOpaques cfg cfg.envExpr ctx rhsσ
    let (chainOpt, finalT) ← replayRewrites cfg ctx rhsσ rhsKids (depth + 1)
    unless finalT == rhs do
      throwError "rule {rname}: RHS chain reached {repr finalT}, node rhs is \
                  {repr rhs}"
    match chainOpt with
    | none => return pCore
    | some ch => mkAppM ``fuel_chain_eq #[pCore, ch]
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
    -- an if-simplification recorded as an IDENTITY (`X ⇒ X`, no children) is
    -- ambiguous: either a true no-op, or a DISPLAY-FOLDED constant-test
    -- collapse (`(if 'c a b) ⇒ branch` logged with the already-collapsed
    -- term on both sides). The RUNNING term at the node's path is the ground
    -- truth: equal to rhs → no-op (replay as reflexivity by skipping);
    -- a constant-test if collapsing to rhs → replay the collapse.
    if lhs == rhs && (runeOf n).1 == "if-simplification" then
      if let .node _ _ _ [] _ := n then
        let rel ← relativizeAndStrip (nodePath n) depth strip
        let (_, S) ← ofExcept (navigateFrames start rel)
        if S == rhs then
          return ← replayRewrites cfg ctx start rest depth strip
        let .cons (.atom (.symbol ifS))
            (.cons (.cons (.atom (.symbol q)) (.cons cv .nil))
              (.cons thn (.cons els .nil))) := S
          | throwError "replayRewrites: identity if-simplification's running \
                        subterm {repr S} is neither rhs {repr rhs} nor a \
                        constant-test if (frontier)"
        unless ifS.name == "if" && q.name == "quote" do
          throwError "replayRewrites: identity if-simplification's running \
                      subterm {repr S} is not a constant-test if (frontier)"
        let branch := if cv == SExpr.nil then els else thn
        unless branch == rhs do
          throwError "replayRewrites: folded constant-test collapse of \
                      {repr S} selects {repr branch}, node rhs is {repr rhs}"
        let c : SExpr := .cons (.atom (.symbol q)) (.cons cv .nil)
        let hc ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr cv]
        let nodeEq ←
          if cv == SExpr.nil then
            let vb ← ctxValExpr cfg ctx els
            let hb ← ctxValProof cfg ctx els
            let hcNil ← mkAppM ``re_val_cast
              #[cfg.worldExpr, cfg.envExpr, reflectSExpr c, reflectSExpr cv,
                mkConst ``SExpr.nil, hc, ← proveByDecide
                  (← mkEq (reflectSExpr cv) (mkConst ``SExpr.nil)) "cv is nil"]
            let _ := vb
            mkAppM ``re_if_false
              #[cfg.worldExpr, cfg.envExpr, reflectSExpr c, reflectSExpr thn,
                reflectSExpr els, vb, hcNil, hb]
          else
            let hcv ← proveByDecide
              (← mkEq (mkApp (mkConst ``Logic.toBool) (reflectSExpr cv))
                      (mkConst ``Bool.true)) "toBool of the constant test"
            let va ← ctxValExpr cfg ctx thn
            let ha ← ctxValProof cfg ctx thn
            let _ := va
            mkAppM ``re_if_true
              #[cfg.worldExpr, cfg.envExpr, reflectSExpr c, reflectSExpr thn,
                reflectSExpr els, reflectSExpr cv, va, hc, hcv, ha]
        let (lifted, newTerm) ←
          emitCongruence cfg.worldExpr cfg.envExpr start (nodePath n) S branch
            nodeEq depth strip
        let (restProof, finalTerm) ← replayRewrites cfg ctx newTerm rest depth strip
        match restProof with
        | none => return (some lifted, finalTerm)
        | some rp => return (some (← mkAppM ``fuel_chain_eq #[lifted, rp]), finalTerm)
    -- DEAD-BRANCH display folds (option A, docs/notes/2026-06-14_exec-
    -- counterpart-and-folding-wall.md, data-ratified 2026-07-06: every
    -- observed fold sits in the DISCARDED branch): a constant-test
    -- if-simplification's recorded lhs went through sublis-var, whose
    -- cons-term folds (car 'c)/(cdr 'c) inside the branches — logging-only,
    -- per ACL2's own comment. The RUNNING term is the ground truth: require
    -- the SAME test and the SAME taken branch (strict), allow the dead
    -- branch to differ, and replay the collapse on the RUNNING term —
    -- `(if 'c a b) = taken` is independent of the discarded branch.
    if (runeOf n).1 == "if-simplification" && lhs != rhs then
      if let .node _ _ _ [] _ := n then
        if let .cons (.atom (.symbol ifS))
            (.cons c@(.cons (.atom (.symbol q)) (.cons cv .nil))
              (.cons thn (.cons els .nil))) := lhs then
          if ifS.name == "if" && q.name == "quote" then
            let rel ← relativizeAndStrip (nodePath n) depth strip
            let (_, S) ← ofExcept (navigateFrames start rel)
            -- take the relaxation ONLY on the exact dead-branch-fold shape:
            -- same test, same taken branch, difference confined to the dead
            -- branch. Anything else falls THROUGH to the normal machinery
            -- (if-finish/combined etc.), which handles or fails precisely.
            let compatible :=
              match S with
              | .cons (.atom (.symbol ifS')) (.cons c' (.cons thn' (.cons els' .nil))) =>
                let taken := if cv == SExpr.nil then els else thn
                let taken' := if cv == SExpr.nil then els' else thn'
                ifS'.name == "if" && c' == c && taken' == taken && rhs == taken
              | _ => false
            if S != lhs && compatible then
              let .cons _ (.cons _ (.cons thn' (.cons els' .nil))) := S
                | throwError "replayRewrites: internal — compatible running \
                              subterm lost its if shape"
              let hc ← mkAppM ``re_val_quote
                #[cfg.worldExpr, cfg.envExpr, reflectSExpr cv]
              let nodeEq ←
                if cv == SExpr.nil then
                  let hb ← ctxValProof cfg ctx els'
                  let vb ← ctxValExpr cfg ctx els'
                  let hcNil ← mkAppM ``re_val_cast
                    #[cfg.worldExpr, cfg.envExpr, reflectSExpr c, reflectSExpr cv,
                      mkConst ``SExpr.nil, hc, ← proveByDecide
                        (← mkEq (reflectSExpr cv) (mkConst ``SExpr.nil)) "cv is nil"]
                  mkAppM ``re_if_false
                    #[cfg.worldExpr, cfg.envExpr, reflectSExpr c, reflectSExpr thn',
                      reflectSExpr els', vb, hcNil, hb]
                else
                  let hcv ← proveByDecide
                    (← mkEq (mkApp (mkConst ``Logic.toBool) (reflectSExpr cv))
                            (mkConst ``Bool.true)) "toBool of the constant test"
                  let ha ← ctxValProof cfg ctx thn'
                  let va ← ctxValExpr cfg ctx thn'
                  mkAppM ``re_if_true
                    #[cfg.worldExpr, cfg.envExpr, reflectSExpr c, reflectSExpr thn',
                      reflectSExpr els', reflectSExpr cv, va, hc, hcv, ha]
              let (lifted, newTerm) ←
                emitCongruence cfg.worldExpr cfg.envExpr start (nodePath n) S rhs
                  nodeEq depth strip
              let (restProof, finalTerm) ← replayRewrites cfg ctx newTerm rest depth strip
              match restProof with
              | none => return (some lifted, finalTerm)
              | some rp =>
                return (some (← mkAppM ``fuel_chain_eq #[lifted, rp]), finalTerm)
    -- clause-context-resolution marker: ACL2's rewrite-atm emits this as a
    -- terminal REPORT ("we have proved the original literal … hence the
    -- clause", simplify.lisp) — lhs is the ORIGINAL atom, rhs the NET constant
    -- the preceding chain nodes already produced. It is not a sequential step;
    -- when it is terminal and the running term already equals its rhs, it adds
    -- no reasoning, so verify-then-drop. Fail-closed otherwise.
    if (runeOf n).1 == "clause-context-resolution" then
      unless rest.isEmpty do
        throwError "clause-context-resolution: non-terminal marker (frontier)"
      unless rhs == start do
        throwError "clause-context-resolution: rhs {repr rhs} ≠ running term {repr start} \
                    (chain did not reach the reported net result)"
      return (none, start)
    -- `if-finish/combined`: rewrite-if FINISHED an if whose test stayed
    -- symbolic — the summary node's recorded lhs is DISPLAY-FOLDED (body
    -- coordinates), so the running term is the ground truth: navigate to the
    -- node's position for the REAL redex `S = (if c thn els)`, chain the
    -- node's CHILDREN over the branch each descends into UNDER that branch's
    -- test assumption (ACL2's assume-true-false — the conditional-congruence
    -- lemma discharges the hypotheses), require the result to be the node's
    -- recorded rhs, and lift by congruence.
    if let .node ("if-simplification", _) _ _ children prov := n then
      if prov.origin == "if-finish/combined" then
        let rel ← relativizeAndStrip (nodePath n) depth strip
        let (steps, S) ← ofExcept (navigateFrames start rel)
        let strip' := strip ++ steps.map (·.argIdx + 1)
        let .cons (.atom (.symbol ifS)) (.cons c (.cons thn (.cons els .nil))) := S
          | throwError "if-finish/combined: running subterm {repr S} is not a \
                        3-arg if"
        unless ifS.name == "if" do
          throwError "if-finish/combined: running subterm head {ifS.name} ≠ if"
        -- partition the children: branch rewrites (path descends arg 2/3),
        -- then whole-if FINISHING steps (path AT the if, e.g. if1/boolean) —
        -- ACL2 finishes the branches first, then combines
        let mut thenCh : List ProofNode := []
        let mut elseCh : List ProofNode := []
        let mut postCh : List ProofNode := []
        for chN in children do
          let chRel ← relativizeAndStrip (nodePath chN) depth strip'
          match chRel with
          | .arg 2 _ :: _ =>
            unless postCh.isEmpty do
              throwError "if-finish/combined: branch child after a whole-if \
                          child (frontier)"
            thenCh := thenCh ++ [chN]
          | .arg 3 _ :: _ =>
            unless postCh.isEmpty do
              throwError "if-finish/combined: branch child after a whole-if \
                          child (frontier)"
            elseCh := elseCh ++ [chN]
          | [] => postCh := postCh ++ [chN]
          | _ => throwError "if-finish/combined: child path does not descend \
                             a branch of the if (frontier): {repr (nodePath chN)}"
        let w := cfg.worldExpr
        let e := cfg.envExpr
        let vC ← ctxValExpr cfg ctx c
        let pC ← ctxValProof cfg ctx c
        let nilC := mkConst ``SExpr.nil
        let mkIdEq (t : SExpr) : MetaM Expr := do
          let fn ← withLocalDeclD `f (mkConst ``Nat) fun fV =>
            mkLambdaFVars #[fV] (mkApp4 (mkConst ``evalOpt) fV w e (reflectSExpr t))
          mkAppM ``fuel_eq_refl #[fn]
        let (lamT, thn') ← withLocalDeclD `hne (← mkAppM ``Ne #[vC, nilC]) fun hNe => do
          let ctx' := { ctx with branchFacts := ctx.branchFacts ++ [(c, vC, true, hNe)] }
          let (chT, thn') ← replayRewrites cfg ctx' thn thenCh depth (strip' ++ [2])
          let prf ← match chT with
            | some p => pure p
            | none => mkIdEq thn
          pure (← mkLambdaFVars #[hNe] prf, thn')
        let (lamE, els') ← withLocalDeclD `hnil (← mkEq vC nilC) fun hNil => do
          let ctx' := { ctx with branchFacts := ctx.branchFacts ++ [(c, vC, false, hNil)] }
          let (chE, els') ← replayRewrites cfg ctx' els elseCh depth (strip' ++ [3])
          let prf ← match chE with
            | some p => pure p
            | none => mkIdEq els
          pure (← mkLambdaFVars #[hNil] prf, els')
        let target : SExpr := .cons (.atom (.symbol ifS))
          (.cons c (.cons thn' (.cons els' .nil)))
        -- whole-if finishing steps apply AFTER the branch congruence, on the
        -- rebuilt if
        let (postOpt, final) ← replayRewrites cfg ctx target postCh depth strip'
        unless final == rhs do
          throwError "if-finish/combined: children chains reached {repr final}, \
                      node rhs is {repr rhs}"
        let mut proofs : List Expr := []
        if target != S then
          proofs := proofs ++ [← mkAppM ``evalOpt_congr_if_branches_cond
            #[w, e, reflectSExpr c, reflectSExpr thn, reflectSExpr els,
              reflectSExpr thn', reflectSExpr els', vC, pC, lamT, lamE]]
        if let some p := postOpt then
          proofs := proofs ++ [p]
        if proofs.isEmpty then
          -- no effective rewrites: a no-op summary node
          unless S == rhs do
            throwError "if-finish/combined: no effective children but running \
                        subterm {repr S} ≠ rhs {repr rhs}"
          return ← replayRewrites cfg ctx start rest depth strip
        let nodeProof ← chainEqs proofs
        let (lifted, newTerm) ←
          emitCongruence w e start (nodePath n) S final nodeProof depth strip
        let (restProof, finalTerm) ← replayRewrites cfg ctx newTerm rest depth strip
        match restProof with
        | none => return (some lifted, finalTerm)
        | some rp => return (some (← mkAppM ``fuel_chain_eq #[lifted, rp]), finalTerm)
    -- a CONSTANT-TEST if-simplification whose recorded test does not match
    -- the running term's test: the test was resolved by an UNEMITTED
    -- type-alist lookup (a clause/segment fact, possibly through `equal`'s
    -- commutativity — if-interp-assumed-value2's rule). Mirror the
    -- resolution as an explicit test-position rewrite, then replay the
    -- recorded collapse on the reconciled term.
    let reconciled? ← do
      if (runeOf n).1 == "if-simplification" then
        match lhs with
        | .cons (.atom (.symbol ifS))
            (.cons (.cons (.atom (.symbol q)) (.cons cv .nil)) _) =>
          if ifS.name == "if" && q.name == "quote" && cv == SExpr.nil then
            let rel ← relativizeAndStrip (nodePath n) depth strip
            let (steps, S) ← ofExcept (navigateFrames start rel)
            match S with
            | .cons (.atom (.symbol ifS'))
                (.cons T (.cons thn (.cons els .nil))) =>
              if ifS'.name == "if" && S != lhs &&
                 lhs == SExpr.cons (.atom (.symbol ifS'))
                   (.cons (.cons (.atom (.symbol q)) (.cons cv .nil))
                     (.cons thn (.cons els .nil))) then
                -- derive `value of T = nil` from the in-scope facts: spine
                -- falsity (litFacts/segFacts), an enclosing if-test assumed
                -- FALSE (branchFacts), either through `equal`'s commutativity
                -- (if-interp-assumed-value2's rule), or through a
                -- :CONTEXT-SUBST segment equality pinning one `equal` side
                -- (a false `(not (equal p q))` gives vp = vq; the substituted
                -- test's falsity is then a direct fact)
                let nilFactFor : SExpr → Option Expr := fun u =>
                  (ctx.litFactByTerm? u).orElse fun _ =>
                    (ctx.branchFacts.find? (fun (t, _, sign, _) =>
                      t == u && !sign)).map (·.2.2.2)
                let eqOf : SExpr → SExpr → SExpr := fun x y =>
                  .cons (.atom (.symbol { name := "equal" }))
                    (.cons x (.cons y .nil))
                let directOrFlipped : SExpr → MetaM (Option Expr) := fun u => do
                  match nilFactFor u with
                  | some h => return some h
                  | none =>
                    match u with
                    | .cons (.atom (.symbol eqS)) (.cons x (.cons y .nil)) =>
                      if eqS.name == "equal" then
                        match nilFactFor (eqOf y x) with
                        | some h => do
                          let vx ← ctxValExpr cfg ctx x
                          let vy ← ctxValExpr cfg ctx y
                          let comm ← mkAppM ``logic_equal_comm #[vx, vy]
                          return some (← mkAppM ``Eq.trans #[comm, h])
                        | none => return none
                      else return none
                    | _ => return none
                let hNil? ← do
                  match ← directOrFlipped T with
                  | some h => pure (some h)
                  | none =>
                    match T with
                    | .cons (.atom (.symbol eqS)) (.cons u (.cons v .nil)) =>
                      if !(eqS.name == "equal") then pure none else do
                      let mut found : Option Expr := none
                      for (st, hSeg) in ctx.segFacts do
                        if found.isSome then break
                        let .cons (.atom (.symbol ns))
                            (.cons pq@(.cons (.atom (.symbol eqS'))
                              (.cons p (.cons q .nil))) .nil) := st
                          | continue
                        unless ns.name == "not" && eqS'.name == "equal" do
                          continue
                        -- heq : vp = vq from the false segment literal
                        let vPQ ← ctxValExpr cfg ctx pq
                        let hne ← mkAppM ``logic_not_nil_ne #[vPQ, hSeg]
                        let heq ← mkAppM ``Logic.eq_of_equal_ne_nil #[hne]
                        let vu ← ctxValExpr cfg ctx u
                        let vv ← ctxValExpr cfg ctx v
                        -- the four side-substitution variants; each transports
                        -- vT to the substituted test's value, then a direct
                        -- fact finishes
                        let tryVariant (t' : SExpr) (vEq : Expr) :
                            MetaM (Option Expr) := do
                          match ← directOrFlipped t' with
                          | some h' => return some (← mkAppM ``Eq.trans #[vEq, h'])
                          | none => return none
                        let fR ← withLocalDeclD `z (mkConst ``SExpr) fun zV => do
                          mkLambdaFVars #[zV] (← mkAppM ``Logic.equal #[vu, zV])
                        let fL ← withLocalDeclD `z (mkConst ``SExpr) fun zV => do
                          mkLambdaFVars #[zV] (← mkAppM ``Logic.equal #[zV, vv])
                        if v == p then
                          -- T = (equal u p): vT = f vp = f vq = v(equal u q)
                          let vEq ← mkAppM ``congrArg #[fR, heq]
                          found ← tryVariant (eqOf u q) vEq
                        if found.isNone && v == q then
                          let vEq ← mkAppM ``Eq.symm #[← mkAppM ``congrArg #[fR, heq]]
                          found ← tryVariant (eqOf u p) vEq
                        if found.isNone && u == p then
                          let vEq ← mkAppM ``congrArg #[fL, heq]
                          found ← tryVariant (eqOf q v) vEq
                        if found.isNone && u == q then
                          let vEq ← mkAppM ``congrArg #[fL, heq]
                          found ← tryVariant (eqOf p v) (← mkAppM ``Eq.symm #[vEq])
                      pure found
                    | _ => pure none
                let some hNil := hNil?
                  | throwError "replayRewrites: unemitted test resolution — no \
                                in-scope nil fact for the if-test {repr T} \
                                (frontier)"
                let pT ← ctxValProof cfg ctx T
                let pQ ← mkAppM ``re_val_quote
                  #[cfg.worldExpr, cfg.envExpr, reflectSExpr SExpr.nil]
                let testEq ← mkAppM ``fuel_eq_of_conv #[pT, pQ, hNil]
                -- lift the test rewrite at the node's path + the test position
                let mut inner := testEq
                let testStep : PathStep :=
                  { fn := ifS', arity := 3, argIdx := 0, siblings := [thn, els] }
                inner ← applyStep cfg.worldExpr cfg.envExpr testStep T
                  (SExpr.cons (.atom (.symbol q)) (.cons cv .nil)) inner
                let mut curL := S
                let mut curR := lhs
                for st in steps.reverse do
                  inner ← applyStep cfg.worldExpr cfg.envExpr st curL curR inner
                  curL := rebuild st.fn st.arity st.argIdx curL st.siblings
                  curR := rebuild st.fn st.arity st.argIdx curR st.siblings
                unless curL == start do
                  throwError "replayRewrites: test-resolution lift \
                              reconstructed {repr curL} ≠ {repr start}"
                pure (some (inner, curR))
              else pure none
            | _ => pure none
          else pure none
        | _ => pure none
      else pure none
    if let some (testChain, start') := reconciled? then
      -- eval start ≡ eval start[T := 'nil]; replay THIS node on the
      -- reconciled term and continue
      let (restAll, finalT) ← replayRewrites cfg ctx start' (n :: rest) depth strip
      match restAll with
      | none => return (some testChain, finalT)
      | some rp =>
        return (some (← mkAppM ``fuel_chain_eq #[testChain, rp]), finalT)
    let nodeEq ← replayNode cfg ctx n depth
    let (lifted, newTerm) ←
      emitCongruence cfg.worldExpr cfg.envExpr start (nodePath n) lhs rhs nodeEq depth strip
    -- an if-simplification AT THE CHAIN ROOT selects a branch; ACL2's rewrite-if
    -- keeps the if on the gstack while rewriting inside that branch, so the
    -- remaining nodes' paths carry the branch frame — record it for stripping.
    let strip' ←
      -- BRANCH-SELECTING root if-simplifications only: an `if1/boolean`
      -- collapse replaces the if by its (boolean) test — no branch frame
      -- remains on the gstack, so nothing to strip.
      if (runeOf n).1 == "if-simplification" && lhs == start &&
         (nodeOrigin n) != "if1/boolean" then
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
    -- HIDDEN definitional `implies` unfold: rewrite-atm expands an implies
    -- atom with NO emitted node (only the literal's :RESULT shows it) —
    -- mirror it via the same ground-zero recipe as the preprocess step,
    -- record-directed (only when the plain chain does not already match).
    let (chainOpt, finalAtom) ←
      match finalAtom with
      | .cons (.atom (.symbol impS)) (.cons A (.cons B .nil)) =>
        if impS.name == "implies" &&
           SExpr.cons (.atom (.symbol notS)) (.cons finalAtom .nil) != lp.result then do
          let expanded : SExpr :=
            .cons (.atom (.symbol { name := "if" }))
              (.cons A (.cons (.cons (.atom (.symbol { name := "if" }))
                (.cons B (.cons quoteT (.cons quoteNil .nil))))
                (.cons quoteT .nil)))
          let step ← replayImpliesDef cfg ctx
            (.node ("definition", "implies") finalAtom expanded [] {})
          let combined ← match chainOpt with
            | none => pure step
            | some c => mkAppM ``fuel_chain_eq #[c, step]
          pure (some combined, expanded)
        else pure (chainOpt, finalAtom)
      | _ => pure (chainOpt, finalAtom)
    let finalLit := SExpr.cons (.atom (.symbol notS)) (.cons finalAtom .nil)
    let lifted ← match chainOpt with
      | none => pure none
      | some ch =>
        let ns ← proveNotSpecial notS
        pure (some (mkAppN (mkConst ``evalOpt_congr_unary)
          #[cfg.worldExpr, cfg.envExpr, reflectSymbol notS, reflectSExpr atm,
            reflectSExpr finalAtom, ns, ch]))
    -- when the atom chain ends at a quoted constant, ACL2 folds `(not 'c)` by
    -- execution — implicit in the record (only the literal's :RESULT shows it).
    -- Mirror it: re-run the SAME closed computation (the exec-counterpart
    -- carve-out) and chain `eval (not 'c) ≡ eval 'folded`. The spine's
    -- result check then validates the fold against ACL2's recorded :RESULT.
    match finalAtom with
    | .cons (.atom (.symbol q)) (.cons c .nil) =>
      if q.name == "quote" then
        let foldedV : SExpr := if c == SExpr.nil then SExpr.t else SExpr.nil
        let foldedT : SExpr :=
          .cons (.atom (.symbol { name := "quote" })) (.cons foldedV .nil)
        let pNot ← replayExecGround cfg finalLit foldedV
        let pQ ← mkAppM ``re_val_quote
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr foldedV]
        let step ← mkAppM ``fuel_eq_of_conv
          #[pNot, pQ, ← mkEqRefl (reflectSExpr foldedV)]
        let chain ← match lifted with
          | none => pure step
          | some l => mkAppM ``fuel_chain_eq #[l, step]
        return (some chain, foldedT)
      else
        return (lifted, finalLit)
    | _ => return (lifted, finalLit)
  else
    replayRewrites cfg ctx lp.literal lp.nodes 0

/-- Replay a literal that closes to `t`: chain its rewrite nodes, then close with the
    terminal node. The closer is either `equal-self` (reflexivity of `equal`) or an
    `executable-counterpart` ground computation that reduces the rewritten literal
    (a closed term, e.g. `(equal 'nil 'nil)`) to `t` — the same way ACL2 closed it.
    Returns `∃N∀f≥N, eval lp.literal = some t`. -/
def replayLiteral (cfg : ReplayConfig) (ctx : ReplayCtx) (lp : LiteralProof) : MetaM Expr := do
  if lp.notFlg then
    -- A `:NOT-FLG T` closer `(not atm)` reaches `t` because ACL2 rewrote the
    -- atom to a nil constant and then ran `(not <nil-const>)` implicitly (no
    -- separate closer node — the negation-of-false is recorded only as the
    -- literal's `:RESULT 'T`). Replay it the same way: chain the atom and lift
    -- through `not` exactly as the non-closing notFlg path does
    -- (`replayLiteralChain`), then close the resulting ground `(not finalAtom)`
    -- by re-running the SAME computation (`replayExecGround`, the
    -- exec-counterpart carve-out). Hard-fails cleanly if the lifted literal is
    -- not ground or does not reduce to `t` — i.e. if ACL2 closed it some other
    -- way (a new, named frontier, not a guess).
    let (chainOpt, finalLit) ← replayLiteralChain cfg ctx lp
    let closeProof ← replayExecGround cfg finalLit SExpr.t
    match chainOpt with
    | none => return closeProof
    | some ch => return (← mkAppM ``fuel_chain_eq #[ch, closeProof])
  -- non-notFlg closer: the FULL chain — equal-self, executable-counterpart,
  -- with-lemma-to-'t, clause-context-resolution reports are all ordinary
  -- node recipes now — must reduce the literal to `(quote t)`; close by the
  -- chain + the quote's evaluation.
  if lp.nodes.isEmpty then
    throwError "replayLiteral: literal {repr lp.literal} has no proof nodes"
  let (chainOpt, finalT) ← replayRewrites cfg ctx lp.literal lp.nodes 0
  unless finalT == quoteT do
    throwError "replayLiteral: closing literal's chain reached {repr finalT}, \
                not (quote t) (frontier)"
  let some ch := chainOpt
    | throwError "replayLiteral: closing literal {repr lp.literal} chained to \
                  't with no effective steps"
  mkAppM ``fuel_conv_of_eq #[ch, ← quoteTFact cfg]

/-- The clause's literal items in order, with their 1-based indices, descending
    into case branches (a branch's items continue the same clause's literals). -/
partial def flattenLiterals : List ClauseItem → List (Nat × LiteralProof)
  | [] => []
  | .literal lp :: rest => (lp.index, lp) :: flattenLiterals rest
  | .step _ :: rest => flattenLiterals rest
  | .clausify _ :: rest => flattenLiterals rest
  | .branch _ items :: rest => flattenLiterals items ++ flattenLiterals rest

/-- The CLAUSE-CONTEXT falsity demands of a literal's chain, as the exact
    clause-literal terms whose falsity the chain's nodes consume (ACL2 rewrites
    literal i under the falsity of ALL other clause literals):
    - a silent hyp-relief marker for hyp `h` demands `(not h)`;
    - a `type-alist` nil-verdict node `l ⇒ 'nil` demands `l` itself;
    - a `type-alist` truthy node `l ⇒ 't` demands `(not l)`. -/
partial def collectContextDemands : ProofNode → List SExpr
  | .node (rty, _) l rh children _ =>
    let notOf : SExpr → SExpr := fun t =>
      .cons (.atom (.symbol { name := "not" })) (.cons t .nil)
    (if rty == "hyp-relief" then [notOf l]
     else if rty == "type-alist" then
       if rh == quoteNil then [l]
       else if rh == quoteT then [notOf l]
       else []
     else []) ++ children.flatMap collectContextDemands

/-- `EvTrue (disjoin lits)` from the TRUTH of the k-th literal (0-based):
    descend the lazy if-spine by value splits — an earlier literal's truth
    closes the clause anyway; at `k` the nil case is refuted by `hTrue`
    (`v(litK) ≠ nil`). -/
partial def evtrueOfLitTrue (cfg : ReplayConfig) (ctx : ReplayCtx)
    (lits : List SExpr) (k : Nat) (litK : SExpr) (hTrue : Expr) : MetaM Expr := do
  match lits with
  | [] => throwError "evtrueOfLitTrue: index beyond the clause"
  | [l] =>
    unless k == 0 && l == litK do
      throwError "evtrueOfLitTrue: index/literal mismatch at the last literal"
    let ctx ← pinTermOpaques cfg cfg.envExpr ctx l
    let pL ← ctxValProof cfg ctx l
    mkAppM ``evtrue_of_conv_ne_nil #[pL, hTrue]
  | l :: rest =>
    -- pin the literal's user-fn opaques on demand (callers hold facts about
    -- other literals; this walk may be the first to touch this one)
    let ctx ← pinTermOpaques cfg cfg.envExpr ctx l
    let vL ← ctxValExpr cfg ctx l
    let pL ← ctxValProof cfg ctx l
    let restTerm := disjoinTerm rest
    let nilC := mkConst ``SExpr.nil
    let hthen ← withLocalDeclD `h (← mkAppM ``Ne #[vL, nilC]) fun h => do
      let p ← mkAppM ``evtrue_of_eq_t #[← quoteTFact cfg]
      let _ := h
      mkLambdaFVars #[h] p
    let helse ← withLocalDeclD `h (← mkEq vL nilC) fun h => do
      let p ←
        if k == 0 then do
          unless l == litK do
            throwError "evtrueOfLitTrue: literal at k ≠ the true literal"
          let goalTy ← mkAppM ``EvTrue
            #[cfg.worldExpr, cfg.envExpr, reflectSExpr restTerm]
          mkAppOptM ``absurd #[none, some goalTy, some h, some hTrue]
        else
          evtrueOfLitTrue cfg ctx rest (k - 1) litK hTrue
      mkLambdaFVars #[h] p
    mkAppM ``evtrue_dp_if_split
      #[cfg.worldExpr, cfg.envExpr, reflectSExpr l, reflectSExpr quoteT,
        reflectSExpr restTerm, vL, pL, hthen, helse]

/-- The literal-clausify DECISION TREE, reconstructed from the flat
    `SplitDecision` trace (docs/notes/2026-07-03_branch-split-spine.md).
    `if-interp` pushes events else-branch-FIRST at splits; every event is
    self-located by its `path`, which the parser validates against its
    position (fail-closed). -/
inductive TraceTree where
  | leaf (value : SExpr) (outcome : String)
  | resolved (test : SExpr) (verdict : String) (how : String) (sub : TraceTree)
  /-- A genuine split: `fSide` (test assumed false — the ELSE branch,
      logged first) and `tSide`. -/
  | split (test : SExpr) (fSide tSide : TraceTree)
  deriving Repr, Inhabited

partial def parseTraceTree (path : List (Bool × SExpr)) :
    List SplitDecision → Except String (TraceTree × List SplitDecision)
  | [] => throw "parseTraceTree: trace ended without a leaf"
  | .test t v h p :: rest => do
    unless p == path do
      throw s!"parseTraceTree: test {repr t} at path {repr p}, expected \
               {repr path}"
    if v == "split" then
      let (fSide, rest) ← parseTraceTree (path ++ [(false, t)]) rest
      let (tSide, rest) ← parseTraceTree (path ++ [(true, t)]) rest
      return (.split t fSide tSide, rest)
    else
      let (sub, rest) ← parseTraceTree path rest
      return (.resolved t v h sub, rest)
  | .leaf v o p :: rest => do
    unless p == path do
      throw s!"parseTraceTree: leaf {repr v} at path {repr p}, expected \
               {repr path}"
    return (.leaf v o, rest)

/-- Collapse `t`'s ifs whose tests are DECIDED by the in-scope facts (the
    branch-split composer's byCases hypotheses + re-derived resolved
    verdicts), plus the two `call-stack` folds if-interp applied — `(not 'c)`
    by ground re-execution, `(equal X X)` by reflexivity — bottom-up,
    mirroring if-interp's interpretation of the rewritten literal. Returns
    the fuel-eq chain `eval t ≡ eval t'` and the collapsed `t'`. Anything the
    enumerated rule set cannot decide is left in place; the composer's
    leaf-value check fail-closes on divergence from the emitted trace. -/
partial def collapseEval (cfg : ReplayConfig) (ctx : ReplayCtx)
    (facts : List (SExpr × Expr × Bool × Expr)) (t : SExpr) :
    MetaM (Option Expr × SExpr) := do
  let w := cfg.worldExpr
  let e := cfg.envExpr
  let some (fs, args) := asApp t | return (none, t)
  if fs.name == "quote" then return (none, t)
  -- an in-scope SPINE falsity fact resolves the term outright: if-interp
  -- consults the clause-segment ASSUMPTIONS for the terms it encounters (the
  -- other literals are assumed false) — e.g. a collapsed residual that IS
  -- another clause literal. Divergence still fail-closes at the composer's
  -- leaf-value check.
  if let some hNil := ctx.litFactByTerm? t then
    let pl ← ctxValProof cfg ctx t
    let pr ← mkAppM ``re_val_quote #[w, e, reflectSExpr SExpr.nil]
    let step ← mkAppM ``fuel_eq_of_conv #[pl, pr, hNil]
    return (some step, quoteNil)
  if fs.name == "if" then
    match args with
    | [c, a, b] =>
      -- collapse the test first; decide; then only the LIVE branch
      let (chC, c') ← collapseEval cfg ctx facts c
      let mut acc : Option Expr := none
      let mut cur := t
      if let some ch := chC then
        let st : PathStep := { fn := fs, arity := 3, argIdx := 0, siblings := [a, b] }
        acc := some (← applyStep w e st c c' ch)
        cur := .cons (.atom (.symbol fs)) ([c', a, b].foldr .cons .nil)
      match facts.find? (fun (T, _, _, _) => T == c') with
      | some (_, vT, sign, h) =>
        let hc ← ctxValProof cfg ctx c'
        let step ←
          if sign then
            let hcv ← mkAppM ``toBool_true_of_ne_nil #[h]
            let va ← ctxValExpr cfg ctx a
            let ha ← ctxValProof cfg ctx a
            let _ := va
            mkAppM ``re_if_true
              #[w, e, reflectSExpr c', reflectSExpr a, reflectSExpr b, vT, va, hc, hcv, ha]
          else
            let hcNil ← mkAppM ``re_val_cast
              #[w, e, reflectSExpr c', vT, mkConst ``SExpr.nil, hc, h]
            let vb ← ctxValExpr cfg ctx b
            let hb ← ctxValProof cfg ctx b
            let _ := vb
            mkAppM ``re_if_false
              #[w, e, reflectSExpr c', reflectSExpr a, reflectSExpr b, vb, hcNil, hb]
        let sel := if sign then a else b
        let acc' ← match acc with
          | none => pure step
          | some p => mkAppM ``fuel_chain_eq #[p, step]
        let (chSel, final) ← collapseEval cfg ctx facts sel
        match chSel with
        | none => return (some acc', final)
        | some m => return (some (← mkAppM ``fuel_chain_eq #[acc', m]), final)
      | none =>
        -- unresolved test: collapse both branches in place
        let (chA, a') ← collapseEval cfg ctx facts a
        if let some ch := chA then
          let st : PathStep := { fn := fs, arity := 3, argIdx := 1, siblings := [c', b] }
          let lifted ← applyStep w e st a a' ch
          acc ← match acc with
            | none => pure (some lifted)
            | some p => pure (some (← mkAppM ``fuel_chain_eq #[p, lifted]))
          cur := .cons (.atom (.symbol fs)) ([c', a', b].foldr .cons .nil)
        let (chB, b') ← collapseEval cfg ctx facts b
        if let some ch := chB then
          let st : PathStep := { fn := fs, arity := 3, argIdx := 2, siblings := [c', a'] }
          let lifted ← applyStep w e st b b' ch
          acc ← match acc with
            | none => pure (some lifted)
            | some p => pure (some (← mkAppM ``fuel_chain_eq #[p, lifted]))
          cur := .cons (.atom (.symbol fs)) ([c', a', b'].foldr .cons .nil)
        let _ := cur
        return (acc, .cons (.atom (.symbol fs)) ([c', a', b'].foldr .cons .nil))
    | _ => throwError "collapseEval: malformed if {repr t}"
  -- generic application: collapse arguments left-to-right, then head folds
  let mut curArgs := args.toArray
  let mut acc : Option Expr := none
  for i in [0:args.length] do
    let a := curArgs[i]!
    let (chA, a') ← collapseEval cfg ctx facts a
    if let some ch := chA then
      let siblings := (curArgs.toList.zipIdx.filterMap fun (x, j) =>
        if j == i then none else some x)
      let st : PathStep := { fn := fs, arity := args.length, argIdx := i, siblings }
      let lifted ← applyStep w e st a a' ch
      acc ← match acc with
        | none => pure (some lifted)
        | some p => pure (some (← mkAppM ``fuel_chain_eq #[p, lifted]))
      curArgs := curArgs.set! i a'
  let cur : SExpr := .cons (.atom (.symbol fs)) (curArgs.toList.foldr .cons .nil)
  -- the POST-COLLAPSE term may be the form an in-scope assumption is about
  -- (argument collapse rebuilt it into another clause literal)
  if let some hNil := ctx.litFactByTerm? cur then
    let pl ← ctxValProof cfg ctx cur
    let pr ← mkAppM ``re_val_quote #[w, e, reflectSExpr SExpr.nil]
    let step ← mkAppM ``fuel_eq_of_conv #[pl, pr, hNil]
    let acc' ← match acc with
      | none => pure step
      | some p => mkAppM ``fuel_chain_eq #[p, step]
    return (some acc', quoteNil)
  -- call-stack folds (the enumerated rule set; extend ONLY with rules
  -- if-interp itself applies — rewrite.lisp:3671-3778)
  let fold? ← do
    if fs.name == "not" then
      match curArgs.toList with
      | [.cons (.atom (.symbol q)) (.cons cc .nil)] =>
        if q.name == "quote" then
          let foldedV : SExpr := if cc == SExpr.nil then SExpr.t else SExpr.nil
          let foldedT : SExpr :=
            .cons (.atom (.symbol { name := "quote" })) (.cons foldedV .nil)
          let pNot ← replayExecGround cfg cur foldedV
          let pQ ← mkAppM ``re_val_quote #[w, e, reflectSExpr foldedV]
          pure (some (← mkAppM ``fuel_eq_of_conv
            #[pNot, pQ, ← mkEqRefl (reflectSExpr foldedV)], foldedT))
        else pure none
      | _ => pure none
    else if fs.name == "equal" then
      match curArgs.toList with
      | [x, y] =>
        if x == y then
          let hX ← proveConv cfg e ctx x
          let hNoEqual ← proveNoShadow cfg { name := "equal" }
          let pEq ← mkAppM ``re_equal_self #[w, e, reflectSExpr x, hX, hNoEqual]
          let pQ ← mkAppM ``re_val_quote #[w, e, reflectSExpr SExpr.t]
          pure (some (← mkAppM ``fuel_eq_of_conv
            #[pEq, pQ, ← mkEqRefl (mkConst ``SExpr.t)], quoteT))
        else pure none
      | _ => pure none
    else pure none
  match fold? with
  | none => return (acc, cur)
  | some (stepPf, next) =>
    let acc' ← match acc with
      | none => pure stepPf
      | some p => mkAppM ``fuel_chain_eq #[p, stepPf]
    return (some acc', next)

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

/-- Run `x` under a REAL heartbeat bound of `n` USER units (×1000 internal).
    `withOptions (maxHeartbeats := …)` is a NO-OP for this purpose —
    `Core.Context.maxHeartbeats` is fixed when the command context is created
    (perf profile P1); this is the toolchain's own idiom (cf. Grind/Canon). -/
def withRealMaxHeartbeats (n : Nat) (x : MetaM α) : MetaM α :=
  withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := n * 1000 }) <|
    Core.withCurrHeartbeats x

/-- The direct attempt's budget where the SPLIT FALLBACK exists
    (`total ≤` the split bound): a pure LATENCY knob, free to tune — on
    timeout the split enumeration still proves everything provable, so this
    constant can never change an OUTCOME, only how fast a failing attempt
    gives up. (Premise, stated honestly: "the split path closes whatever
    the direct path closes" is empirically true for every corpus leaf —
    the pure-split-first run was golden-byte-identical — but not a theorem;
    the golden gate is the corpus tripwire, and for new books the failure
    mode is a LOUD conditional hypothesis, never a wrong verdict.) -/
def dpDirectBudget : Nat := 15000

/-- The direct attempt's budget where it is the ONLY prover (`total >` the
    split bound): OUTCOME-determining, so deliberately NOT a tuned constant —
    a generous runaway guard (~40 s, the same role as the harness's per-leaf
    guards). A true fact needing more than this from the fixed tactic is
    reported as an honest frontier; a corpus-calibrated bar here would
    silently gate FUTURE books' coverage on today's timings. -/
def dpOnlyProverGuard : Nat := 1000000

/-- PROVE the DP fact by the carved-out decision procedure: one BOUNDED run
    of the fixed tactic on the unsplit goal, else a one-level value split
    (policy-bounded) and the fixed tactic per leaf. Hard-fails if any case
    survives. -/
def proveDpFact (stmt : Expr) (total : Nat) : MetaM Expr := do
  -- PRISTINE-CONTEXT (perf profile P6): the fact statement is CLOSED
  -- (∀-quantified over its values), but the caller invokes this inside the
  -- vop/hconv/htp telescopes — and `simp_all` on EVERY split leaf re-churns
  -- those ambient hypotheses (whose types carry the reflected world):
  -- measured 23 s vs 1.7 s for the same statement. Run the whole proof in
  -- an empty local context when the statement is genuinely closed: no
  -- fvars AND no mvars (an unassigned mvar would carry the outer context —
  -- the audit's F2; instantiate first so assigned mvars don't trip it).
  let stmt ← instantiateMVars stmt
  if stmt.hasFVar || stmt.hasMVar then
    proveDpFactCore stmt total
  else
    Meta.withLCtx {} #[] do proveDpFactCore stmt total
where proveDpFactCore (stmt : Expr) (total : Nat) : MetaM Expr := do
  let tac ← dpLeafTactic
  -- BOUNDED-DIRECT-FIRST (perf profile P5 + the 08-equality trade): the
  -- whole-goal simp_all is the fastest path when it works (sub-second on
  -- propositional/equality facts) and catastrophic when it fails UNBOUNDED
  -- (40–860 s measured) — so try it once under a REAL small budget, then
  -- fall back to the case-split enumeration (~30 ms per concrete leaf; a
  -- failing leaf aborts immediately). Splitting is sound case analysis and
  -- each leaf carries strictly more constructor information than the
  -- un-split goal. FIXED policy, not search: one bounded direct attempt;
  -- split ≤ 3 values (≈9 cases each — 9⁴ ≈ 6500 leaves is not a viable
  -- check); past the bound the bounded direct attempt is all there is.
  -- Each attempt uses a FRESH metavariable (a failed attempt may leave its
  -- mvar half-assigned).
  let direct? ←
    withRealMaxHeartbeats (if total ≤ 3 then dpDirectBudget else dpOnlyProverGuard) <|
    tryCatchRuntimeEx
      (try
        let mv ← mkFreshExprMVar stmt
        let (_, g) ← mv.mvarId!.intros
        let remaining ← Lean.Elab.runTactic g tac
        if remaining.1.isEmpty then pure (some (← instantiateMVars mv)) else pure none
      catch _ => pure none)
      (fun _ => pure none)
  if let some p := direct? then return p
  if total > 3 then
    throwError "proveDpFact: the bounded direct tactic failed and {total} \
                quantified values exceed the split bound (3) — DP-fact \
                frontier (fact: {stmt})"
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

/-! ## G3 Fragment A wiring — the consolidated value-layer proof

`DpLiftBundle` carries the REFLECTED `vars`/`opq` lists and the premises of
`dpLiftF_sound`; `dpLiftProof` then certifies any liftable term's
value-characterized convergence by ONE lemma instantiation, the
`dpLiftF … = some v` fact discharged by defeq (D-A5: concrete keys reduce;
symbolic values are carried opaquely). Replaces `dpValProof`'s per-node
proof chains in the discharge path. -/

/-- `∃ N, ∀ f ≥ N, evalOpt f w e t = some v`, term and value as `Expr`s
    (the per-entry premise shape of the bundle). -/
private def mkValConvPropE (w e tE vE : Expr) : MetaM Expr := do
  withLocalDeclD `N (mkConst ``Nat) fun nV => do
    let body ← withLocalDeclD `f (mkConst ``Nat) fun fV => do
      let ge ← mkAppM ``GE.ge #[fV, nV]
      let lhs := mkAppN (mkConst ``evalOpt) #[fV, w, e, tE]
      let rhs := mkApp2 (mkConst ``Option.some [0]) (mkConst ``SExpr) vE
      mkForallFVars #[fV] (← mkArrow ge (← mkEq lhs rhs))
    mkAppM ``Exists #[← mkLambdaFVars #[nV] body]

/-- The reflected lists + premise proofs feeding `dpLiftF_sound`. -/
structure DpLiftBundle where
  varsE : Expr
  hvars : Expr
  opqE : Expr
  hopq : Expr
  hns : Expr

/-- Build the bundle: clause variables ↦ their `dpConcVar` values (premises
    by `re_val_var`), opaques ↦ their pinned values (premises supplied),
    no-shadow by one kernel `decide` on the world. -/
def mkDpLiftBundle (cfg : ReplayConfig) (envExpr : Expr)
    (vars : List Symbol) (opqMap opqP : List (SExpr × Expr)) :
    MetaM DpLiftBundle := do
  let symTy := mkConst ``Symbol
  let sexprTy := mkConst ``SExpr
  -- vars: pair + per-entry re_val_var proof
  let varPairTy ← mkAppM ``Prod #[symTy, sexprTy]
  let varEntries ← vars.mapM fun sym => do
    let vE ← dpConcVar envExpr sym
    let pairE ← mkAppM ``Prod.mk #[reflectSymbol sym, vE]
    let hNotT ← proveIsNamedFalse sym "t"
    let h ← mkAppM ``re_val_var #[cfg.worldExpr, envExpr, reflectSymbol sym, hNotT]
    return (pairE, h)
  let varP ← withLocalDeclD `q varPairTy fun qV => do
    let fst ← mkAppM ``Prod.fst #[qV]
    let snd ← mkAppM ``Prod.snd #[qV]
    let atomE ← mkAppM ``SExpr.atom #[← mkAppM ``Atom.symbol #[fst]]
    mkLambdaFVars #[qV] (← mkValConvPropE cfg.worldExpr envExpr atomE snd)
  let (varsE, hvars) ← mkForallMemProof varPairTy varP varEntries
  -- opq: pair + the supplied convergence proof (zipped by the opaque term)
  let opqPairTy ← mkAppM ``Prod #[sexprTy, sexprTy]
  let opqEntries ← opqMap.mapM fun (op, vE) => do
    let some (_, h) := opqP.find? (fun (o, _) => o == op)
      | throwError "mkDpLiftBundle: opaque {repr op} has a value but no proof"
    let pairE ← mkAppM ``Prod.mk #[reflectSExpr op, vE]
    return (pairE, h)
  let opqProp ← withLocalDeclD `p opqPairTy fun pV => do
    let fst ← mkAppM ``Prod.fst #[pV]
    let snd ← mkAppM ``Prod.snd #[pV]
    mkLambdaFVars #[pV] (← mkValConvPropE cfg.worldExpr envExpr fst snd)
  let (opqE, hopq) ← mkForallMemProof opqPairTy opqProp opqEntries
  -- no-shadow: one decide on the (concrete) world
  let hns ← mkDecideProof (mkApp (mkConst ``dpNoShadow) cfg.worldExpr)
  return { varsE, hvars, opqE, hopq, hns }

/-- Value-characterized convergence of `t` to `vE` by ONE `dpLiftF_sound`
    instantiation; `vE` must be the walker-computed value (`dpValExpr`), and
    the `dpLiftF … = some vE` fact must hold by REDUCTION — a mismatch is a
    hard error naming the term (the consolidated function and the walker
    disagreeing would be a defect, not a recoverable state). -/
def dpLiftProof (cfg : ReplayConfig) (envExpr : Expr) (b : DpLiftBundle)
    (t : SExpr) (vE : Expr) : MetaM Expr := do
  let someV := mkApp2 (mkConst ``Option.some [0]) (mkConst ``SExpr) vE
  let liftApp := mkApp3 (mkConst ``dpLiftF) b.varsE b.opqE (reflectSExpr t)
  unless ← isDefEq liftApp someV do
    throwError "dpLiftProof: dpLiftF does not reduce to the walker's value \
                for {repr t} (function/walker divergence — a defect)"
  let hfact ← mkExpectedTypeHint (← mkEqRefl someV) (← mkEq liftApp someV)
  mkAppM ``dpLiftF_sound
    #[cfg.worldExpr, envExpr, b.varsE, b.opqE, b.hvars, b.hopq, b.hns,
      reflectSExpr t, vE, hfact]

mutual
/-- Fold `evtrue_dp_if_split` over the discharge clause's spine, feeding
    nil-hypotheses to the partially-applied DP fact; result `EvTrue` of the
    spine (G2). The DP FACT itself stays value-level (`concVal = SExpr.t`) —
    only the clause boundary wraps. -/
partial def dischargeSpine (cfg : ReplayConfig) (b : DpLiftBundle)
    (opqMap : List (SExpr × Expr))
    (t : SExpr) (fPartial : Expr) : MetaM Expr := do
  match t with
  | .cons (.atom (.symbol fs)) (.cons c (.cons th (.cons e .nil))) =>
    if fs.name == "if" && th == quoteT then
      let vc ← dpValExpr opqMap (dpConcVar cfg.envExpr) c
      let pc ← dpLiftProof cfg cfg.envExpr b c vc
      -- hthen : vc ≠ nil → EvTrue (quote t)
      let neTy ← mkAppM ``Ne #[vc, mkConst ``SExpr.nil]
      let hthen ← withLocalDeclD `h neTy fun h => do
        let _ := h
        mkLambdaFVars #[h] (← mkAppM ``evtrue_of_eq_t #[← quoteTFact cfg])
      -- helse : vc = nil → EvTrue e   (descend, feeding the hyp to F)
      let fTy ← whnf (← inferType fPartial)
      let .forallE _ dom _ _ := fTy
        | throwError "dischargeSpine: DP fact arity mismatch at {repr c}"
      let helse ← withLocalDeclD `h dom fun h => do
        let p ← dischargeSpine cfg b opqMap e (mkApp fPartial h)
        mkLambdaFVars #[h] p
      mkAppM ``evtrue_dp_if_split
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr c, reflectSExpr th, reflectSExpr e,
          vc, pc, hthen, helse]
    else dischargeClose cfg b opqMap t fPartial
  | _ => dischargeClose cfg b opqMap t fPartial

/-- Close the spine's last literal: cast its value-characterized convergence by
    the DP fact's conclusion `concVal(t) = SExpr.t`, entering `EvTrue` via the
    exact-t injection. -/
partial def dischargeClose (cfg : ReplayConfig) (b : DpLiftBundle)
    (opqMap : List (SExpr × Expr))
    (t : SExpr) (fPartial : Expr) : MetaM Expr := do
  let vt ← dpValExpr opqMap (dpConcVar cfg.envExpr) t
  let pt ← dpLiftProof cfg cfg.envExpr b t vt
  let pExact ← mkAppM ``re_val_cast
    #[cfg.worldExpr, cfg.envExpr, reflectSExpr t, vt, mkConst ``SExpr.t, pt, fPartial]
  mkAppM ``evtrue_of_eq_t #[pExact]
end

/-! ## Totality from admission (#37)

Discharge the driver's `total:fn` hypotheses from the EMITTED admission data:
the justification (measure/wfrel/measured subset) and the RAW termination
clauses (the per-call-site decrease obligations). The body-convergence walk
is CASE-SPLIT style (`conv_if_split`): each `if` branch proceeds under an
explicit `toBool` fact, which is exactly what the decrease discharge consumes
at recursive call sites. Scope (decision log D5): measure
`(acl2-count <single-formal>)` under `o<`; everything else is a named
frontier and the `total:` hypothesis stays in the mirror's type (D6). -/

/-- Is every head of `t` walk-liftable (vars/quote/dp-primitives only)? -/
def totLiftable (t : SExpr) : Bool := (collectOpaques t).isEmpty

/-- The decrease discharge (D5/D7'): prove
    `(value-of callArg).acl2Count < av.acl2Count` from the in-scope branch
    facts, AFTER verifying the EMITTED clause for this call site (its `o<`
    literal mentions exactly `callArg`, and every ruling literal's test has a
    matching in-scope fact). Supported value shape: `callArg = (cdr m)` for
    the measured formal `m` under an in-scope `(consp m) = true` fact. -/
def totDischargeDecrease (just : Justification)
    (measuredFormal : Symbol)
    (facts : List (SExpr × Bool × Expr))
    (callArg : SExpr) : MetaM Expr := do
  -- the emitted obligation for THIS call site
  let countOf (t : SExpr) : SExpr :=
    .cons (.atom (.symbol { name := "acl2-count" })) (.cons t .nil)
  let wanted : SExpr :=
    .cons (.atom (.symbol { name := "o<" }))
      (.cons (countOf callArg)
        (.cons (countOf (.atom (.symbol { name := measuredFormal.name }))) .nil))
  let some clause := just.terminationClauses.find? fun c =>
      match c.toList? with
      | some lits => lits.any (· == wanted)
      | none => false
    | throwError "proveTotality: no emitted decrease obligation for call \
        argument {repr callArg} (emission gap or unsupported call shape)"
  let some lits := clause.toList?
    | throwError "proveTotality: malformed obligation clause {repr clause}"
  -- every ruling literal must be justified by an in-scope branch fact:
  -- (not T) requires fact (T, true); a bare positive literal T requires (T, false)
  for lit in lits do
    if lit == wanted then continue
    match lit with
    | .cons (.atom (.symbol n)) (.cons tst .nil) =>
      if n.name == "not" then
        unless facts.any (fun (f, pos, _) => f == tst && pos) do
          throwError "proveTotality: ruling test {repr tst} not established \
              on this branch (obligation {repr clause})"
      else
        unless facts.any (fun (f, pos, _) => f == lit && !pos) do
          throwError "proveTotality: ruling literal {repr lit} not refuted \
              on this branch (obligation {repr clause})"
    | _ =>
      unless facts.any (fun (f, pos, _) => f == lit && !pos) do
        throwError "proveTotality: ruling literal {repr lit} not refuted \
            on this branch (obligation {repr clause})"
  -- the Lean-side decrease: supported shapes (frontier otherwise)
  match callArg with
  | .cons (.atom (.symbol c)) (.cons (.atom (.symbol m)) .nil) =>
    if c.name == "cdr" && m == measuredFormal then
      let conspTest : SExpr :=
        .cons (.atom (.symbol { name := "consp" }))
          (.cons (.atom (.symbol { name := m.name })) .nil)
      let some (_, _, factPf) := facts.find?
          (fun (f, pos, _) => f == conspTest && pos)
        | throwError "proveTotality: decrease for (cdr {m.name}) needs an \
            in-scope (consp {m.name}) fact (frontier)"
      mkAppM ``ACL2.acl2Count_cdr_lt_of_consp #[factPf]
    else if c.name == "car" && m == measuredFormal then
      let conspTest : SExpr :=
        .cons (.atom (.symbol { name := "consp" }))
          (.cons (.atom (.symbol { name := m.name })) .nil)
      let some (_, _, factPf) := facts.find?
          (fun (f, pos, _) => f == conspTest && pos)
        | throwError "proveTotality: decrease for (car {m.name}) needs an \
            in-scope (consp {m.name}) fact (frontier)"
      mkAppM ``ACL2.acl2Count_car_lt_of_consp #[factPf]
    else
      throwError "proveTotality: decrease shape {repr callArg} unsupported \
          (frontier: cdr/car of the measured formal)"
  | _ =>
    throwError "proveTotality: decrease shape {repr callArg} unsupported \
        (frontier: cdr/car of the measured formal)"

/-- The body-convergence walk: a proof of `∃N∃v ∀f≥N, eval envE t = some v`.
    `vals` carries each formal's VALUE expr and var-convergence proof;
    `facts` the branch context; `totalEnv` earlier functions' totality
    proofs (hypothesis-shaped); `selfC` the recursion data (the IH plus the
    justification whose emitted clauses license its use). -/
partial def totWalk (cfg : ReplayConfig) (envE : Expr)
    (vals : List (Symbol × Expr × Expr))
    (facts : List (SExpr × Bool × Expr))
    (totalEnv : List (String × Nat × Expr))
    (selfC : Option (String × Symbol × Expr × Justification))
    (t : SExpr) : MetaM Expr := do
  let varP : Symbol → Option (Expr × Expr) := fun s =>
    (vals.find? (fun (f, _, _) => f == s)).map (fun (_, v, p) => (v, p))
  if totLiftable t then
    -- vars / quote / dp-primitive tree: value-characterize and ∃-pack
    let pf ← dpValProof cfg envE [] [] varP t
    return ← mkAppM ``conv_ex_of_vfix #[pf]
  match t with
  | .cons (.atom (.symbol fs)) (.cons c (.cons th (.cons e .nil))) =>
    if fs.name == "if" then
      unless totLiftable c do
        throwError "proveTotality: if-test {repr c} is not liftable (frontier)"
      let vc ← dpValExpr [] (dpValProof.dpVarVal envE varP) c
      let hc ← dpValProof cfg envE [] [] varP c
      let toBoolVc ← mkAppM ``Logic.toBool #[vc]
      let tTrue ← mkEq toBoolVc (mkConst ``Bool.true)
      let tFalse ← mkEq toBoolVc (mkConst ``Bool.false)
      let ht ← withLocalDeclD `hb tTrue fun hb => do
        let p ← totWalk cfg envE vals ((c, true, hb) :: facts) totalEnv selfC th
        mkLambdaFVars #[hb] p
      let he ← withLocalDeclD `hb tFalse fun hb => do
        let p ← totWalk cfg envE vals ((c, false, hb) :: facts) totalEnv selfC e
        mkLambdaFVars #[hb] p
      return ← mkAppM ``conv_if_split
        #[cfg.worldExpr, envE, reflectSExpr c, reflectSExpr th, reflectSExpr e,
          vc, hc, ht, he]
    else
      throwError "proveTotality: ternary {fs.name} unsupported (frontier)"
  | .cons (.atom (.symbol fs)) argsSpine =>
    let args := (argsSpine.toList?).getD []
    -- dp-known BUILTIN over non-liftable args (e.g. a self-call inside
    -- binary-+): walk the args and compose in the ∃∃ shape
    if args.length == 1 then
      if let some (fn, cb) := dpUnary.lookup fs.name then
        let pa ← totWalk cfg envE vals facts totalEnv selfC args[0]!
        let hNs ← proveNotSpecial fs
        let hNo ← proveNoShadow cfg fs
        return ← mkAppM ``conv_builtin1_ex
          #[cfg.worldExpr, envE, reflectSymbol fs, reflectSExpr args[0]!,
            mkConst fn, hNs, hNo, mkConst cb, pa]
    if args.length == 2 then
      if let some (fn, cb) := dpBinary.lookup fs.name then
        let pa ← totWalk cfg envE vals facts totalEnv selfC args[0]!
        let pb ← totWalk cfg envE vals facts totalEnv selfC args[1]!
        let hNs ← proveNotSpecial fs
        let hNo ← proveNoShadow cfg fs
        return ← mkAppM ``conv_builtin2_ex
          #[cfg.worldExpr, envE, reflectSymbol fs, reflectSExpr args[0]!,
            reflectSExpr args[1]!, mkConst fn, hNs, hNo, mkConst cb, pa, pb]
    -- SELF-call: the IH, licensed by the emitted decrease obligation
    if let some (selfName, measuredFormal, ih, just) := selfC then
      if fs.name == selfName then
        match cfg.worldVal.defs.get? fs with
        | some (formals, body) =>
          unless args.length == formals.length do
            throwError "proveTotality: self-call arity mismatch {repr t}"
          unless args.all totLiftable do
            throwError "proveTotality: self-call argument not liftable \
                {repr t} (frontier)"
          let argVals ← args.mapM (dpValExpr [] (dpValProof.dpVarVal envE varP))
          let argPfs ← args.mapM (dpValProof cfg envE [] [] varP)
          let mIdx := formals.findIdx (· == measuredFormal)
          unless vals.any (fun (f, _, _) => f == measuredFormal) do
            throwError "proveTotality: measured formal has no bound value"
          let dec ← totDischargeDecrease just measuredFormal facts args[mIdx]!
          let hNs ← proveNotSpecial fs
          let hDef ← totDefFact cfg fs formals body
          match formals, args with
          | [f1], [a1] =>
            let hbody ← mkAppM' ih #[argVals[0]!, dec]
            return ← mkAppM ``conv_defn_1_ex
              #[cfg.worldExpr, envE, reflectSymbol fs, reflectSymbol f1,
                reflectSExpr body, reflectSExpr a1, argVals[0]!, hNs, hDef,
                argPfs[0]!, hbody]
          | [f1, f2], [a1, a2] =>
            -- the IH's binder order follows the MEASURED formal (the strong
            -- induction is on its count; the other formal is inner-∀)
            let hbody ←
              if mIdx == 0 then mkAppM' ih #[argVals[0]!, dec, argVals[1]!]
              else if mIdx == 1 then mkAppM' ih #[argVals[1]!, dec, argVals[0]!]
              else throwError "proveTotality: measured formal not among the \
                               formals (internal)"
            return ← mkAppM ``conv_defn_2_ex
              #[cfg.worldExpr, envE, reflectSymbol fs, reflectSymbol f1,
                reflectSymbol f2, reflectSExpr body, reflectSExpr a1,
                reflectSExpr a2, argVals[0]!, argVals[1]!, hNs, hDef,
                argPfs[0]!, argPfs[1]!, hbody]
          | _, _ =>
            throwError "proveTotality: self-call arity {args.length} \
                unsupported (frontier)"
        | none => throwError "proveTotality: self {fs.name} not in world"
    -- EARLIER defined fn: its accumulated totality proof
    if let some (_, arity, pf) := totalEnv.find? (fun (n, _, _) => n == fs.name) then
      unless args.length == arity do
        throwError "proveTotality: call arity mismatch {repr t}"
      let argPfs ← args.mapM (totWalk cfg envE vals facts totalEnv selfC)
      let argsR := args.map reflectSExpr
      return ← mkAppM' pf (#[envE] ++ argsR.toArray ++ argPfs.toArray)
    throwError "proveTotality: call to {fs.name} with no totality fact \
        in scope (frontier: development-order dependency or unsupported head)"
  | _ => throwError "proveTotality: term shape {repr t} unsupported (frontier)"
where
  /-- `w.defs.get? fn = some (formals, body)` by `decide` on the reflected world. -/
  totDefFact (cfg : ReplayConfig) (fn : Symbol) (formals : List Symbol)
      (body : SExpr) : MetaM Expr := do
    let defsE ← mkAppM ``World.defs #[cfg.worldExpr]
    let lhs ← mkAppM ``DefMap.get? #[defsE, reflectSymbol fn]
    let formalsE ← mkListLit (mkConst ``Symbol) (formals.map reflectSymbol)
    let pairE ← mkAppM ``Prod.mk #[formalsE, reflectSExpr body]
    let rhs ← mkAppM ``Option.some #[pairE]
    mkDecideProof (← mkEq lhs rhs)

/-- Replay a decision-procedure DISCHARGE LEAF standalone: prove the discharge
    node's claim `EvTrue w env (disjoin clause)` (G2),
    CONDITIONAL on, per opaque user-fn subterm: its convergence (totality) and —
    when the development carries one — its emitted type-prescription corollary.
    `tps` maps fn name ↦ corollary (from the parsed `:TYPE-PRESCRIPTION` events).
    Returns the (lambda-abstracted) proof and the list of assumed conditions.
    With `assumeFact`, an unclosable DP fact is NOT sorried: it becomes a further
    bound hypothesis (`hfact : <the fact>`) — the proof is CONDITIONAL, its type
    states the exact missing obligation, no `sorryAx` anywhere. -/
def replayDischargeLeaf (cfg : ReplayConfig) (clauseTerm : SExpr)
    (tps : List (String × SExpr) := []) (assumeFact : Bool := false)
    (totalEnv : List (String × Nat × Expr) := []) :
    MetaM (Expr × List String) := do
  let (tests, last) := dpSpine clauseTerm
  let lits := tests ++ [last]
  let vars := (lits.flatMap ACL2.Replay.freeVars).eraseDups
  let opaques := (lits.flatMap collectOpaques).eraseDups
  -- #37: derive each opaque application's convergence from the admission
  -- totality environment where possible — the leaf then carries NO total:
  -- hypothesis for it (an ∃-elimination consumes the derivation instead)
  let derived : List (Option Expr) ← opaques.mapM fun op =>
    try
      pure (some (← totWalk cfg cfg.envExpr [] [] totalEnv none op))
    catch _ =>
      pure none
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
  -- an opaque's convergence hypothesis is ELIMINABLE only when (a) the
  -- totality environment derives it AND (b) no TP hypothesis mentions its
  -- value (a TP-bearing opaque's value must stay universally bound so the
  -- TP hypothesis can be stated over it — restructuring those to the
  -- fn-level TP shape is a tracked follow-up)
  let eliminable : List Bool := (opaques.zip derived).map fun (op, d?) =>
    d?.isSome && (opCors.find? (fun (o, c?) => o == op && c?.isSome)).isNone
  let conds :=
    ((opaques.zip eliminable).filterMap fun (op, e) =>
      if e then none else some s!"total:{op}") ++
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
        -- close over (vop, hconv) pairs INNER-to-OUTER: a derived opaque's
        -- pair is consumed by exists_conv_elim (its totality derivation);
        -- an underived one stays a λ-bound hypothesis. TP hyps (which may
        -- mention any vop) bind innermost.
        let closeOver (prf0 : Expr) (extra : Array Expr) : MetaM Expr := do
          let mut prf ← mkLambdaFVars (htps ++ extra) prf0
          for i in (List.range opaques.length).reverse do
            match derived[i]!, eliminable[i]! with
            | some tot, true =>
              let k ← mkLambdaFVars #[vops[i]!, hconvs[i]!] prf
              prf ← mkAppM ``exists_conv_elim #[tot, k]
            | _, _ =>
              prf ← mkLambdaFVars #[vops[i]!, hconvs[i]!] prf
          return prf
        let bundle ← mkDpLiftBundle cfg cfg.envExpr vars opqMap opqP
        match fact? with
        | some fact =>
          -- instantiate the fact: concrete var values, opaque value fvars, TP hyps
          let factConc := mkAppN fact (concArgs.toArray ++ vops ++ htps)
          let prf ← dischargeSpine cfg bundle opqMap clauseTerm factConc
          let r ← closeOver prf #[]
          return (r, false)
        | none =>
          withLocalDeclD `hfact stmt fun hFact => do
            let factConc := mkAppN hFact (concArgs.toArray ++ vops ++ htps)
            let prf ← dischargeSpine cfg bundle opqMap clauseTerm factConc
            let r ← closeOver prf #[hFact]
            return (r, true)
  return (p, if assumed then conds ++ ["ASSUMED:dp-fact"] else conds)

/-- COMPOSE a verdict-only discharge node into a clause/preprocess replay: prove
    `EvTrue w env (disjoin clause)` (G2) under the AMBIENT `ReplayCtx` —
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
  let bundle ← mkDpLiftBundle cfg cfg.envExpr vars opqMap opqP
  dischargeSpine cfg bundle opqMap clauseTerm factConc

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
  let .node _ _ _ _ prov := n
  -- a non-EQUAL preprocess rule application must route through the
  -- R-parameterized judgment (the if-iff shape is handled by the chain core;
  -- anything else is the G1 frontier)
  unless prov.equiv == "equal" || prov.origin == "preprocess/if-iff" do
    throwError "replayPreprocessNode: step under equivalence {prov.equiv} — \
                R-parameterized recipe pending (G1 frontier)"
  -- a verdict-only DISCHARGE node routes through the chain core's IFF lane
  -- (D10): its honest content is `EvTrue lhs`, an SIff step to 't — NOT an
  -- eval-equality (that strengthening held only for boolean-valued clauses)
  if dischargeOrigins.contains prov.origin then
    throwError "replayPreprocessNode: discharge node {prov.origin} must \
                compose via the chain core's SIff lane (D10) — direct \
                eval-equality replay is gone"
  match rty with
  | "executable-counterpart" =>
    let .cons (.atom (.symbol q)) (.cons v .nil) := rhs
      | throwError "executable-counterpart: rhs {repr rhs} is not a quoted constant"
    unless q.name == "quote" do
      throwError "executable-counterpart: rhs {repr rhs} is not a quoted constant"
    let convLhs ← replayExecGround cfg lhs v
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

/-- The `PREPROCESS/IF-IFF` node: `(if A 't 'nil) ⇒ A` — IFF-only, NOT
    value-preserving (the chain runs under `*geneqv-iff*`). Returns
    `EvRel SIff w env lhs rhs`. -/
def replayIfIffNode (cfg : ReplayConfig) (ctx : ReplayCtx) (n : ProofNode) :
    MetaM Expr := do
  let (lhs, rhs) := nodeLhsRhs n
  let expectedLhs : SExpr :=
    .cons (.atom (.symbol { name := "if" }))
      (.cons rhs (.cons quoteT (.cons quoteNil .nil)))
  unless lhs == expectedLhs do
    throwError "preprocess/if-iff: lhs {repr lhs} is not (if rhs 't 'nil)"
  let vA ← ctxValExpr cfg ctx rhs
  let pA ← ctxValProof cfg ctx rhs
  mkAppM ``evrel_siff_if_t_nil
    #[cfg.worldExpr, cfg.envExpr, reflectSExpr rhs, vA, pA]

/-- Lift an `EvRel SIff` node proof through ONE position step, per the
    congruence table (G1): if-THEN and if-ELSE positions preserve SIff (the
    untaken branch relates by reflexivity — needs the test's and the other
    branch's convergence); the if-TEST position COLLAPSES SIff to an
    eval-equality (the lazy `if` consults only `toBool`). Returns the lifted
    proof and whether it is still SIff (`true`) or collapsed to Eq (`false`).
    Any other position under an iff payload is a frontier. -/
def applyStepSIff (cfg : ReplayConfig) (ctx : ReplayCtx) (st : PathStep)
    (inner : Expr) : MetaM (Expr × Bool) := do
  unless st.fn.name == "if" && st.arity == 3 do
    throwError "iff congruence: position {st.fn.name}/{st.argIdx} does not \
                propagate IFF (frontier — only if-test/branch positions do)"
  -- a composition that does not typecheck (e.g. a branch-congruence result fed
  -- into a test-collapse — a NESTED conditional structure) is the conditional-
  -- congruence frontier (R1 wall d, deferred — perm-is-an-equivalence); surface
  -- it as a CLEAN named frontier rather than leaking `mkAppM` metavariables.
  -- The original error is PRESERVED in the message: this is still a hard-fail
  -- (never a false pass), but if a FIXABLE bug (wrong sibling/order) — rather
  -- than the genuine wall-d nesting — caused the failure, its text stays visible
  -- so it is not silently misattributed to the deferred frontier.
  let wallD : Exception → MetaM Expr := fun e => do
    throwError "applyStepSIff: SIff branch-congruence composition unsupported for \
      this nesting at if-position {st.argIdx} (conditional-congruence — R1 wall d, \
      deferred); underlying elaboration error: {e.toMessageData}"
  match st.argIdx, st.siblings with
  | 0, [thn, els] =>
    -- TEST position: SIff collapses to eval-equality
    let _ := thn; let _ := els
    let p ← (try mkAppM ``evrel_if_test_siff_collapse #[inner] catch e => wallD e)
    return (p, false)
  | 1, [c, els] =>
    -- THEN position
    let pc ← ctxValProof cfg ctx c
    let pels ← ctxValProof cfg ctx els
    let p ← (try mkAppM ``evrel_if_then_congr #[mkConst ``siff_refl, pc, pels, inner]
             catch e => wallD e)
    return (p, true)
  | 2, [c, thn] =>
    -- ELSE position
    let pc ← ctxValProof cfg ctx c
    let pthn ← ctxValProof cfg ctx thn
    let p ← (try mkAppM ``evrel_if_else_congr #[mkConst ``siff_refl, pc, pthn, inner]
             catch e => wallD e)
    return (p, true)
  | _, _ => throwError "iff congruence: bad if position {st.argIdx}"

/-- Replay a preprocess chain's CORE: the composed relation between the
    formula and the final term — `(proof, isIff)` where the proof is the
    eval-equality `∃N∀f≥N, eval formula = eval final` when `isIff = false`,
    and `EvRel SIff w env formula final` when any step was IFF-only
    (`isIff = true`). `none` for an empty chain. R is threaded per the
    binding invariant L2: equal steps inject into the iff composite by
    refinement (`evrel_of_fuel_eq` + `siff_refl`). -/
def replayPreprocessChainCore (cfg : ReplayConfig) (ctx : ReplayCtx)
    (formula : SExpr) (nodes : List ProofNode) :
    MetaM (Option (Expr × Bool) × SExpr) := do
  let mut cur := formula
  let mut acc : Option (Expr × Bool) := none
  for n in nodes do
    let (lhs, rhs) := nodeLhsRhs n
    let .node _ _ _ _ prov := n
    -- D10: a verdict-only discharge node is an SIff step `lhs ~iff~ 't`
    -- (its honest content is `EvTrue lhs`); if-iff nodes stay; everything
    -- else is an eval-equality step
    let isDischarge := dischargeOrigins.contains prov.origin
    let isIffNode := prov.origin == "preprocess/if-iff" || isDischarge
    let nodeP ←
      if isDischarge then do
        unless rhs == quoteT do
          throwError "discharge node: rhs {repr rhs} ≠ (quote t)"
        let ev ← replayDischargeNode cfg ctx lhs
        mkAppM ``evrel_siff_qt_of_evtrue #[ev]
      else if isIffNode then replayIfIffNode cfg ctx n
      else replayPreprocessNode cfg ctx n
    let path ← match findOccurrences cur lhs with
      | [p] => pure p
      | [] => throwError "replayPreprocessChain: node lhs {repr lhs} does not occur \
                          in the current term {repr cur}"
      | ps => throwError "replayPreprocessChain: node lhs {repr lhs} occurs \
                          {ps.length} times in {repr cur} — ambiguous position \
                          (needs :PATH emission at the preprocess site)"
    -- lift innermost-out; iff payloads use the R congruence table and may
    -- COLLAPSE to an eval-equality at an if-test position
    let mut inner := nodeP
    let mut innerIff := isIffNode
    let mut curL := lhs
    let mut curR := rhs
    for st in path.reverse do
      if innerIff then
        let (p, stillIff) ← applyStepSIff cfg ctx st inner
        inner := p
        innerIff := stillIff
      else
        inner ← applyStep cfg.worldExpr cfg.envExpr st curL curR inner
      curL := rebuild st.fn st.arity st.argIdx curL st.siblings
      curR := rebuild st.fn st.arity st.argIdx curR st.siblings
    unless curL == cur do
      throwError "replayPreprocessChain: reconstructed {repr curL} ≠ current {repr cur}"
    -- compose
    acc := some (← match acc, innerIff with
      | none, _ => pure (inner, innerIff)
      | some (a, false), false =>
        return (← mkAppM ``fuel_chain_eq #[a, inner], false)
      | some (a, aIff), _ => do
        -- iff composite: inject any eval-equality side via refinement
        let aS ← if aIff then pure a else do
          let pConv ← ctxValProof cfg ctx curL
          mkAppM ``evrel_of_fuel_eq #[mkConst ``siff_refl, a, pConv]
        let iS ← if innerIff then pure inner else do
          let pConv ← ctxValProof cfg ctx curR
          mkAppM ``evrel_of_fuel_eq #[mkConst ``siff_refl, inner, pConv]
        return (← mkAppM ``evrel_trans #[mkConst ``siff_trans, aS, iS], true))
    cur := curR
  return (acc, cur)

/-- Replay a clause discharged ENTIRELY by a preprocess chain: the step nodes
    compose the single-literal clause's formula to `(quote t)`. Returns
    `EvTrue w env formula` — an IFF chain ends by backward truth transport
    with NO boolean-valuedness side condition (the G1-interim
    `strengthenIffChain`/`formulaBooleanFact` pair is gone, G2). -/
def replayPreprocessChain (cfg : ReplayConfig) (ctx : ReplayCtx)
    (formula : SExpr) (nodes : List ProofNode) : MetaM Expr := do
  let (acc, cur) ← replayPreprocessChainCore cfg ctx formula nodes
  unless cur == quoteT do
    throwError "replayPreprocessChain: chain ended at {repr cur}, expected (quote t)"
  let some (chain, isIff) := acc
    | throwError "replayPreprocessChain: no step nodes"
  if isIff then
    let pEnd ← mkAppM ``evtrue_of_eq_t #[← quoteTFact cfg]
    mkAppM ``evtrue_of_evrel_siff #[chain, pEnd]
  else
    let hq ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr SExpr.t]
    mkAppM ``evtrue_of_eq_t #[← mkAppM ``fuel_conv_of_eq #[chain, hq]]

/-! ## The clausify BRIDGE (#53C): proved child clause → the clausify input

`bridgeClausify` proves `EvTrue w env input` from the PROVED output
clause (`EvTrue w env (disjoinTerm cl)` — the pool-root/child replay), by
mirroring `clausify-input1`'s PURE if-recursion. The recorded checkpoints
validate every joint (recomputed neg-clause/split/out must equal the record;
an `expand-and-or` marker is a frontier — that expansion is ens-dependent and
not recomputable). Mechanism (G3
Fragment B): ONE `clausifyPure_sound` instantiation — the once-proved bridge
lemma over the pure recursion — replaces the per-leaf peel/walk proof
construction entirely; its premises are the Fragment-A bundle, the input's
lift fact (by reduction), and the opaque-key well-formedness (by kernel
decision). -/

/-- Bridge a clausify record: prove `EvTrue w env info.input` from
    `pOut : EvTrue w env (disjoinTerm cl₀)` (the proved single output clause).
    Validates the WHOLE record against the pure recomputation; any divergence
    (an `expand-and-or` expansion, a structured neg-clause, multiple outputs)
    is a hard frontier error. -/
def bridgeClausify (cfg : ReplayConfig) (ctx : ReplayCtx) (info : ClausifyInfo)
    (pOut : Expr) : MetaM Expr := do
  -- An `expand-and-or` marker (ens-dependent expansion, e.g. a `not` unfold
  -- under a test) is NOT a hard frontier by itself: the expansions ACL2
  -- applies during the walk often ROUND-TRIP (the if-lifting + negation
  -- folding restore the literal form), and every joint below is validated
  -- against the pure recomputation — a genuinely diverging expansion still
  -- fail-closes at the neg/split/out checks.
  let negRecomputed := clausifyPure info.input false
  unless negRecomputed == info.negClause do
    throwError "clausify bridge: recomputed neg-clause {repr negRecomputed} ≠ \
                recorded {repr info.negClause} (divergence: expand-and-or, \
                disjoin-clauses literal merging, or an unmirrored \
                dumb-negate-lit arm)"
  let [l0] := info.negClause
    | throwError "clausify bridge: structured (multi-literal) neg-clause — \
                  frontier: {repr info.negClause}"
  let [(splitLit, cl0)] := info.splits
    | throwError "clausify bridge: expected exactly one split (frontier)"
  unless splitLit == dumbNegateLit l0 do
    throwError "clausify bridge: split literal {repr splitLit} ≠ \
                (dumb-negate {repr l0})"
  unless dumbNegateLit l0 == info.input do
    throwError "clausify bridge: negation round-trip {repr (dumbNegateLit l0)} ≠ \
                input {repr info.input} (frontier)"
  unless clausifyPure info.input true == cl0 do
    throwError "clausify bridge: recomputed split clause \
                {repr (clausifyPure info.input true)} ≠ recorded {repr cl0} \
                (divergence: expand-and-or, disjoin-clauses literal merging, \
                or an unmirrored dumb-negate-lit arm)"
  unless info.out == [cl0] do
    throwError "clausify bridge: output set {repr info.out} ≠ [the split clause] \
                (multi-clause output — frontier)"
  -- G3 Fragment B: ONE clausifyPure_sound instantiation (the validation
  -- above is unchanged — stage-(b) recompute-and-validate).
  let vars := (ACL2.Replay.freeVars info.input).eraseDups
  let opaques := (collectOpaques info.input).eraseDups
  let pinned ← opaques.mapM fun op => do
    let some (v, p) := ctx.val? op
      | throwError "bridgeClausify: opaque {repr op} has no pinned value \
                    (frontier)"
    pure (op, v, p)
  let opqMap := pinned.map fun (op, v, _) => (op, v)
  let opqP := pinned.map fun (op, _, p) => (op, p)
  let b ← mkDpLiftBundle cfg cfg.envExpr vars opqMap opqP
  let vE ← dpValExpr opqMap (dpConcVar cfg.envExpr) info.input
  let someV := mkApp2 (mkConst ``Option.some [0]) (mkConst ``SExpr) vE
  let liftApp := mkApp3 (mkConst ``dpLiftF) b.varsE b.opqE
    (reflectSExpr info.input)
  unless ← isDefEq liftApp someV do
    throwError "bridgeClausify: the input does not lift to the walker's \
                value for {repr info.input} (function/walker divergence — \
                a defect)"
  let isSomeApp ← mkAppM ``Option.isSome #[liftApp]
  let hisSome ← mkExpectedTypeHint (← mkEqRefl (mkConst ``Bool.true))
    (← mkEq isSomeApp (mkConst ``Bool.true))
  let hwf ← mkDecideProof
    (← mkEq (mkApp (mkConst ``dpOpqWF) b.opqE) (mkConst ``Bool.true))
  let prf ← mkAppM ``clausifyPure_sound
    #[cfg.worldExpr, cfg.envExpr, b.hvars, b.hopq, b.hns, hwf,
      reflectSExpr info.input, mkConst ``Bool.true, hisSome, pOut]
  -- `ClausifyGoal … true` IS `EvTrue …` definitionally; cast for consumers
  mkExpectedTypeHint prf
    (← mkAppM ``EvTrue #[cfg.worldExpr, cfg.envExpr, reflectSExpr info.input])

/-! ## The c3 induction scaffold + the conditional-mirror harness

The WF-induction scaffold consumes the EMITTED justification (measure / rel /
controllers / per-case tests + IH substitutions — the measure-emission track's
output) and instantiates `acl2_induction_consp` (strong induction on
`SExpr.acl2Count` — the well-foundedness construction Lean owns; everything else
is read off the tree). Case children are SELF-CONTAINED clause proofs (the spine's
split is the case hypothesis); the scaffold only peels the case literals
(`evtrue_extract_else`) and bridges the IH (`evalOpt_substTerm_subst1`).

Opaque user-fn values are PINNED from the bound totality hypotheses (`pinVal` —
choice-based, no Exists.elim plumbing), refined to int-atom shape when the fn's
emitted `:TYPE-PRESCRIPTION` corollary has the standard `(IF (INTEGERP …) … 'NIL)`
shape. The hypotheses themselves are machine-generated from the development
(`replayProofConditional`) — the c2 conditional-proof pattern: the obligations are
explicit in the returned proof's type, reported as conditions. -/

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

/-- The theorem-dependency hypothesis TYPE for a STORED rewrite rule
    (`rule:<thm>`, the `equal` instance — the rule's own `:EQUIV`; a
    non-`equal` rule is a frontier at the USE site, `replayNode`):
    `∀ env', EvTrue w env' h₁ → … → ∃N ∀f≥N, eval env' lhs = eval env' rhs`.
    The premises are TRUTHINESS (ACL2 relieves hyps under iff), the conclusion
    the rule's stored equality — exactly the emitted rule, nothing else
    (docs/plans/2026-07-05_theorem-dependency-hypotheses.md §v1). -/
def mkRuleHypType (cfg : ReplayConfig) (spec : RuleSpec) : MetaM Expr := do
  -- defense-in-depth (audit 2026-07-06 finding E): the caller offers only
  -- equal-class rules; stating an iff rule as an eval-EQUALITY would be too
  -- strong, so refuse rather than mis-state.
  unless spec.equiv == "equal" do
    throwError "mkRuleHypType: rule {spec.name} is stored under equivalence \
                {spec.equiv} — the R-parameterized hypothesis shape is an L2 \
                frontier (equal instance only)"
  withLocalDeclD `env' (mkConst ``ACL2.Env) fun envV => do
    let concl ← mkEvalEqPropEx cfg.worldExpr envV
      (reflectSExpr spec.lhs) (reflectSExpr spec.rhs)
    let body ← spec.hyps.foldrM (fun h acc => do
      mkArrow (mkAppN (mkConst ``EvTrue) #[cfg.worldExpr, envV, reflectSExpr h]) acc)
      concl
    mkForallFVars #[envV] body

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

/-- The decision tree recovered from the cases' ruling-test lists (ACL2's
    induction machine derives the cases from the scheme function's
    if-structure, so the test lists always form a binary split tree). Leaves
    carry the case INDEX into `ind.cases`. -/
private inductive CaseTree where
  | leaf (caseIdx : Nat)
  | split (test : SExpr) (pos neg : CaseTree)
  deriving Repr

/-- Recover the decision tree. Each input is `(caseIdx, remaining tests)`;
    at each level all nonempty heads must be the same test up to negation.
    Hard-fails on anything else (no inference — the structure is validated,
    never guessed). -/
private partial def buildCaseTree (cases : List (Nat × List SExpr)) :
    Except String CaseTree := do
  match cases with
  | [] => throw "buildCaseTree: empty case set"
  | [(i, [])] => return .leaf i
  | _ =>
    let some (_, t0 :: _) := cases.find? (fun (_, ts) => !ts.isEmpty)
      | throw "buildCaseTree: multiple cases left but no remaining tests \
               (overlapping case tests?)"
    -- the split test, positive form: strip a leading not
    let test := match t0 with
      | .cons (.atom (.symbol ns)) (.cons u .nil) =>
        if ns.name == "not" then u else t0
      | _ => t0
    let negT := dumbNegateLit test
    let mut pos : List (Nat × List SExpr) := []
    let mut neg : List (Nat × List SExpr) := []
    for (i, ts) in cases do
      match ts with
      | h :: rest =>
        if h == test then pos := pos ++ [(i, rest)]
        else if h == negT then neg := neg ++ [(i, rest)]
        else throw s!"buildCaseTree: case head {repr h} is neither {repr test} \
                      nor its negation (non-tree case structure, frontier)"
      | [] => throw "buildCaseTree: a case ran out of tests while siblings \
                     remain (subsumed case, frontier)"
    if pos.isEmpty || neg.isEmpty then
      throw s!"buildCaseTree: one-sided split on {repr test} (non-exhaustive \
               case structure, frontier)"
    return .split test (← buildCaseTree pos) (← buildCaseTree neg)

/-- An in-scope ruling-test fact at a decision-tree position: the test term,
    its walked value `Expr`, the value-convergence proof, and the sign
    hypothesis (`sign = true` ⇒ `signE : valueE ≠ nil`; `sign = false` ⇒
    `signE : valueE = nil`). -/
private structure TestFact where
  test : SExpr
  valueE : Expr
  convE : Expr
  sign : Bool
  signE : Expr

/-- The destructor-elimination substitution: replace `(car v) ↦ v1`,
    `(cdr v) ↦ v2`, then remaining bare `v ↦ (cons v1 v2)` — quote-protected,
    mirroring ACL2's elim rewrite (the recomputation `replayElim` validates
    the emitted output clause against). -/
partial def elimReplace (carT cdrT vT uT : SExpr) (v1 v2 : Symbol) (t : SExpr) : SExpr :=
  if t == carT then .atom (.symbol v1)
  else if t == cdrT then .atom (.symbol v2)
  else if t == vT then uT
  else match t with
    | .cons (.atom (.symbol q)) rest =>
      if q.isNamed "quote" then t
      else .cons (.atom (.symbol q)) (elimSpine rest)
    | _ => t
where
  elimSpine : SExpr → SExpr
    | .cons a rest => .cons (elimReplace carT cdrT vT uT v1 v2 a) (elimSpine rest)
    | t => t

mutual

/-- Replay a clause as its LITERAL SPINE: prove `EvTrue w env (disjoinTerm
    clauseLits)`. Items are walked STRUCTURALLY: each non-closing literal is
    followed by its case BRANCHES (`.branch seg items` — the clause scan
    continues INSIDE them). A literal with a trivial clausify trace (no
    split-verdict tests) has exactly one branch, the plain continuation,
    entered via `evtrue_dp_if_split` (truth closes the clause; falsity
    descends with the value fact in `ctx.litFacts`). A literal whose trace
    SPLITS enters `composeSplit` (the W3 assume-true-false composer).
    `accClause` mirrors ACL2's `new-clause` (surviving segment literals, for
    residual-child matching); `children` are the clause node's pushed
    subgoals. -/
partial def replayClauseSpine (cfg : ReplayConfig) (ctx : ReplayCtx) (idStr : String)
    (clauseLits : List (Nat × SExpr)) (items : List ClauseItem)
    (accClause : List SExpr) (children : List ClauseNode) :
    MetaM Expr := do
  match items with
  | [] => throwError "replayClauseSpine: ran out of items with no closer \
                      at {idStr}"
  | .clausify _ :: _ =>
    throwError "replayClauseSpine: clausify record in the spine at {idStr} \
                (frontier)"
  | .step n :: rest =>
    -- a :CONTEXT-SUBST decoration (clausify-branch segment hypothesis): its
    -- equation is consumed by solidify `.segment` nodes from the in-scope
    -- segFacts — no separate proof obligation here
    if (runeOf n).1 == "context-subst" then
      return ← replayClauseSpine cfg ctx idStr clauseLits rest accClause children
    -- a :BRANCH-SUBSTITUTION (remove-trivial-equivalences): ACL2 substitutes
    -- `var := val` THROUGHOUT the clause, justified by the clause's own
    -- `(not (equal var val))` literal, and scans the SUBSTITUTED literals.
    -- Mirror: byCases on that literal's value — truthy closes the clause;
    -- nil gives the value equality, `diffCollapse` transports the whole
    -- disjunction to the substituted clause, and the walk continues there.
    if (runeOf n).1 == "branch-substitution" then
      let .node _ varT valT _ prov := n
      -- :EQUIVALENCE is the RELATION name; only `equal` is supported
      unless prov.equivTerm == some (.atom (.symbol { name := "equal" })) do
        throwError "replayClauseSpine: branch-substitution under equivalence \
                    {repr prov.equivTerm} at {idStr} (frontier — equal only)"
      let .atom (.symbol varSym) := varT
        | throwError "replayClauseSpine: branch-substitution variable \
                      {repr varT} is not a variable at {idStr}"
      -- the justifying clause literal `(not (equal … …))`, either orientation
      let mkNegEq (x y : SExpr) : SExpr :=
        .cons (.atom (.symbol { name := "not" }))
          (.cons (.cons (.atom (.symbol { name := "equal" }))
            (.cons x (.cons y .nil))) .nil)
      let ((ta, tb), kIdx) ←
        match clauseLits.find? (fun (_, l) => l == mkNegEq varT valT) with
        | some (i, _) => pure ((varT, valT), i)
        | none =>
          match clauseLits.find? (fun (_, l) => l == mkNegEq valT varT) with
          | some (i, _) => pure ((valT, varT), i)
          | none =>
            throwError "replayClauseSpine: branch-substitution literal \
                        (not (equal {repr varT} {repr valT})) is not in the \
                        clause at {idStr}"
      let negEq : SExpr := mkNegEq ta tb
      let mut ctx := ctx
      ctx ← pinTermOpaques cfg cfg.envExpr ctx valT
      let vK ← ctxValExpr cfg ctx negEq
      let pK ← ctxValProof cfg ctx negEq
      let nilC := mkConst ``SExpr.nil
      let negL ← withLocalDeclD `hnil (← mkEq vK nilC) fun hNil => do
        let va ← ctxValExpr cfg ctx ta
        let vb ← ctxValExpr cfg ctx tb
        let hEq ← mkAppM ``logic_not_equal_nil_eq #[va, vb, hNil]  -- va = vb
        -- orient var ⇒ val
        let hVeq ← if ta == varT then pure hEq else mkAppM ``Eq.symm #[hEq]
        let pVar ← ctxValProof cfg ctx varT
        let pVal ← ctxValProof cfg ctx valT
        let nodeEq ← mkAppM ``fuel_eq_of_conv #[pVar, pVal, hVeq]
        let substLits := clauseLits.map fun (i, l) =>
          (i, ACL2.Replay.substTerm [varSym] [valT] l)
        -- the SUBSTITUTED literals are new terms — pin their user-fn opaques
        -- before any value construction over them
        let ctx ← pinTermOpaques cfg cfg.envExpr ctx
          (disjoinTerm (substLits.map (·.2)))
        let chainOpt ← diffCollapse cfg.worldExpr cfg.envExpr varT valT nodeEq
          (disjoinTerm (clauseLits.map (·.2))) (disjoinTerm (substLits.map (·.2)))
        -- remove-trivial-equivalences also DELETES the used literal — now the
        -- trivial `(not (equal v v))` — from the clause it scans; collapse its
        -- if-frame out of the disjunction (its value is nil by reflexivity)
        let kPos := clauseLits.findIdx (fun (i, _) => i == kIdx)
        unless kPos + 1 < clauseLits.length do
          throwError "replayClauseSpine: branch-substitution literal is the \
                      clause's LAST literal at {idStr} (frontier)"
        let shortened := (substLits.eraseIdx kPos).zipIdx.map fun ((_, l), j) =>
          (j + 1, l)
        let some (_, trivLit) := substLits[kPos]?
          | throwError "replayClauseSpine: internal — kPos out of range"
        let .cons _ (.cons trivEq .nil) := trivLit
          | throwError "replayClauseSpine: substituted equality literal \
                        {repr trivLit} is not (not …) at {idStr}"
        let .cons _ (.cons tx (.cons ty .nil)) := trivEq
          | throwError "replayClauseSpine: substituted equality \
                        {repr trivEq} shape at {idStr}"
        unless tx == ty do
          throwError "replayClauseSpine: substituted equality {repr trivEq} \
                      is not reflexive at {idStr}"
        let vx ← ctxValExpr cfg ctx tx
        let hEqT ← mkAppM ``Logic.equal_self #[vx]
        let hNotNil ← mkAppM ``Eq.trans
          #[← mkAppM ``congrArg #[mkConst ``Logic.not, hEqT],
            mkConst ``logic_not_t_nil]
        let pTriv ← ctxValProof cfg ctx trivLit
        let hcNil ← mkAppM ``re_val_cast
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr trivLit,
            ← ctxValExpr cfg ctx trivLit, nilC, pTriv, hNotNil]
        -- (if triv 't tail) ≡ tail, lifted through the k-1 else-descents
        let tailLits := (substLits.drop (kPos + 1)).map (·.2)
        let tailTerm := disjoinTerm tailLits
        let vTail ← ctxValExpr cfg ctx tailTerm
        let hTail ← ctxValProof cfg ctx tailTerm
        let _ := vTail
        let mut inner ← mkAppM ``re_if_false
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr trivLit, reflectSExpr quoteT,
            reflectSExpr tailTerm, vTail, hcNil, hTail]
        let mut curL : SExpr := .cons (.atom (.symbol { name := "if" }))
          (.cons trivLit (.cons quoteT (.cons tailTerm .nil)))
        let mut curR : SExpr := tailTerm
        for (_, l) in (substLits.take kPos).reverse do
          let st : PathStep := { fn := { name := "if" }, arity := 3, argIdx := 2,
                                 siblings := [l, quoteT] }
          inner ← applyStep cfg.worldExpr cfg.envExpr st curL curR inner
          curL := rebuild st.fn st.arity st.argIdx curL st.siblings
          curR := rebuild st.fn st.arity st.argIdx curR st.siblings
        unless curL == disjoinTerm (substLits.map (·.2)) &&
               curR == disjoinTerm (shortened.map (·.2)) do
          throwError "replayClauseSpine: branch-substitution shortening lift \
                      reconstructed {repr curL} / {repr curR} at {idStr}"
        let chainAll ← match chainOpt with
          | none => pure inner
          | some ch => mkAppM ``fuel_chain_eq #[ch, inner]
        let pRest ← replayClauseSpine cfg ctx idStr shortened rest accClause children
        let p ← mkAppM ``evtrue_of_fuel_eq #[chainAll, pRest]
        mkLambdaFVars #[hNil] p
      let posL ← withLocalDeclD `hne (← mkAppM ``Ne #[vK, nilC]) fun hNe => do
        let p ← evtrueOfLitTrue cfg ctx (clauseLits.map (·.2)) (kIdx - 1) negEq hNe
        mkLambdaFVars #[hNe] p
      let _ := pK
      return ← mkAppM ``Classical.byCases #[negL, posL]
    throwError "replayClauseSpine: clause-level step item (rune \
                {repr (runeOf n)}) in the spine at {idStr} (frontier)"
  | .branch seg _ :: _ =>
    throwError "replayClauseSpine: branch item with no preceding literal at \
                {idStr} (frontier): segment {repr seg}"
  | .literal lp :: rest =>
    -- this literal's case branches. Clause-level steps emitted BETWEEN the
    -- literal and a `┌ branch` (rewrite-clause emits each new clause's
    -- post-split steps — remove-trivial-equivalences, its evaluations —
    -- before that clause's BEGIN-BRANCH) belong to the FOLLOWING branch's
    -- continuation: regroup each maximal `.step` run into the next branch.
    -- Nothing else may follow at this level; trailing steps with no branch
    -- hard-fail.
    let rec regroup : List ClauseItem → Except String (List (SExpr × List ClauseItem))
      | [] => pure []
      | items => do
        let pre := items.takeWhile (fun | .step _ => true | _ => false)
        match items.drop pre.length with
        | .branch seg its :: tail => pure ((seg, pre ++ its) :: (← regroup tail))
        | [] => throw s!"replayClauseSpine: {pre.length} clause-level step(s) \
                         after literal {lp.index} with no following branch at \
                         {idStr} (frontier)"
        | it :: _ =>
          let tag := match it with
            | .literal l => s!"literal {l.index}"
            | .clausify _ => "clausify"
            | _ => "step"
          throw s!"replayClauseSpine: non-branch item ({tag}) after literal \
                   {lp.index}'s branches at {idStr} (frontier)"
    let branchSegs ← ofExcept (regroup rest)
    let idx := lp.index
    let (cidx, clit) :: restLits := clauseLits
      | throwError "replayClauseSpine: literal item {idx} beyond the clause's \
                    literals at {idStr} (item/clause walk divergence)"
    unless idx == cidx && lp.literal == clit do
      -- a SKIPPED literal whose falsity is already an in-scope hypothesis —
      -- chiefly a DUPLICATE (ACL2's add-literal drops a literal identical to
      -- an earlier one; branch-substitution creates these), but sound for
      -- ANY literal with a genuine falsity fact: collapsing its if-frame by
      -- the fact preserves the disjunction. A spurious fire (e.g. on a
      -- hoisted later-literal fact) misaligns the walk and hard-fails
      -- downstream — never a wrong proof (audit 2026-07-06).
      if lp.literal != clit then
        if let some hNil := ctx.litFactByTerm? clit then
          let restTerm := disjoinTerm (restLits.map (·.2))
          let vC ← ctxValExpr cfg ctx clit
          let pC ← ctxValProof cfg ctx clit
          let hcNil ← mkAppM ``re_val_cast
            #[cfg.worldExpr, cfg.envExpr, reflectSExpr clit, vC,
              mkConst ``SExpr.nil, pC, hNil]
          let hRest ← ctxValProof cfg ctx restTerm
          let vRest ← ctxValExpr cfg ctx restTerm
          let hIf ← mkAppM ``re_if_false
            #[cfg.worldExpr, cfg.envExpr, reflectSExpr clit, reflectSExpr quoteT,
              reflectSExpr restTerm, vRest, hcNil, hRest]
          let restLits' := restLits.map fun (i, l) => (i - 1, l)
          let p ← replayClauseSpine cfg ctx idStr restLits' items accClause children
          return ← mkAppM ``evtrue_of_fuel_eq #[hIf, p]
      throwError "replayClauseSpine: literal item {idx} {repr lp.literal} does \
                  not walk the clause at {idStr} (next clause literal is {cidx} \
                  {repr clit})"
    -- HOIST later-literal facts demanded by SILENT hyp reliefs in this
    -- literal's chain (the emitted relieve-hyp/* markers): ACL2 rewrites
    -- literal i under the falsity of ALL other clause literals, but the walk
    -- holds only the earlier ones. For each marker hyp whose complement IS a
    -- later clause literal with no fact in scope, case-split on that literal
    -- FIRST — its truth closes the whole disjunction; its falsity joins
    -- litFacts and the walk re-enters (one fewer demand each time).
    let demanded := (lp.nodes.flatMap collectContextDemands).eraseDups
    for notH in demanded do
      if (ctx.litFactByTerm? notH).isSome then continue
      let some (k, _) := restLits.find? (fun (_, l) => l == notH)
        | continue  -- not a later literal: the consumer fails precisely if missing
      let ctx ← pinTermOpaques cfg cfg.envExpr ctx notH
      let vL ← ctxValExpr cfg ctx notH
      let pL ← ctxValProof cfg ctx notH
      let _ := pL
      let nilC := mkConst ``SExpr.nil
      let allLits := clauseLits.map (·.2)
      let some pos := clauseLits.findIdx? (fun (i, _) => i == k)
        | throwError "replayClauseSpine: internal — hoisted literal {k} not \
                      in the clause at {idStr}"
      let negL ← withLocalDeclD `hnil (← mkEq vL nilC) fun hNil => do
        let ctx' := { ctx with litFacts := ctx.litFacts ++ [(k, notH, hNil)] }
        let p ← replayClauseSpine cfg ctx' idStr clauseLits items accClause children
        mkLambdaFVars #[hNil] p
      let posL ← withLocalDeclD `hne (← mkAppM ``Ne #[vL, nilC]) fun hNe => do
        let p ← evtrueOfLitTrue cfg ctx allLits pos notH hNe
        mkLambdaFVars #[hNe] p
      return ← mkAppM ``Classical.byCases #[negL, posL]
    if lp.result == quoteT then
      -- the closer: its chain proves it `t`; any later literals (scanned or
      -- not) are short-circuited by the true test.
      unless branchSegs.isEmpty do
        throwError "replayClauseSpine: branches after the closing literal \
                    {idx} at {idStr} (frontier)"
      let pclose ← replayLiteral cfg ctx lp
      if restLits.isEmpty then
        mkAppM ``evtrue_of_eq_t #[pclose]
      else
        -- `(if litᵢ 't rest)` with the test KNOWN `t`
        let restTerm := disjoinTerm (restLits.map (·.2))
        let hq ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr SExpr.t]
        let hcv ← proveByDecide
          (← mkEq (mkApp (mkConst ``Logic.toBool) (mkConst ``SExpr.t)) (mkConst ``Bool.true))
          "toBool t"
        let hIf ← mkAppM ``conv_if_true
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr lp.literal, reflectSExpr quoteT,
            reflectSExpr restTerm, mkConst ``SExpr.t, mkConst ``SExpr.t, pclose, hcv, hq]
        mkAppM ``evtrue_of_eq_t #[hIf]
    else
      -- the literal's rewrite chain: literal ⇒ result
      let (chainOpt, finalT) ← replayLiteralChain cfg ctx lp
      unless finalT == lp.result do
        throwError "replayClauseSpine: literal {idx} chain reached {repr finalT} \
                    at {idStr}, recorded result is {repr lp.result}"
      -- does the clausify decision trace SPLIT?
      let hasSplit := lp.splitTrace.any fun
        | .test _ v _ _ => v == "split"
        | _ => false
      if hasSplit then
        -- W3: the assume-true-false composer. Post-pass reshaping (the
        -- Satriani REPLACEMENT, the subsumption loop) is transparent to the
        -- LEAF-driven composer: branch selection is by derivable segment
        -- falsity with a uniqueness requirement, so a redistributed literal
        -- set still links each leaf to its branch, and a missing or
        -- ambiguous link fails closed at selection. A SUBSUMED-dropped new
        -- clause leaves its leaf unlinkable — still a clean failure there.
        unless lp.splitReshaped.all
            (fun r => r == "satriani-replaced" || r == "subsumption-loop") do
          throwError "replayClauseSpine: literal {idx}'s segment set was \
                      reshaped ({lp.splitReshaped}) at {idStr} (frontier)"
        let (tree, restTrace) ← ofExcept (parseTraceTree [] lp.splitTrace)
        unless restTrace.isEmpty do
          throwError "replayClauseSpine: trailing decision-trace events on \
                      literal {idx} at {idStr}: {repr restTrace.head?}"
        -- pin the trace leaf values' opaques (collapse intermediates live
        -- inside them)
        let mut ctx := ctx
        for d in lp.splitTrace do
          if let .leaf v _ _ := d then
            ctx ← pinTermOpaques cfg cfg.envExpr ctx v
        return ← composeSplit cfg ctx idStr lp chainOpt clit restLits branchSegs
          accClause children [] tree
      -- TRIVIAL continuation: exactly one branch, its segment matching the
      -- single trace leaf's clause segment
      let (contItems, segLits) ← match branchSegs with
        | [(seg, cont)] => do
          let some segL := seg.toList?
            | throwError "replayClauseSpine: literal {idx}'s branch segment \
                          {repr seg} is not a list at {idStr}"
          match lp.splitTrace.filter (fun | .leaf .. => true | _ => false) with
          | [.leaf lv outcome _] =>
            if outcome == "dropped" then
              throwError "replayClauseSpine: single DROPPED leaf on the \
                          non-closing literal {idx} at {idStr} (frontier)"
            let expectedSeg : SExpr :=
              if outcome == "segment-open" then .cons lp.result .nil else .nil
            unless seg == expectedSeg &&
                   (outcome == "segment-false" || lv == lp.result) do
              throwError "replayClauseSpine: literal {idx}'s branch segment \
                          {repr seg} does not match its trace leaf \
                          ({outcome}, {repr lv}) at {idStr}"
          | [] => pure ()  -- no trace (synthetic/legacy log): tolerated
          | leaves =>
            throwError "replayClauseSpine: literal {idx} has {leaves.length} \
                        trace leaves but no split test at {idStr}"
          pure (cont, segL)
        | [] =>
          throwError "replayClauseSpine: non-closing literal {idx} with no \
                      continuation branch at {idStr} (frontier)"
        | _ =>
          throwError "replayClauseSpine: {branchSegs.length} branches on \
                      literal {idx} without a split trace at {idStr} (frontier)"
      if contItems.isEmpty && restLits.isEmpty then
        -- LAST literal, non-closing, trivial trace: the SURVIVING clause was
        -- PUSHED as the sibling subgoal (composeSplit's empty-cont residual,
        -- on the trivial path). The spine's goal here is the BARE literal
        -- (singleton disjunction) — no case split: replay the child, peel it
        -- down to this literal's survivor, and bridge back along the chain.
        let accClause' := accClause ++ segLits.filter (!accClause.contains ·)
        let some child := children.find? (·.inputClause == accClause')
          | throwError "replayClauseSpine: no child clause matches the \
                        residual {repr accClause'} at {idStr}"
        unless accClause'.getLast? == some lp.result do
          throwError "replayClauseSpine: residual's surviving literal is not \
                      literal {idx}'s result at {idStr} (frontier)"
        let pChild ← replayClause cfg ctx child
        let mut p := pChild
        for L in accClause'.dropLast do
          let some hf := ctx.litFactByTerm? L
            | throwError "replayClauseSpine: no falsity fact for the residual \
                          literal {repr L} at {idStr}"
          let pNil ← mkAppM ``re_val_cast
            #[cfg.worldExpr, cfg.envExpr, reflectSExpr L,
              ← ctxValExpr cfg ctx L, mkConst ``SExpr.nil,
              ← ctxValProof cfg ctx L, hf]
          p ← mkAppM ``evtrue_extract_else #[pNil, p]
        -- p : EvTrue(lp.result) — bridge to the pre-rewrite literal
        match chainOpt with
        | none => return p
        | some ch => return ← mkAppM ``evtrue_of_fuel_eq #[ch, p]
      -- split on the literal's value
      let vLit ← ctxValExpr cfg ctx lp.literal
      let pLit ← ctxValProof cfg ctx lp.literal
      let restTerm := disjoinTerm (restLits.map (·.2))
      let neTy ← mkAppM ``Ne #[vLit, mkConst ``SExpr.nil]
      let hthen ← withLocalDeclD `h neTy fun h => do
        let p ← mkAppM ``evtrue_of_eq_t #[← quoteTFact cfg]
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
        let accClause' := accClause ++ segLits.filter (!accClause.contains ·)
        let p ← replayClauseSpine cfg ctx' idStr restLits contItems accClause' children
        mkLambdaFVars #[h] p
      mkAppM ``evtrue_dp_if_split
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr lp.literal, reflectSExpr quoteT,
          reflectSExpr restTerm, vLit, pLit, hthen, helse]

/-- The W3 branch-split COMPOSER: prove `EvTrue w env (disjoin (lit :: rest))`
    for a literal whose clausify SPLIT (docs/notes/2026-07-03_branch-split-
    spine.md, ratified partial logging). The byCases tree comes from the
    emitted decision trace; at each leaf the literal's collapse along the path
    facts is re-derived by `collapseEval` (fail-closed against the emitted
    leaf value), then:
    - a DROPPED leaf ('t): the literal itself is true — the disjunction closes;
    - a SEGMENT leaf: split on the literal's value (truth closes); under its
      falsity, select the unique branch whose segment literals are all
      derivably false, inject the segment facts, and recurse the branch's
      continuation — or, for an EMPTY continuation, peel the pushed sibling
      clause down to the surviving literal and bridge it back. -/
partial def composeSplit (cfg : ReplayConfig) (ctx : ReplayCtx) (idStr : String)
    (lp : LiteralProof) (chainOpt : Option Expr) (clauseLit : SExpr)
    (restLits : List (Nat × SExpr)) (branches : List (SExpr × List ClauseItem))
    (accClause : List SExpr) (children : List ClauseNode)
    (facts : List (SExpr × Expr × Bool × Expr)) (tree : TraceTree) :
    MetaM Expr := do
  let w := cfg.worldExpr
  let e := cfg.envExpr
  let nilC := mkConst ``SExpr.nil
  match tree with
  | .split T fSide tSide =>
    let ctx ← pinTermOpaques cfg e ctx T
    let vT ← ctxValExpr cfg ctx T
    let negL ← withLocalDeclD `hnil (← mkEq vT nilC) fun hNil => do
      let p ← composeSplit cfg ctx idStr lp chainOpt clauseLit restLits branches
        accClause children (facts ++ [(T, vT, false, hNil)]) fSide
      mkLambdaFVars #[hNil] p
    let posL ← withLocalDeclD `hne (← mkAppM ``Ne #[vT, nilC]) fun hNe => do
      let p ← composeSplit cfg ctx idStr lp chainOpt clauseLit restLits branches
        accClause children (facts ++ [(T, vT, true, hNe)]) tSide
      mkLambdaFVars #[hNe] p
    mkAppM ``Classical.byCases #[negL, posL]
  | .resolved T verdict how sub =>
    unless how == "assumed" do
      throwError "composeSplit: resolved test {repr T} how={how} at {idStr} \
                  (frontier — only assumption-resolved tests are re-derived)"
    let ctx ← pinTermOpaques cfg e ctx T
    let vT ← ctxValExpr cfg ctx T
    let wantSign := verdict == "true"
    -- re-derive the resolution: exact match, then commutative equal match
    -- (if-interp-assumed-value2's rule set; fail-closed beyond)
    let hFact ←
      match facts.find? (fun (T', _, _, _) => T' == T) with
      | some (_, _, sign, h) => do
        unless sign == wantSign do
          throwError "composeSplit: fact for {repr T} has sign {sign}, trace \
                      verdict {verdict} at {idStr}"
        pure h
      | none =>
        match T with
        | .cons (.atom (.symbol eqS)) (.cons x (.cons y .nil)) => do
          unless eqS.name == "equal" do
            throwError "composeSplit: no fact for resolved test {repr T} at \
                        {idStr} (frontier)"
          let flipped : SExpr := .cons (.atom (.symbol eqS)) (.cons y (.cons x .nil))
          let some (_, _, sign, h) :=
              facts.find? (fun (T', _, _, _) => T' == flipped)
            | throwError "composeSplit: no fact for resolved test {repr T} \
                          (or its flip) at {idStr} (frontier)"
          unless sign == wantSign do
            throwError "composeSplit: flipped fact for {repr T} has sign \
                        {sign}, trace verdict {verdict} at {idStr}"
          -- transport across logic_equal_comm: vT = Logic.equal vx vy,
          -- fact over Logic.equal vy vx
          let vx ← ctxValExpr cfg ctx x
          let vy ← ctxValExpr cfg ctx y
          let comm ← mkAppM ``logic_equal_comm #[vx, vy]
          if wantSign then
            mkAppM ``ne_of_eq_of_ne #[comm, h]
          else
            mkAppM ``Eq.trans #[comm, h]
        | _ =>
          throwError "composeSplit: no fact for resolved test {repr T} at \
                      {idStr} (frontier)"
    composeSplit cfg ctx idStr lp chainOpt clauseLit restLits branches
      accClause children (facts ++ [(T, vT, wantSign, hFact)]) sub
  | .leaf value outcome =>
    -- re-derive the literal's collapse along the path facts
    let (collapseOpt, collapsed) ← collapseEval cfg ctx facts lp.result
    unless collapsed == value do
      throwError "composeSplit: collapse of literal {lp.index} reached \
                  {repr collapsed}, trace leaf is {repr value} at {idStr}"
    let fullChain ← match chainOpt, collapseOpt with
      | none, none => pure none
      | some c, none => pure (some c)
      | none, some c => pure (some c)
      | some c1, some c2 => pure (some (← mkAppM ``fuel_chain_eq #[c1, c2]))
    let restTerm := disjoinTerm (restLits.map (·.2))
    if outcome == "dropped" then
      -- the literal is TRUE on this path: eval lit ≡ eval 't → close
      unless value == quoteT do
        throwError "composeSplit: dropped leaf value {repr value} ≠ 't at {idStr}"
      let some ch := fullChain
        | throwError "composeSplit: dropped leaf with no chain at {idStr}"
      let pclose ← mkAppM ``fuel_conv_of_eq #[ch, ← quoteTFact cfg]
      if restLits.isEmpty then
        mkAppM ``evtrue_of_eq_t #[pclose]
      else
        let hq ← mkAppM ``re_val_quote #[w, e, reflectSExpr SExpr.t]
        let hcv ← proveByDecide
          (← mkEq (mkApp (mkConst ``Logic.toBool) (mkConst ``SExpr.t)) (mkConst ``Bool.true))
          "toBool t"
        let hIf ← mkAppM ``conv_if_true
          #[w, e, reflectSExpr clauseLit, reflectSExpr quoteT, reflectSExpr restTerm,
            mkConst ``SExpr.t, mkConst ``SExpr.t, pclose, hcv, hq]
        mkAppM ``evtrue_of_eq_t #[hIf]
    else if restLits.isEmpty then
      -- SEGMENT leaf on a SINGLETON clause: the disjunction IS the literal,
      -- and the leaf must be the RESIDUAL (an inline continuation would
      -- prove an empty disjunction). Peel the pushed sibling clause down to
      -- the surviving open-leaf literal and bridge it back — no value split.
      unless outcome == "segment-open" do
        throwError "composeSplit: {outcome} leaf on a singleton clause at \
                    {idStr} (frontier)"
      let deriveFalsity (L : SExpr) : MetaM (Option Expr) := do
        if let some (_, _, _, hf) :=
            facts.find? (fun (T, _, sign, _) => !sign && L == T) then
          return some hf
        match L with
        | .cons (.atom (.symbol ns)) (.cons T .nil) =>
          if ns.name == "not" then
            match facts.find? (fun (T', _, sign, _) => sign && T' == T) with
            | some (_, _, _, hf) =>
              return some (← mkAppM ``not_nil_of_truthy #[hf])
            | none => return none
          else return none
        | _ => return none
      let mut selected : Option (List SExpr × List Expr) := none
      for (seg, cont) in branches do
        -- :CONTEXT-SUBST decorations are inert here (their equations live in
        -- the segment); a residual branch may still carry them
        let contCore := cont.dropWhile fun
          | .step n => (runeOf n).1 == "context-subst"
          | _ => false
        unless contCore.isEmpty do continue
        let some segL := seg.toList?
          | throwError "composeSplit: branch segment {repr seg} is not a \
                        list at {idStr}"
        unless segL.getLast? == some value do continue
        let mut proofs : List Expr := []
        let mut ok := true
        for L in segL.dropLast do
          match ← deriveFalsity L with
          | some p => proofs := proofs ++ [p]
          | none => ok := false
        if ok then
          unless selected.isNone do
            throwError "composeSplit: ambiguous residual selection for the \
                        open leaf {repr value} at {idStr}"
          selected := some (segL, proofs)
      let some (segL, segProofs) := selected
        | throwError "composeSplit: no residual branch matches the open leaf \
                      {repr value} at {idStr} (frontier)"
      let expected := accClause ++ segL.filter (!accClause.contains ·)
      let some child := children.find? (·.inputClause == expected)
        | throwError "composeSplit: no child clause matches the residual \
                      {repr expected} at {idStr}"
      unless expected.getLast? == some value do
        throwError "composeSplit: residual survivor is not last at {idStr}"
      let pChild ← replayClause cfg ctx child
      let segFactsHere := segL.dropLast.zip segProofs
      let mut p := pChild
      for L in expected.dropLast do
        let hf ← match ctx.litFactByTerm? L,
                    (segFactsHere.find? (·.1 == L)).map (·.2) with
          | some hf, _ => pure hf
          | none, some hf => pure hf
          | none, none =>
            throwError "composeSplit: no falsity fact for the residual \
                        literal {repr L} at {idStr}"
        let pNil ← mkAppM ``re_val_cast
          #[w, e, reflectSExpr L, ← ctxValExpr cfg ctx L, nilC,
            ← ctxValProof cfg ctx L, hf]
        p ← mkAppM ``evtrue_extract_else #[pNil, p]
      -- p : EvTrue(value); bridge back to the literal
      match fullChain with
      | none => pure p
      | some ch => mkAppM ``evtrue_of_fuel_eq #[ch, p]
    else
      -- SEGMENT leaf: split on the literal's value
      let vLit ← ctxValExpr cfg ctx clauseLit
      let pLit ← ctxValProof cfg ctx clauseLit
      let hthen ← withLocalDeclD `h (← mkAppM ``Ne #[vLit, nilC]) fun h => do
        let p ← mkAppM ``evtrue_of_eq_t #[← quoteTFact cfg]
        let _ := h
        mkLambdaFVars #[h] p
      let helse ← withLocalDeclD `h (← mkEq vLit nilC) fun h => do
        -- the leaf value's falsity, bridged along the full chain
        let hLeafNil ← match fullChain with
          | none => pure h
          | some ch => do
            let pLeaf ← ctxValProof cfg ctx value
            let vEq ← mkAppM ``val_eq_of_eval_eq #[ch, pLit, pLeaf]
            mkAppM ``Eq.trans #[← mkAppM ``Eq.symm #[vEq], h]
        -- a segment literal's falsity, derivable from the path facts / the
        -- leaf fact (if-interp's convert-assumptions-to-clause-segment)
        let deriveFalsity (L : SExpr) : MetaM (Option Expr) := do
          if outcome == "segment-open" && L == value then
            return some hLeafNil
          if let some (_, _, _, hf) :=
              facts.find? (fun (T, _, sign, _) => !sign && L == T) then
            return some hf
          match L with
          | .cons (.atom (.symbol ns)) (.cons T .nil) =>
            if ns.name == "not" then
              match facts.find? (fun (T', _, sign, _) => sign && T' == T) with
              | some (_, _, _, hf) =>
                return some (← mkAppM ``not_nil_of_truthy #[hf])
              | none => return none
            else return none
          | _ => return none
        -- select the UNIQUE branch whose segment is derivably all-false
        let mut selected : Option (List SExpr × List ClauseItem × List Expr) := none
        for (seg, cont) in branches do
          let some segL := seg.toList?
            | throwError "composeSplit: branch segment {repr seg} is not a \
                          list at {idStr}"
          let mut proofs : List Expr := []
          let mut ok := true
          for L in segL do
            match ← deriveFalsity L with
            | some p => proofs := proofs ++ [p]
            | none => ok := false
          if ok then
            unless selected.isNone do
              throwError "composeSplit: ambiguous branch selection for the \
                          {outcome} leaf {repr value} at {idStr}"
            selected := some (segL, cont, proofs)
        let some (segL, cont, segProofs) := selected
          | throwError "composeSplit: no branch matches the {outcome} leaf \
                        {repr value} at {idStr} (frontier)"
        let cont := cont.dropWhile fun
          | .step n => (runeOf n).1 == "context-subst"
          | _ => false
        let p ←
          if cont.isEmpty then do
            -- RESIDUAL: the branch's clause was pushed as a sibling subgoal
            let expected := accClause ++ segL.filter (!accClause.contains ·)
            let some child := children.find? (·.inputClause == expected)
              | throwError "composeSplit: no child clause matches the residual \
                            {repr expected} at {idStr}"
            unless outcome == "segment-open" && expected.getLast? == some value do
              throwError "composeSplit: residual branch's surviving literal is \
                          not the open leaf at {idStr} (frontier)"
            let pChild ← replayClause cfg ctx child
            -- peel every literal but the survivor
            let segFactsHere := segL.zip segProofs
            let mut p := pChild
            for L in expected.dropLast do
              let hf ← match ctx.litFactByTerm? L,
                          (segFactsHere.find? (·.1 == L)).map (·.2) with
                | some hf, _ => pure hf
                | none, some hf => pure hf
                | none, none =>
                  throwError "composeSplit: no falsity fact for the residual \
                              literal {repr L} at {idStr}"
              let pNil ← mkAppM ``re_val_cast
                #[w, e, reflectSExpr L, ← ctxValExpr cfg ctx L, nilC,
                  ← ctxValProof cfg ctx L, hf]
              p ← mkAppM ``evtrue_extract_else #[pNil, p]
            -- p : EvTrue(value); bridge to the literal and refute h
            let pLitTrue ← match fullChain with
              | none => pure p
              | some ch => mkAppM ``evtrue_of_fuel_eq #[ch, p]
            let hNe ← mkAppM ``ne_nil_of_evtrue_conv #[pLitTrue, pLit]
            let goalTy ← mkAppM ``EvTrue #[w, e, reflectSExpr restTerm]
            mkAppOptM ``absurd #[none, some goalTy, some h, some hNe]
          else do
            -- inline continuation: inject the segment facts and recurse;
            -- leading context-subst steps are the :CONTEXT-SUBST decorations
            -- (their equations are consumed by solidify .segment nodes)
            let cont' := cont.dropWhile fun
              | .step n => (runeOf n).1 == "context-subst"
              | _ => false
            -- the literal's own falsity — at its RECORDED rewritten form
            -- (what the tree linker matched `.literal`-sourced solidify
            -- nodes against), bridged along the literal chain — joins
            -- litFacts under its index, exactly as on the non-split path
            let hResultNil ← match chainOpt with
              | none => pure h
              | some ch => do
                let pLit' ← ctxValProof cfg ctx lp.result
                let vEq ← mkAppM ``val_eq_of_eval_eq #[ch, pLit, pLit']
                mkAppM ``Eq.trans #[← mkAppM ``Eq.symm #[vEq], h]
            let ctx' := { ctx with
              litFacts := ctx.litFacts ++ [(lp.index, lp.result, hResultNil)],
              segFacts := ctx.segFacts ++ segL.zip segProofs }
            let accClause' := accClause ++ segL.filter (!accClause.contains ·)
            replayClauseSpine cfg ctx' idStr restLits cont' accClause' children
        mkLambdaFVars #[h] p
      mkAppM ``evtrue_dp_if_split
        #[w, e, reflectSExpr clauseLit, reflectSExpr quoteT, reflectSExpr restTerm,
          vLit, pLit, hthen, helse]

/-- Replay a clause node: prove `EvTrue w env (disjoinTerm inputClause)`
    (for a single-literal clause this IS the literal/formula statement).
    Induction nodes hard-fail (the scaffold lands next); a pushed clause delegates
    to its pool-root child when the clauses coincide. -/
partial def replayClause (cfg : ReplayConfig) (ctx : ReplayCtx) (cn : ClauseNode) : MetaM Expr := do
  if cn.induction.isSome then
    return ← replayInduction cfg ctx cn
  -- EFFECTIVE clausify records: clausify-input emits its checkpoints on every
  -- preprocess pass, including 'miss passes (whose events flush into the NEXT
  -- step's :REWRITES) and identity re-clausifications — a record whose single
  -- output clause disjoins back to exactly its input, or whose input is the
  -- trivially-true `(quote t)` with an EMPTY output set, certifies that the
  -- pass changed nothing the replay must mirror.
  let isNoopClausify : ClausifyInfo → Bool := fun i =>
    match i.out with
    | [cl] => disjoinTerm cl == i.input
    | [] => i.input == quoteT
    | _ => false
  let clausifyInfos := ((cn.steps.flatMap (·.items)).filterMap fun
    | .clausify i => some i | _ => none).filter (fun i => !(isNoopClausify i))
  -- a push-clause node defers to its pool-root child (same clause) — UNLESS an
  -- effective clausify record changed the clause first (the clausify path
  -- below replays the chain + split and consumes the child itself)
  if clausifyInfos.isEmpty && cn.steps.any (fun s => s.processor.toLower == "push-clause") then
    match cn.children with
    | [child] =>
      unless child.inputClause == cn.inputClause do
        throwError "replayClause: pushed clause ≠ pool-root clause at {cn.idStr}"
      return ← replayClause cfg ctx child
    | _ => throwError "replayClause: push-clause with {cn.children.length} children at {cn.idStr}"
  -- a POOL-SUBSUMED root (synthetic; from (:POOL-SUBSUMED …)): its clause is
  -- an instance-superset of the MORE GENERAL pool root attached as its child
  if cn.steps.any (fun s => s.processor.toLower == "pool-subsumed") then
    return ← replaySubsumed cfg ctx cn
  -- a DESTRUCTOR-ELIMINATION node: the child clause is over the elim's fresh
  -- variables; replayElim bridges it back through the emitted ELIMSEQUENCE
  if let some st := cn.steps.find? (fun s => s.processor.toLower == "eliminate-destructors-clause") then
    unless clausifyInfos.isEmpty do
      throwError "replayClause: elim step alongside an effective clausify \
                  record at {cn.idStr} (frontier)"
    return ← replayElim cfg ctx cn st
  -- a GENERALIZE node: the child clause abstracts the emitted :TERMS by fresh
  -- :VARS; replayGeneralize replays the child at the env binding the fresh
  -- vars to the terms' values and substN-bridges back
  if let some st := cn.steps.find? (fun s => s.processor.toLower == "generalize-clause") then
    unless clausifyInfos.isEmpty do
      throwError "replayClause: generalize step alongside an effective \
                  clausify record at {cn.idStr} (frontier)"
    return ← replayGeneralize cfg ctx cn st
  -- an ELIMINATE-IRRELEVANCE node: the child clause is an order-preserving
  -- SUBSET of this clause (irrelevant literals dropped) — the child's truth
  -- closes the parent disjunction through whichever literal is truthy
  if cn.steps.any (fun s => s.processor.toLower == "eliminate-irrelevance-clause") then
    unless clausifyInfos.isEmpty do
      throwError "replayClause: eliminate-irrelevance step alongside an \
                  effective clausify record at {cn.idStr} (frontier)"
    return ← replayEliminateIrrelevance cfg ctx cn
  -- pin every user-fn application in this clause's subtree from the totality/TP
  -- hypotheses (idempotent — already-pinned terms are skipped), so the value
  -- layer can lift opaque subterms under a quantified env
  let mut ctx := ctx
  for tm in (clauseSubtreeTerms cn).eraseDups do
    ctx ← pinTermOpaques cfg cfg.envExpr ctx tm
  let lits := flattenLiterals (cn.steps.flatMap (·.items))
  -- a preprocess CLAUSIFY split: chain to the recorded input, bridge the proved
  -- output clause (the pushed/pool-root child) back through the if-recursion
  match clausifyInfos with
  | [info] =>
    -- literal items on the same (merged) node come from the PUSH step's
    -- per-literal scan — identity displays only; real rewriting here is a
    -- frontier
    for (_, lp) in lits do
      unless lp.nodes.isEmpty && lp.result == lp.literal do
        throwError "replayClause: non-identity literal item alongside a \
                    clausify record at {cn.idStr} (frontier): {repr lp.literal}"
    let stepNodes := (cn.steps.flatMap (·.items)).filterMap fun
      | .step n => some n | _ => none
    -- the formula is the clause's DISJUNCTION; for a multi-literal clause the
    -- preprocess steps rewrite individual literals, lifted into the disjunction
    -- by path-directed congruence (including the lazy `if`'s then/else branches,
    -- sound here because each step's eval-equality is unconditional)
    let formula := disjoinTerm cn.inputClause
    let (chainOpt, finalT) ← replayPreprocessChainCore cfg ctx formula stepNodes
    unless finalT == info.input do
      throwError "replayClause: preprocess chain reached {repr finalT}, the \
                  clausify input is {repr info.input}"
    let [outClause] := info.out
      | throwError "replayClause: clausify produced {info.out.length} clauses at \
                    {cn.idStr} (multi-clause frontier)"
    let [child] := cn.children
      | throwError "replayClause: clausify with {cn.children.length} children at \
                    {cn.idStr} (frontier)"
    unless child.inputClause == outClause do
      throwError "replayClause: child clause {repr child.inputClause} ≠ the \
                  clausify output {repr outClause}"
    let pChild ← replayClause cfg ctx child
    let pInput ← bridgeClausify cfg ctx info pChild
    match chainOpt with
    | none => return pInput
    | some (ch, false) => return ← mkAppM ``evtrue_of_fuel_eq #[ch, pInput]
    | some (ch, true) => return ← mkAppM ``evtrue_of_evrel_siff #[ch, pInput]
  | _ :: _ :: _ =>
    throwError "replayClause: multiple clausify records at {cn.idStr} (frontier)"
  | [] =>
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
  replayClauseSpine cfg ctx cn.idStr (cn.inputClause.zipIdx.map fun (l, i) => (i + 1, l))
    ((cn.steps.flatMap (·.items)).filter fun
      | .clausify _ => false | _ => true)
    [] cn.children

/-- Replay a DESTRUCTOR-ELIMINATION node (`eliminate-destructors-clause`, rune
    `car-cdr-elim`, single elim record): prove `EvTrue w env (disjoin C)` from
    the child clause `C' = C[(car v)↦v1, (cdr v)↦v2, v↦(cons v1 v2)]` — the
    emitted `:ELIMSEQUENCE`, recomputed and REQUIRED to match, never inferred —
    by cases on the value of `(consp v)`:
    - nil: the clause's `(not (consp v))` literal (required to be literal 1 —
      frontier otherwise) is true and closes the disjunction;
    - non-nil: replay the child at `env' = env[v1 ↦ car vv, v2 ↦ cdr vv]`;
      `evalOpt_substTerm_substN` bridges `eval env' (disjoin C')` to
      `eval env ((disjoin C')σ)` for `σ = v1↦(car v), v2↦(cdr v)`; the residual
      syntactic gap `disjoin C` vs `(disjoin C')σ` is exactly bare-`v`
      occurrences vs `(cons (car v) (cdr v))`, collapsed occurrence-by-occurrence
      by `diffCollapse` under `logic_cons_car_cdr_of_consp` (the elim rule at
      the value level). -/
partial def replayElim (cfg : ReplayConfig) (ctx : ReplayCtx) (cn : ClauseNode)
    (st : WaterfallStep) : MetaM Expr := do
  -- companions must be inert; literal items are identity displays only
  for s in cn.steps do
    unless s.processor.toLower == "eliminate-destructors-clause" ||
           s.processor.toLower == "settled-down-clause" do
      throwError "replayElim: processor {s.processor} alongside elim at \
                  {cn.idStr} (frontier)"
  for (_, lp) in flattenLiterals (cn.steps.flatMap (·.items)) do
    unless lp.nodes.isEmpty && lp.result == lp.literal do
      throwError "replayElim: non-identity literal item at {cn.idStr} \
                  (frontier): {repr lp.literal}"
  -- the emitted justification: exactly one round of one car-cdr-elim record
  let some seqS := st.extraFields.lookup "elimsequence"
    | throwError "replayElim: no :ELIMSEQUENCE at {cn.idStr}"
  let some [roundS] := seqS.toList?
    | throwError "replayElim: :ELIMSEQUENCE is not a single round at {cn.idStr} \
                  (frontier): {repr seqS}"
  let some [recS] := roundS.toList?
    | throwError "replayElim: elim round is not a single record at {cn.idStr} \
                  (frontier): {repr roundS}"
  let some [runeS, varS, targetS, destS, crit1, crit2, crit3] := recS.toList?
    | throwError "replayElim: elim record shape at {cn.idStr}: {repr recS}"
  unless crit1 == .nil && crit2 == .nil && crit3 == .nil do
    throwError "replayElim: elim record carries non-nil trailing fields at \
                {cn.idStr} (frontier): {repr recS}"
  let some [.atom (.keyword "elim"), .atom (.symbol runeName)] := runeS.toList?
    | throwError "replayElim: elim record rune {repr runeS} at {cn.idStr}"
  unless runeName.name == "car-cdr-elim" do
    throwError "replayElim: elim rule {runeName.name} ≠ car-cdr-elim at \
                {cn.idStr} (frontier)"
  let .atom (.symbol v) := varS
    | throwError "replayElim: eliminated var {repr varS} at {cn.idStr}"
  let .cons (.atom (.symbol consS))
      (.cons (.atom (.symbol v1)) (.cons (.atom (.symbol v2)) .nil)) := targetS
    | throwError "replayElim: elim target {repr targetS} is not (cons v1 v2) \
                  at {cn.idStr}"
  unless consS.name == "cons" && v1 != v2 && v1 != v && v2 != v do
    throwError "replayElim: elim target vars ({consS.name} {v1.name} {v2.name}) \
                at {cn.idStr}"
  let vT : SExpr := .atom (.symbol v)
  let carT : SExpr := .cons (.atom (.symbol { name := "car" })) (.cons vT .nil)
  let cdrT : SExpr := .cons (.atom (.symbol { name := "cdr" })) (.cons vT .nil)
  let uT : SExpr := .cons (.atom (.symbol { name := "cons" }))
    (.cons (.atom (.symbol v1)) (.cons (.atom (.symbol v2)) .nil))
  let expectedDest : List SExpr :=
    [.cons carT (.atom (.symbol v1)), .cons cdrT (.atom (.symbol v2))]
  unless destS.toList? == some expectedDest do
    throwError "replayElim: destructor map {repr destS} ≠ ((car {v.name}) . \
                {v1.name}) ((cdr {v.name}) . {v2.name}) at {cn.idStr}"
  let some varsS := st.extraFields.lookup "elimvars"
    | throwError "replayElim: no :ELIMVARS at {cn.idStr}"
  let expectedVars : SExpr :=
    .cons (.cons (.atom (.symbol v1)) (.cons (.atom (.symbol v2)) .nil)) .nil
  unless varsS == expectedVars do
    throwError "replayElim: :ELIMVARS {repr varsS} ≠ (({v1.name} {v2.name})) \
                at {cn.idStr}"
  -- structure: one output clause, one child, and they match
  let [outClause] := st.newClauses
    | throwError "replayElim: {st.newClauses.length} output clauses at \
                  {cn.idStr} (frontier)"
  let some outLits := outClause.toList?
    | throwError "replayElim: output clause {repr outClause} is not a list"
  let [child] := cn.children
    | throwError "replayElim: {cn.children.length} children at {cn.idStr} (frontier)"
  unless child.inputClause == outLits do
    throwError "replayElim: child clause ≠ elim output clause at {cn.idStr}"
  -- recompute the elim substitution on the input clause and REQUIRE the
  -- emitted output (round-trip validation of the record)
  unless cn.inputClause.map (elimReplace carT cdrT vT uT v1 v2) == outLits do
    throwError "replayElim: recomputed elim clause ≠ emitted output at \
                {cn.idStr} (record/output divergence)"
  -- the clause's head literal must be (not (consp v)) — the elim split's guard
  let lit1 : SExpr := .cons (.atom (.symbol { name := "not" }))
    (.cons (.cons (.atom (.symbol { name := "consp" })) (.cons vT .nil)) .nil)
  let c0 :: cRest := cn.inputClause
    | throwError "replayElim: empty input clause at {cn.idStr}"
  unless c0 == lit1 do
    throwError "replayElim: clause head {repr c0} is not (not (consp {v.name})) \
                at {cn.idStr} (frontier — elim literal not first)"
  if cRest.isEmpty then
    throwError "replayElim: singleton clause at {cn.idStr} (frontier)"
  let w := cfg.worldExpr
  let env := cfg.envExpr
  let vE ← ctxValExpr cfg ctx vT
  let pV ← ctxValProof cfg ctx vT
  let conspVE := mkApp (mkConst ``Logic.consp) vE
  let nilC := mkConst ``SExpr.nil
  -- CASE (consp v) = nil: literal 1 is true and closes the disjunction
  let negL ← withLocalDeclD `hnil (← mkEq conspVE nilC) fun hNil => do
    let pLit1 ← ctxValProof cfg ctx lit1
    let hT ← mkAppM ``logic_not_t_of_nil #[hNil]
    let pLit1T ← mkAppM ``re_val_cast
      #[w, env, reflectSExpr lit1, mkApp (mkConst ``Logic.not) conspVE,
        mkConst ``SExpr.t, pLit1, hT]
    let hToBool ← proveByDecide
      (← mkEq (mkApp (mkConst ``Logic.toBool) (mkConst ``SExpr.t)) (mkConst ``Bool.true))
      "toBool t"
    let hQt ← quoteTFact cfg
    let hIf ← mkAppM ``conv_if_true
      #[w, env, reflectSExpr lit1, reflectSExpr quoteT,
        reflectSExpr (disjoinTerm cRest), mkConst ``SExpr.t, mkConst ``SExpr.t,
        pLit1T, hToBool, hQt]
    let p ← mkAppM ``evtrue_of_eq_t #[hIf]
    mkLambdaFVars #[hNil] p
  -- CASE (consp v) ≠ nil: replay the child at the elim env and bridge back
  let posL ← withLocalDeclD `hne (← mkAppM ``Ne #[conspVE, nilC]) fun hNe => do
    let carV := mkApp (mkConst ``Logic.car) vE
    let cdrV := mkApp (mkConst ``Logic.cdr) vE
    let formalsE ← mkListLit (mkConst ``Symbol) [reflectSymbol v1, reflectSymbol v2]
    let valsE ← mkListLit (mkConst ``SExpr) [carV, cdrV]
    let env' ← mkAppM ``envUpdate #[env, formalsE, valsE]
    let cfg' := { cfg with envExpr := env' }
    let ctx' := { ctx with varVals := [], vals := [], litFacts := [] }
    let pChild ← replayClause cfg' ctx' child
    -- substN bridge: eval env ((disjoin C')σ) ≡ eval env' (disjoin C')
    let bodyT := disjoinTerm child.inputClause
    let argsS : List SExpr := [carT, cdrT]
    let argsE ← mkListLit (mkConst ``SExpr) (argsS.map reflectSExpr)
    let hNoLet ← proveByDecide
      (← mkEq (← mkAppM ``ACL2.Replay.NoLet #[reflectSExpr bodyT]) (mkConst ``Bool.true))
      "NoLet elim child"
    let hlenPf ← proveByDecide
      (← mkEq (← mkAppM ``List.length #[argsE]) (← mkAppM ``List.length #[valsE]))
      "substN arg/val lengths"
    let pCar ← ctxValProof cfg ctx carT
    let pCdr ← ctxValProof cfg ctx cdrT
    let prodTy ← mkAppM ``Prod #[mkConst ``SExpr, mkConst ``SExpr]
    let pFn ← withLocalDeclD `pr prodTy fun prV => do
      let fst ← mkAppM ``Prod.fst #[prV]
      let snd ← mkAppM ``Prod.snd #[prV]
      mkLambdaFVars #[prV] (← mkValConvPropEx w env fst snd)
    let entries ← (argsS.zip [carV, cdrV]).mapM fun (a, av) =>
      mkAppM ``Prod.mk #[reflectSExpr a, av]
    let (_, hargsRaw) ← mkForallMemProof prodTy pFn (entries.zip [pCar, pCdr])
    let zipE ← mkAppM ``List.zip #[argsE, valsE]
    let hargsTy ← withLocalDeclD `pr prodTy fun prV => do
      let mem ← mkAppM ``Membership.mem #[zipE, prV]
      mkForallFVars #[prV] (← mkArrow mem (mkApp pFn prV).headBeta)
    let hargs ← mkExpectedTypeHint hargsRaw hargsTy
    let pBridge ← mkAppM ``evalOpt_substTerm_substN
      #[w, env, formalsE, argsE, valsE, reflectSExpr bodyT, hNoLet, hlenPf, hargs]
    -- diff-collapse: eval env (disjoin C) ≡ eval env ((disjoin C')σ) — the
    -- residual diffs are bare `v` vs the σ-IMAGE of the elim target,
    -- `(cons (car v) (cdr v))`
    let sTermS := ACL2.Replay.substTerm [v1, v2] argsS bodyT
    let uSig : SExpr := .cons (.atom (.symbol { name := "cons" }))
      (.cons carT (.cons cdrT .nil))
    let hVeq ← mkAppM ``Eq.symm #[← mkAppM ``logic_cons_car_cdr_of_consp #[hNe]]
    let pU ← ctxValProof cfg ctx uSig
    let nodeEq ← mkAppM ``fuel_eq_of_conv #[pV, pU, hVeq]
    let chainOpt ← diffCollapse w env vT uSig nodeEq (disjoinTerm cn.inputClause) sTermS
    let pAll ← match chainOpt with
      | none => pure pBridge
      | some c => mkAppM ``fuel_chain_eq #[c, pBridge]
    let p ← mkAppM ``evtrue_of_fuel_eq #[pAll, pChild]
    mkLambdaFVars #[hNe] p
  mkAppM ``Classical.byCases #[negL, posL]


/-- Replay a GENERALIZE node (`generalize-clause`): the child clause `C'`
    abstracts the emitted `:TERMS` by the fresh `:VARS` — substituting the
    terms back for the vars must recover THIS clause exactly (recompute-and-
    check; a var that was not fresh fails it). Prove `EvTrue w env (disjoin C)`
    by replaying the child at `env' = env[vars ↦ term values]` and bridging
    `eval env ((disjoin C')σ) ≡ eval env' (disjoin C')` by `substN`
    (σ = vars ↦ terms) — the elim pattern without the case split. -/
partial def replayGeneralize (cfg : ReplayConfig) (ctx : ReplayCtx) (cn : ClauseNode)
    (st : WaterfallStep) : MetaM Expr := do
  for s in cn.steps do
    unless s.processor.toLower == "generalize-clause" ||
           s.processor.toLower == "settled-down-clause" do
      throwError "replayGeneralize: processor {s.processor} alongside \
                  generalize at {cn.idStr} (frontier)"
  for (_, lp) in flattenLiterals (cn.steps.flatMap (·.items)) do
    unless lp.nodes.isEmpty && lp.result == lp.literal do
      throwError "replayGeneralize: non-identity literal item at {cn.idStr} \
                  (frontier): {repr lp.literal}"
  let some genS := st.extraFields.lookup "generalize"
    | throwError "replayGeneralize: no :GENERALIZE record at {cn.idStr}"
  let rec plistLookup (k : String) : SExpr → Option SExpr
    | .cons (.atom (.keyword kw)) (.cons v rest) =>
      if kw == k then some v else plistLookup k rest
    | .cons _ rest => plistLookup k rest
    | _ => none
  let some termsS := plistLookup "terms" genS
    | throwError "replayGeneralize: :GENERALIZE without :TERMS at {cn.idStr}"
  let some varsS := plistLookup "vars" genS
    | throwError "replayGeneralize: :GENERALIZE without :VARS at {cn.idStr}"
  -- one round only (a multi-round generalize is a frontier)
  let some [roundTermsS] := termsS.toList?
    | throwError "replayGeneralize: :TERMS {repr termsS} is not a single \
                  round at {cn.idStr} (frontier)"
  let some [roundVarsS] := varsS.toList?
    | throwError "replayGeneralize: :VARS {repr varsS} is not a single \
                  round at {cn.idStr} (frontier)"
  let some terms := roundTermsS.toList?
    | throwError "replayGeneralize: round terms {repr roundTermsS} not a list"
  let some varsL := roundVarsS.toList?
    | throwError "replayGeneralize: round vars {repr roundVarsS} not a list"
  let gvars ← varsL.mapM fun v => do
    let .atom (.symbol s) := v
      | throwError "replayGeneralize: non-variable {repr v} in :VARS"
    pure s
  unless gvars.length == terms.length && !gvars.isEmpty do
    throwError "replayGeneralize: {gvars.length} vars for {terms.length} \
                terms at {cn.idStr}"
  let [child] := cn.children
    | throwError "replayGeneralize: {cn.children.length} children at \
                  {cn.idStr} (frontier)"
  -- recompute-and-check: σ-substituting the child recovers this clause
  let childTerm := disjoinTerm child.inputClause
  unless ACL2.Replay.substTerm gvars terms childTerm
      == disjoinTerm cn.inputClause do
    throwError "replayGeneralize: substituting the :TERMS back does not \
                recover the clause at {cn.idStr} (recompute/emission \
                divergence)"
  let w := cfg.worldExpr
  let env := cfg.envExpr
  -- pin the generalized terms and take their values at THIS env
  let mut ctx := ctx
  let mut vals : List Expr := []
  let mut convs : List Expr := []
  for t in terms do
    ctx ← pinTermOpaques cfg env ctx t
    vals := vals ++ [← ctxValExpr cfg ctx t]
    convs := convs ++ [← ctxValProof cfg ctx t]
  let formalsE ← mkListLit (mkConst ``Symbol) (gvars.map reflectSymbol)
  let argsE ← mkListLit (mkConst ``SExpr) (terms.map reflectSExpr)
  let valsE ← mkListLit (mkConst ``SExpr) vals
  let env' ← mkAppM ``envUpdate #[env, formalsE, valsE]
  let cfg' := { cfg with envExpr := env' }
  -- clear ALL env-bound fact channels (audit 2026-07-06: branchFacts/segFacts
  -- carry proofs about THIS env; stale ones at env\' would only kernel-fail,
  -- but must not be offered)
  let ctx' := { ctx with varVals := [], vals := [], litFacts := [],
                         branchFacts := [], segFacts := [] }
  let pChild ← replayClause cfg' ctx' child
  -- substN bridge back to this env
  let hNoLet ← proveByDecide
    (← mkEq (← mkAppM ``ACL2.Replay.NoLet #[reflectSExpr childTerm])
            (mkConst ``Bool.true))
    "NoLet generalize child"
  let hlenPf ← proveByDecide
    (← mkEq (← mkAppM ``List.length #[argsE]) (← mkAppM ``List.length #[valsE]))
    "substN arg/val lengths"
  let prodTy ← mkAppM ``Prod #[mkConst ``SExpr, mkConst ``SExpr]
  let pFn ← withLocalDeclD `pr prodTy fun prV => do
    let fst ← mkAppM ``Prod.fst #[prV]
    let snd ← mkAppM ``Prod.snd #[prV]
    mkLambdaFVars #[prV] (← mkValConvPropEx w env fst snd)
  let entries ← (terms.zip vals).mapM fun (t, v) =>
    mkAppM ``Prod.mk #[reflectSExpr t, v]
  let (_, hargsRaw) ← mkForallMemProof prodTy pFn (entries.zip convs)
  let zipE ← mkAppM ``List.zip #[argsE, valsE]
  let hargsTy ← withLocalDeclD `pr prodTy fun prV => do
    let mem ← mkAppM ``Membership.mem #[zipE, prV]
    mkForallFVars #[prV] (← mkArrow mem (mkApp pFn prV).headBeta)
  let hargs ← mkExpectedTypeHint hargsRaw hargsTy
  let pBridge ← mkAppM ``evalOpt_substTerm_substN
    #[w, env, formalsE, argsE, valsE, reflectSExpr childTerm, hNoLet, hlenPf, hargs]
  mkAppM ``evtrue_of_fuel_eq #[pBridge, pChild]

/-- Replay a POOL-SUBSUMED root: ACL2 regarded this pool clause `C` as proved
    pending the MORE GENERAL pool root `G` (its clause attached as the child's
    subtree by the builder). Recompute the subsumption witness σ (every
    Gσ-literal ∈ C — validated, fail-closed), replay `G`'s subtree at
    `env' = env[σvars ↦ σterm values]`, bridge `eval env ((∨G)σ) ≡
    eval env' (∨G)` by substN, and walk the σ-instance literals: nil peels,
    the first truthy literal is IN `C` and closes the disjunction. -/
partial def replaySubsumed (cfg : ReplayConfig) (ctx : ReplayCtx)
    (cn : ClauseNode) : MetaM Expr := do
  let [child] := cn.children
    | throwError "replaySubsumed: {cn.children.length} children at {cn.idStr}"
  let G := child.inputClause
  let C := cn.inputClause
  let gvars := (G.flatMap ACL2.Replay.freeVars).eraseDups
  let some σ := subsumeWitness gvars G C []
    | throwError "replaySubsumed: no subsumption witness — {cn.idStr}'s \
                  clause is not an instance-superset of {child.idStr}'s \
                  (recompute/emission divergence)"
  -- VALIDATE the witness (recompute-and-check): every σ-literal is in C
  let σvars := σ.map (·.1)
  let σterms := σ.map (·.2)
  let litsσ := G.map (ACL2.Replay.substTerm σvars σterms)
  for l in litsσ do
    unless C.contains l do
      throwError "replaySubsumed: witness literal {repr l} not in the \
                  subsumed clause at {cn.idStr}"
  let w := cfg.worldExpr
  let env := cfg.envExpr
  let mut ctx := ctx
  let mut vals : List Expr := []
  let mut convs : List Expr := []
  for t in σterms do
    ctx ← pinTermOpaques cfg env ctx t
    vals := vals ++ [← ctxValExpr cfg ctx t]
    convs := convs ++ [← ctxValProof cfg ctx t]
  let formalsE ← mkListLit (mkConst ``Symbol) (σvars.map reflectSymbol)
  let argsE ← mkListLit (mkConst ``SExpr) (σterms.map reflectSExpr)
  let valsE ← mkListLit (mkConst ``SExpr) vals
  let env' ← mkAppM ``envUpdate #[env, formalsE, valsE]
  let cfg' := { cfg with envExpr := env' }
  let ctx' := { ctx with varVals := [], vals := [], litFacts := [],
                         branchFacts := [], segFacts := [] }
  let pChild ← replayClause cfg' ctx' child
  let childTerm := disjoinTerm G
  let hNoLet ← proveByDecide
    (← mkEq (← mkAppM ``ACL2.Replay.NoLet #[reflectSExpr childTerm])
            (mkConst ``Bool.true))
    "NoLet subsumed general clause"
  let hlenPf ← proveByDecide
    (← mkEq (← mkAppM ``List.length #[argsE]) (← mkAppM ``List.length #[valsE]))
    "substN arg/val lengths"
  let prodTy ← mkAppM ``Prod #[mkConst ``SExpr, mkConst ``SExpr]
  let pFn ← withLocalDeclD `pr prodTy fun prV => do
    let fst ← mkAppM ``Prod.fst #[prV]
    let snd ← mkAppM ``Prod.snd #[prV]
    mkLambdaFVars #[prV] (← mkValConvPropEx w env fst snd)
  let entries ← (σterms.zip vals).mapM fun (t, v) =>
    mkAppM ``Prod.mk #[reflectSExpr t, v]
  let (_, hargsRaw) ← mkForallMemProof prodTy pFn (entries.zip convs)
  let zipE ← mkAppM ``List.zip #[argsE, valsE]
  let hargsTy ← withLocalDeclD `pr prodTy fun prV => do
    let mem ← mkAppM ``Membership.mem #[zipE, prV]
    mkForallFVars #[prV] (← mkArrow mem (mkApp pFn prV).headBeta)
  let hargs ← mkExpectedTypeHint hargsRaw hargsTy
  let pBridge ← mkAppM ``evalOpt_substTerm_substN
    #[w, env, formalsE, argsE, valsE, reflectSExpr childTerm, hNoLet, hlenPf, hargs]
  -- EvTrue of the σ-instance disjunction at THIS env
  let pInst ← mkAppM ``evtrue_of_fuel_eq #[pBridge, pChild]
  -- walk the σ-instance literals into the subsumed clause
  let nilC := mkConst ``SExpr.nil
  let closeAt (ctxW : ReplayCtx) (l : SExpr) (hne : Expr) : MetaM Expr := do
    let some m := C.findIdx? (· == l)
      | throwError "replaySubsumed: internal — witness literal {repr l} \
                    lost from the clause"
    evtrueOfLitTrue cfg ctxW C m l hne
  let rec goW (ctxW : ReplayCtx) (pCur : Expr) : List SExpr → MetaM Expr
    | [] => throwError "replaySubsumed: empty instance walk"
    | [l] => do
      let ctxW ← pinTermOpaques cfg cfg.envExpr ctxW l
      let pL ← ctxValProof cfg ctxW l
      let hne ← mkAppM ``ne_nil_of_evtrue_conv #[pCur, pL]
      closeAt ctxW l hne
    | l :: restL => do
      let ctxW ← pinTermOpaques cfg cfg.envExpr ctxW l
      let vL ← ctxValExpr cfg ctxW l
      let pL ← ctxValProof cfg ctxW l
      let negB ← withLocalDeclD `hnil (← mkEq vL nilC) fun hNil => do
        let pNil ← mkAppM ``re_val_cast
          #[w, env, reflectSExpr l, vL, nilC, pL, hNil]
        let pRest ← mkAppM ``evtrue_extract_else #[pNil, pCur]
        mkLambdaFVars #[hNil] (← goW ctxW pRest restL)
      let posB ← withLocalDeclD `hne (← mkAppM ``Ne #[vL, nilC]) fun hNe => do
        mkLambdaFVars #[hNe] (← closeAt ctxW l hNe)
      mkAppM ``Classical.byCases #[negB, posB]
  goW ctx pInst litsσ

/-- Replay an ELIMINATE-IRRELEVANCE node: the child clause `C'` is an
    order-preserving SUBSET of this clause `C` (recompute-and-check).
    `EvTrue (disjoin C')` closes `EvTrue (disjoin C)`: value-walk `C'` —
    a nil literal peels off (`evtrue_extract_else`); the first truthy
    literal is IN `C`, closing the parent disjunction (`evtrueOfLitTrue`);
    the last literal's `EvTrue` is its own truthy fact. -/
partial def replayEliminateIrrelevance (cfg : ReplayConfig) (ctx : ReplayCtx)
    (cn : ClauseNode) : MetaM Expr := do
  for s in cn.steps do
    unless s.processor.toLower == "eliminate-irrelevance-clause" ||
           s.processor.toLower == "settled-down-clause" do
      throwError "replayEliminateIrrelevance: processor {s.processor} \
                  alongside eliminate-irrelevance at {cn.idStr} (frontier)"
  for (_, lp) in flattenLiterals (cn.steps.flatMap (·.items)) do
    unless lp.nodes.isEmpty && lp.result == lp.literal do
      throwError "replayEliminateIrrelevance: non-identity literal item at \
                  {cn.idStr} (frontier): {repr lp.literal}"
  let [child] := cn.children
    | throwError "replayEliminateIrrelevance: {cn.children.length} children \
                  at {cn.idStr} (frontier)"
  -- recompute-and-check: C' is an order-preserving sublist of C
  let rec isSublist : List SExpr → List SExpr → Bool
    | [], _ => true
    | _, [] => false
    | x :: xs, y :: ys => if x == y then isSublist xs ys else isSublist (x :: xs) ys
  unless isSublist child.inputClause cn.inputClause do
    throwError "replayEliminateIrrelevance: child clause is not an \
                order-preserving subset of {cn.idStr}'s clause"
  let mut ctx := ctx
  for tm in child.inputClause do
    ctx ← pinTermOpaques cfg cfg.envExpr ctx tm
  let pChild ← replayClause cfg ctx child
  let nilC := mkConst ``SExpr.nil
  let closeAt (ctxW : ReplayCtx) (l : SExpr) (hne : Expr) : MetaM Expr := do
    let some m := cn.inputClause.findIdx? (· == l)
      | throwError "replayEliminateIrrelevance: internal — surviving literal \
                    {repr l} not in the parent clause"
    evtrueOfLitTrue cfg ctxW cn.inputClause m l hne
  let rec goSub (ctxW : ReplayCtx) (pCur : Expr) : List SExpr → MetaM Expr
    | [] => throwError "replayEliminateIrrelevance: empty child clause walk"
    | [l] => do
      let pL ← ctxValProof cfg ctxW l
      let hne ← mkAppM ``ne_nil_of_evtrue_conv #[pCur, pL]
      closeAt ctxW l hne
    | l :: restL => do
      let vL ← ctxValExpr cfg ctxW l
      let pL ← ctxValProof cfg ctxW l
      let negB ← withLocalDeclD `hnil (← mkEq vL nilC) fun hNil => do
        let pNil ← mkAppM ``re_val_cast
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr l, vL, nilC, pL, hNil]
        let pRest ← mkAppM ``evtrue_extract_else #[pNil, pCur]
        mkLambdaFVars #[hNil] (← goSub ctxW pRest restL)
      let posB ← withLocalDeclD `hne (← mkAppM ``Ne #[vL, nilC]) fun hNe => do
        mkLambdaFVars #[hNe] (← closeAt ctxW l hNe)
      mkAppM ``Classical.byCases #[negB, posB]
  goSub ctx pChild child.inputClause

/-- Replay an INDUCTION pool-root from its EMITTED justification (G5 v2,
    docs/plans/2026-06-12_multicase-induction.md): measure `(acl2-count v)`
    under `o<`, one controller; N cases with COMPOUND ruling tests (the
    emitted decision tree), multiple base cases, multiple IHs per case, IH
    alists substituting non-controller variables by arbitrary computed terms.
    The controller's own substitution must be `(cdr controller)` under an
    in-scope `(consp controller)` ruling test (the Count-library decrease);
    anything else hard-fails (frontier — msort/qsort move this wall). -/
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
  let cdrT : SExpr := .cons (.atom (.symbol { name := "cdr" })) (.cons cvarT .nil)
  -- 2. per-case validation: every IH alist must be over DISTINCT variables and
  -- map the controller to (cdr controller), justified by an in-scope (consp
  -- controller) ruling test; non-controller substitutions are unrestricted.
  for c in ind.cases do
    if c.tests.isEmpty then
      throwError "replayInduction: a case has no ruling tests (frontier)"
    unless c.alists.isEmpty do
      unless c.tests.contains consT do
        throwError "replayInduction: step case tests {repr c.tests} lack \
                    (consp {cvar.name}) — non-cdr measure decrease (frontier)"
      for alist in c.alists do
        let vars := alist.map (·.1)
        unless vars.eraseDups.length == vars.length do
          throwError "replayInduction: IH alist vars {repr vars} not distinct"
        match alist.lookup cvar with
        | some tm =>
          unless tm == cdrT do
            throwError "replayInduction: IH maps controller {cvar.name} to \
                        {repr tm}, expected (cdr {cvar.name}) (frontier)"
        | none =>
          throwError "replayInduction: IH alist omits the controller \
                      {cvar.name} (identity on the measured var — frontier)"
  -- 3. the pushed clause (k literals) and recomputed child clauses. The
  -- induction formula for clause C under IHs σ1…σm is
  -- (tests ∧ (∨C)σ1 ∧ … ∧ (∨C)σm) → (∨C); each IH's ¬(∨C)σi is a
  -- CONJUNCTION of the per-literal negations, so clausification yields the
  -- CROSS PRODUCT: one clause per choice of one literal per IH —
  -- negTests ++ [¬L_{j1}σ1, …, ¬L_{jm}σm] ++ C.
  let pushedLits := cn.inputClause
  if pushedLits.isEmpty then
    throwError "replayInduction: empty pushed clause"
  let pushedTerm := disjoinTerm pushedLits
  -- per case: the list of IH-literal SELECTIONS (cartesian product; a base
  -- case has the single empty selection). Each selection entry is
  -- (alist, literal index j, the clause literal ¬L_jσ).
  let selectionsOf : InductionCase → List (List (List (Symbol × SExpr) × Nat × SExpr)) :=
    fun c => c.alists.foldl (init := [[]]) fun acc alist =>
      let formals := alist.map (·.1)
      let args := alist.map (·.2)
      acc.flatMap fun sel =>
        pushedLits.zipIdx.map fun (l, j) =>
          sel ++ [(alist, j, dumbNegateLit (ACL2.Replay.substTerm formals args l))]
  let expected : List (Nat × InductionCase × List (List (Symbol × SExpr) × Nat × SExpr) × List SExpr) :=
    ind.cases.zipIdx.flatMap fun (c, i) =>
      let negTests := c.tests.map dumbNegateLit
      (selectionsOf c).map fun sel =>
        (i, c, sel, negTests ++ sel.map (·.2.2) ++ pushedLits)
  -- ACL2's induction-formula CLEAN-UP drops trivially-true clauses (a
  -- complementary literal pair, or a 't literal) — a cross-product clause
  -- where σ leaves an IH literal UNCHANGED is the standard case (¬Lσ = ¬L
  -- complements the goal's own L). This mirrors the COMMON arms of ACL2's
  -- add-literal clean-up (audit 2026-07-06: not all — e.g. non-'t quoted
  -- constants, commuted-equality complements are not folded here); ANY
  -- divergence is caught by the scheme-count/containment/children checks
  -- below, never silent. Dropped selections are discharged directly at the
  -- walk (their truthy literal IS a goal literal).
  let isTaut : List SExpr → Bool := fun cl =>
    cl.any (fun l => l == quoteT || cl.contains (dumbNegateLit l))
  let kept := expected.filter (fun (_, _, _, cl) => !isTaut cl)
  let dropped := expected.filter (fun (_, _, _, cl) => isTaut cl)
  -- validate the recomputation against the EMITTED scheme clause set
  let schemeClauses ← ind.scheme.mapM fun cl => do
    let some lits := cl.toList?
      | throwError "replayInduction: scheme clause {repr cl} is not a list"
    pure lits
  unless schemeClauses.length == kept.length do
    throwError "replayInduction: {schemeClauses.length} scheme clauses for \
                {kept.length} recomputed (non-tautological) case clauses \
                (mismatch)"
  for (_, _, _, cl) in kept do
    unless schemeClauses.contains cl do
      throwError "replayInduction: recomputed case clause {repr cl} not in \
                  the emitted :SCHEME (recompute/emission divergence)"
  -- link children 1:1 by exact clause match (duplicate expected clauses would
  -- make the match ambiguous — hard-fail rather than guess)
  unless (kept.map (·.2.2.2)).eraseDups.length == kept.length do
    throwError "replayInduction: duplicate recomputed case clauses (frontier)"
  unless cn.children.length == kept.length do
    throwError "replayInduction: {cn.children.length} children for \
                {kept.length} recomputed case clauses (frontier)"
  let linked ← kept.mapM fun (i, c, sel, cl) => do
    let some child := cn.children.find? (·.inputClause == cl)
      | throwError "replayInduction: no child with clause {repr cl} (case {i})"
    pure (i, c, sel, cl, child)
  let tree ← ofExcept (buildCaseTree (ind.cases.zipIdx.map fun (c, i) => (i, c.tests)))
  let w := cfg.worldExpr
  let pushedE := reflectSExpr pushedTerm
  let nilC := mkConst ``SExpr.nil
  -- 4. P : SExpr → Prop — the pushed clause's truth is `EvTrue` (G2)
  let P ← withLocalDeclD `xv (mkConst ``SExpr) fun xvV => do
    let body ← withLocalDeclD `e (mkConst ``ACL2.Env) fun eV => do
      let hxTy ← mkValConvPropEx w eV (reflectSExpr cvarT) xvV
      let goal ← mkAppM ``EvTrue #[w, eV, pushedE]
      mkForallFVars #[eV] (← mkArrow hxTy goal)
    mkLambdaFVars #[xvV] body
  let conspOf := fun (v : Expr) => mkApp (mkConst ``Logic.consp) v
  let hNoLet ← proveByDecide
    (← mkEq (← mkAppM ``ACL2.Replay.NoLet #[pushedE]) (mkConst ``Bool.true))
    "NoLet pushed"
  -- 5. the strong-induction STEP: ∀ xv, (∀ u, count u < count xv → P u) → P xv,
  -- dispatching the emitted decision tree at the env level.
  let step ← withLocalDeclD `xv (mkConst ``SExpr) fun xvV => do
    let countOf := fun (v : Expr) => mkApp (mkConst ``SExpr.acl2Count) v
    let sihTy ← withLocalDeclD `u (mkConst ``SExpr) fun uV => do
      let lt ← mkAppM ``LT.lt #[countOf uV, countOf xvV]
      mkForallFVars #[uV] (← mkArrow lt (mkApp P uV).headBeta)
    let inner ← withLocalDeclD `sih sihTy fun sihV => do
      let inner2 ← withLocalDeclD `e (mkConst ``ACL2.Env) fun eV => do
        let hxTy ← mkValConvPropEx w eV (reflectSExpr cvarT) xvV
        let inner3 ← withLocalDeclD `hx hxTy fun hX => do
          let cfg' := { cfg with envExpr := eV }
          let ctx0 : ReplayCtx :=
            { ctx with varVals := [(cvar, xvV, hX)], vals := [], litFacts := [] }
          -- ONE IH's truth: instantiate the strong IH at the substituted
          -- controller value and bridge to this env by substN — EvTrue of the
          -- σ-instance of the pushed DISJUNCTION (the walk below consumes it)
          let ihDisjTruth (ctxD : ReplayCtx) (facts : List TestFact)
              (alist : List (Symbol × SExpr)) :
              MetaM (ReplayCtx × Expr) := do
            -- controller FIRST (envUpdate's head insert is outermost — the
            -- controller-lookup cast below depends on it)
            let others := alist.filter (·.1 != cvar)
            let formals := cvar :: others.map (·.1)
            let args := cdrT :: others.map (·.2)
            let uVal := mkApp (mkConst ``Logic.cdr) xvV
            let hCdrConv ← ctxValProof cfg' ctxD cdrT
            let mut ctxD := ctxD
            let mut otherVals : List (Expr × Expr) := []
            for (_, atm) in others do
              ctxD ← pinTermOpaques cfg' eV ctxD atm
              let aE ← ctxValExpr cfg' ctxD atm
              let aP ← ctxValProof cfg' ctxD atm
              otherVals := otherVals ++ [(aE, aP)]
            -- measure decrease from the in-scope (consp cvar) ruling fact
            let some cf := facts.find? (fun f => f.test == consT && f.sign)
              | throwError "replayInduction: no in-scope truthy (consp \
                            {cvar.name}) fact for the IH decrease"
            let neTy ← mkAppM ``Ne #[conspOf xvV, nilC]
            unless ← isDefEq (← inferType cf.signE) neTy do
              throwError "replayInduction: the (consp {cvar.name}) fact's \
                          value is not Logic.consp of the controller pin"
            let hNeCast ← mkExpectedTypeHint cf.signE neTy
            let hToBool ← mkAppM ``toBool_true_of_ne_nil #[hNeCast]
            let hLt ← mkAppM ``acl2Count_cdr_lt_of_consp #[hToBool]
            let pIHu := mkAppN sihV #[uVal, hLt]
            -- e' = envUpdate e formals (uVal :: otherVals)
            let formalsE ← mkListLit (mkConst ``Symbol) (formals.map reflectSymbol)
            let valsList := uVal :: otherVals.map (·.1)
            let valsE ← mkListLit (mkConst ``SExpr) valsList
            let argsE ← mkListLit (mkConst ``SExpr) (args.map reflectSExpr)
            let e' ← mkAppM ``envUpdate #[eV, formalsE, valsE]
            -- eval e' (var cvar) ↦ uVal (head insert is outermost, defeq)
            let restF ← mkListLit (mkConst ``Symbol)
              (others.map (fun o => reflectSymbol o.1))
            let restV ← mkListLit (mkConst ``SExpr) (otherVals.map (·.1))
            let eInner ← mkAppM ``envUpdate #[eV, restF, restV]
            let hx'raw ← mkAppM ``re_val_var_insert
              #[w, eInner, reflectSymbol cvar, uVal]
            let hx' ← mkExpectedTypeHint hx'raw
              (← mkValConvPropEx w e' (reflectSExpr cvarT) uVal)
            let pIH' := mkAppN pIHu #[e', hx']
            -- substN bridge: eval e (subst pushed) = eval e' pushed
            let hlenPf ← proveByDecide
              (← mkEq (← mkAppM ``List.length #[argsE])
                      (← mkAppM ``List.length #[valsE]))
              "substN arg/val lengths"
            let prodTy ← mkAppM ``Prod #[mkConst ``SExpr, mkConst ``SExpr]
            let pFn ← withLocalDeclD `pr prodTy fun prV => do
              let fst ← mkAppM ``Prod.fst #[prV]
              let snd ← mkAppM ``Prod.snd #[prV]
              mkLambdaFVars #[prV] (← mkValConvPropEx w eV fst snd)
            let entries ← (args.zip valsList).mapM fun (a, vE) => do
              let pairE ← mkAppM ``Prod.mk #[reflectSExpr a, vE]
              pure pairE
            let proofs := hCdrConv :: otherVals.map (·.2)
            let (_, hargsRaw) ← mkForallMemProof prodTy pFn (entries.zip proofs)
            let zipE ← mkAppM ``List.zip #[argsE, valsE]
            let hargsTy ← withLocalDeclD `pr prodTy fun prV => do
              let mem ← mkAppM ``Membership.mem #[zipE, prV]
              mkForallFVars #[prV] (← mkArrow mem (mkApp pFn prV).headBeta)
            let hargs ← mkExpectedTypeHint hargsRaw hargsTy
            let pBridge ← mkAppM ``evalOpt_substTerm_substN
              #[w, eV, formalsE, argsE, valsE, pushedE, hNoLet, hlenPf, hargs]
            return (ctxD, ← mkAppM ``evtrue_of_fuel_eq #[pBridge, pIH'])
          -- dispatch the decision tree; at each leaf replay the case child
          -- and peel ruling literals then IH literals (clause order)
          let rec go (t : CaseTree) (ctxD : ReplayCtx) (facts : List TestFact) :
              MetaM Expr := do
            match t with
            | .split test posT negT => do
              let ctxD ← pinTermOpaques cfg' eV ctxD test
              let vE ← ctxValExpr cfg' ctxD test
              let pV ← ctxValProof cfg' ctxD test
              let nilTy ← mkEq vE nilC
              let negL ← withLocalDeclD `hnil nilTy fun hNil => do
                let body ← go negT ctxD (facts ++
                  [{ test, valueE := vE, convE := pV, sign := false, signE := hNil }])
                mkLambdaFVars #[hNil] body
              let posL ← withLocalDeclD `hne (← mkAppM ``Ne #[vE, nilC]) fun hNe => do
                let body ← go posT ctxD (facts ++
                  [{ test, valueE := vE, convE := pV, sign := true, signE := hNe }])
                mkLambdaFVars #[hNe] body
              mkAppM ``Classical.byCases #[negL, posL]
            | .leaf i => do
              let some (_, c, _, _, _) := linked.find? (fun (j, _, _, _, _) => j == i)
                | throwError "replayInduction: internal — leaf {i} unlinked"
              -- replay the linked child for a SELECTION and peel it down to
              -- EvTrue(∨C): the leading negated ruling tests (nil by the
              -- branch facts), then the selection's ¬L_{jᵢ}σᵢ literals (nil
              -- by the walk's truthy facts)
              let dischargeChild (ctxD : ReplayCtx)
                  (chosen : List (List (Symbol × SExpr) × Nat × Expr)) :
                  MetaM Expr := do
                let key := chosen.map fun (al, j, _) => (al, j)
                let some (_, _, sel, _, child) := linked.find?
                    (fun (ci, _, sel, _, _) =>
                      ci == i && sel.map (fun (al, j, _) => (al, j)) == key)
                  | do
                    -- a DROPPED (tautological) selection: ACL2's clean-up
                    -- removed its trivially-true clause. The discharge is
                    -- direct: some chosen IH literal's σ-instance IS a goal
                    -- literal, and this branch holds its truthiness.
                    unless dropped.any (fun (ci, _, sel, _) =>
                        ci == i && sel.map (fun (al, j, _) => (al, j)) == key) do
                      throwError "replayInduction: no child for case {i} \
                                  selection {repr (key.map (·.2))}"
                    for (al, j, hne) in chosen do
                      let some lj := pushedLits[j]?
                        | throwError "replayInduction: internal — selection \
                                      index {j} out of range"
                      let ljσ := ACL2.Replay.substTerm
                        (al.map (·.1)) (al.map (·.2)) lj
                      if let some m := pushedLits.findIdx? (· == ljσ) then
                        return ← evtrueOfLitTrue cfg' ctxD pushedLits m ljσ hne
                    throwError "replayInduction: dropped selection for case \
                                {i} has no goal-literal witness (frontier)"
                let mut p ← replayClause cfg' ctxD child
                -- ruling-literal peels, clause order
                for t in c.tests do
                  let (litPos, fact) ← do
                    match t with
                    | .cons (.atom (.symbol ns)) (.cons u .nil) =>
                      if ns.name == "not" then
                        match facts.find? (fun f => f.test == u && !f.sign) with
                        | some f => pure (true, f)   -- literal = u, value nil
                        | none => throwError "replayInduction: no nil fact for \
                                              ruling test {repr u}"
                      else
                        match facts.find? (fun f => f.test == t && f.sign) with
                        | some f => pure (false, f)  -- literal = (not t), t truthy
                        | none => throwError "replayInduction: no truthy fact \
                                              for ruling test {repr t}"
                    | _ =>
                      match facts.find? (fun f => f.test == t && f.sign) with
                      | some f => pure (false, f)
                      | none => throwError "replayInduction: no truthy fact for \
                                            ruling test {repr t}"
                  let lit := dumbNegateLit t
                  if litPos then
                    -- literal value = fact value = nil
                    let pLit ← ctxValProof cfg' ctxD lit
                    let pLitNil ← mkAppM ``re_val_cast
                      #[w, eV, reflectSExpr lit, fact.valueE, nilC, pLit, fact.signE]
                    p ← mkAppM ``evtrue_extract_else #[pLitNil, p]
                  else
                    -- literal = (not t); Logic.not (truthy) = nil
                    let pLit ← ctxValProof cfg' ctxD lit
                    let hNotNil ← mkAppM ``not_nil_of_truthy #[fact.signE]
                    let pLitNil ← mkAppM ``re_val_cast
                      #[w, eV, reflectSExpr lit,
                        mkApp (mkConst ``Logic.not) fact.valueE, nilC, pLit, hNotNil]
                    p ← mkAppM ``evtrue_extract_else #[pLitNil, p]
                -- selection-literal peels, clause order: entry (alist, j, hne)
                -- with hne : v(L_jσ) ≠ nil; the clause literal is ¬L_jσ
                for ((al, j, negLit), (_, _, hne)) in sel.zip chosen do
                  let formals := al.map (·.1)
                  let args := al.map (·.2)
                  let some lj := pushedLits[j]?
                    | throwError "replayInduction: internal — selection index \
                                  {j} out of range"
                  let ljσ := ACL2.Replay.substTerm formals args lj
                  let vLjσ ← ctxValExpr cfg' ctxD ljσ
                  let pLit ← ctxValProof cfg' ctxD negLit
                  let pLitNil ←
                    if negLit == (.cons (.atom (.symbol { name := "not" }))
                        (.cons ljσ .nil)) then
                      -- L_j positive: ¬L_jσ = (not L_jσ), Logic.not (truthy) = nil
                      let hNil ← mkAppM ``not_nil_of_truthy #[hne]
                      mkAppM ``re_val_cast
                        #[w, eV, reflectSExpr negLit,
                          mkApp (mkConst ``Logic.not) vLjσ, nilC, pLit, hNil]
                    else do
                      -- L_j = (not U): L_jσ = (not Uσ), ¬L_jσ = Uσ; the truthy
                      -- Logic.not pins Uσ's value to nil (two-valued decode)
                      unless vLjσ.isAppOfArity ``Logic.not 1 do
                        throwError "replayInduction: negative pushed literal \
                                    {repr lj} has non-Logic.not value (frontier)"
                      let hNil ← mkAppM ``nil_of_logic_not_ne_nil #[hne]
                      mkAppM ``re_val_cast
                        #[w, eV, reflectSExpr negLit, vLjσ.appArg!, nilC, pLit, hNil]
                  p ← mkAppM ``evtrue_extract_else #[pLitNil, p]
                return p
              -- WALK one IH's σ-instance disjunction: nil literals peel off
              -- (evtrue_extract_else); the first truthy literal selects that
              -- branch's continuation. The LAST literal's EvTrue is its own
              -- truthy fact — the disjunction being true, no absurd case.
              let walkIH (ctxD : ReplayCtx) (pIH : Expr)
                  (litsσ : List SExpr)
                  (k : ReplayCtx → Nat → Expr → MetaM Expr) : MetaM Expr := do
                let rec goW (ctxD : ReplayCtx) (pCur : Expr) (j : Nat)
                    (rest : List SExpr) : MetaM Expr := do
                  match rest with
                  | [] => throwError "replayInduction: empty IH disjunction walk"
                  | [l] => do
                    let ctxD ← pinTermOpaques cfg' eV ctxD l
                    let pL ← ctxValProof cfg' ctxD l
                    -- pCur : EvTrue(l) — truthiness direct
                    let hne ← mkAppM ``ne_nil_of_evtrue_conv #[pCur, pL]
                    k ctxD j hne
                  | l :: restL => do
                    let ctxD ← pinTermOpaques cfg' eV ctxD l
                    let vL ← ctxValExpr cfg' ctxD l
                    let pL ← ctxValProof cfg' ctxD l
                    let negB ← withLocalDeclD `hnil (← mkEq vL nilC) fun hNil => do
                      let pNil ← mkAppM ``re_val_cast
                        #[w, eV, reflectSExpr l, vL, nilC, pL, hNil]
                      let pRest ← mkAppM ``evtrue_extract_else #[pNil, pCur]
                      mkLambdaFVars #[hNil] (← goW ctxD pRest (j + 1) restL)
                    let posB ← withLocalDeclD `hne (← mkAppM ``Ne #[vL, nilC]) fun hNe => do
                      mkLambdaFVars #[hNe] (← k ctxD j hNe)
                    mkAppM ``Classical.byCases #[negB, posB]
                goW ctxD pIH 0 litsσ
              -- nest the walks over the case's IHs (clause order), then
              -- discharge the selected child
              let rec goIHs (ctxD : ReplayCtx)
                  (alists : List (List (Symbol × SExpr)))
                  (chosen : List (List (Symbol × SExpr) × Nat × Expr)) :
                  MetaM Expr := do
                match alists with
                | [] => dischargeChild ctxD chosen
                | alist :: restA => do
                  let (ctxD, pIH) ← ihDisjTruth ctxD facts alist
                  let litsσ := pushedLits.map
                    (ACL2.Replay.substTerm (alist.map (·.1)) (alist.map (·.2)))
                  walkIH ctxD pIH litsσ fun ctxD j hne =>
                    goIHs ctxD restA (chosen ++ [(alist, j, hne)])
              goIHs ctxD c.alists []
          let body ← go tree ctx0 []
          mkLambdaFVars #[hX] body
        mkLambdaFVars #[eV] inner3
      mkLambdaFVars #[sihV] inner2
    mkLambdaFVars #[xvV] inner
  -- 6. apply the induction and instantiate at the ambient env's controller value
  let indP ← mkAppM ``acl2_strong_induction_count #[P, step]
  let hNotT ← proveIsNamedFalse cvar "t"
  let hxv ← mkAppM ``re_val_var #[w, cfg.envExpr, reflectSymbol cvar, hNotT]
  let xv0 ← dpConcVar cfg.envExpr cvar
  return mkAppN indP #[xv0, cfg.envExpr, ← pure hxv] |>.headBeta

end

/-- Replay a whole theorem's proof tree to its mirror statement
    `EvTrue w env cp.formula` (G2: ACL2's own truthiness claim). -/
def replayProof (cfg : ReplayConfig) (cp : ClauseProof) : MetaM Expr := do
  match cp.root with
  | none => throwError "replayProof: theorem {cp.name} has no proof tree"
  | some root => replayClause cfg ReplayCtx.empty root


/-- Prove `total:fn` (the `mkTotalityHypType` statement) from the admission
    data; throws a named-frontier error when out of the D5 scope. -/
def proveTotality (cfg : ReplayConfig)
    (totalEnv : List (String × Nat × Expr))
    (name : String) (formals : List Symbol) (body : SExpr)
    (just? : Option Justification) : MetaM Expr := do
  let fs : Symbol := { name := name }
  let hNs ← proveNotSpecial fs
  let hDef ← totWalk.totDefFact cfg fs formals body
  let mkEnvE (avs : List Expr) : MetaM Expr := do
    let formalsE ← mkListLit (mkConst ``Symbol) (formals.map reflectSymbol)
    let avsE ← mkListLit (mkConst ``SExpr) avs
    mkAppM ``bindArgs #[formalsE, avsE]
  let varProofs (envE : Expr) (avs : List Expr) : MetaM (List (Symbol × Expr × Expr)) := do
    match formals, avs with
    | [f], [av] =>
      let g ← mkAppM ``bindArgs_single_get_self #[reflectSymbol f, av]
      let p ← mkAppM ``re_val_var_get #[cfg.worldExpr, envE, reflectSymbol f, av, g]
      return [(f, av, p)]
    | [f1, f2], [av1, av2] =>
      let hne ← mkDecideProof (← mkAppM ``Ne #[reflectSymbol f1, reflectSymbol f2])
      let g1 ← mkAppM ``bindArgs_pair_get_fst #[reflectSymbol f1, reflectSymbol f2, av1, av2]
      let g2 ← mkAppM ``bindArgs_pair_get_snd #[reflectSymbol f1, reflectSymbol f2, av1, av2, hne]
      let p1 ← mkAppM ``re_val_var_get #[cfg.worldExpr, envE, reflectSymbol f1, av1, g1]
      let p2 ← mkAppM ``re_val_var_get #[cfg.worldExpr, envE, reflectSymbol f2, av2, g2]
      return [(f1, av1, p1), (f2, av2, p2)]
    | _, _ => throwError "proveTotality: arity {formals.length} unsupported (frontier)"
  match just? with
  | none =>
    -- NON-RECURSIVE: the body walk alone
    match formals with
    | [_] =>
      let hbody ← withLocalDeclD `av (mkConst ``SExpr) fun av => do
        let envE ← mkEnvE [av]
        let vals ← varProofs envE [av]
        let p ← totWalk cfg envE vals [] totalEnv none body
        mkLambdaFVars #[av] p
      mkAppM ``totality_1_of_body
        #[cfg.worldExpr, reflectSymbol fs, reflectSymbol formals[0]!,
          reflectSExpr body, hNs, hDef, hbody]
    | [_, _] =>
      let hbody ← withLocalDeclD `av1 (mkConst ``SExpr) fun av1 =>
        withLocalDeclD `av2 (mkConst ``SExpr) fun av2 => do
          let envE ← mkEnvE [av1, av2]
          let vals ← varProofs envE [av1, av2]
          let p ← totWalk cfg envE vals [] totalEnv none body
          mkLambdaFVars #[av1, av2] p
      mkAppM ``totality_2_of_body
        #[cfg.worldExpr, reflectSymbol fs, reflectSymbol formals[0]!,
          reflectSymbol formals[1]!, reflectSExpr body, hNs, hDef, hbody]
    | _ => throwError "proveTotality: arity {formals.length} unsupported (frontier)"
  | some just =>
    -- RECURSIVE (D5 scope): measure (acl2-count m), o<, single measured formal
    unless just.wfRel.name == "o<" do
      throwError "proveTotality: well-founded relation {just.wfRel.name} \
          unsupported (frontier: o< only)"
    let some measuredFormal := just.measuredSubset.head?
      | throwError "proveTotality: empty measured subset"
    unless just.measuredSubset.length == 1 do
      throwError "proveTotality: multi-formal measured subset unsupported \
          (frontier)"
    let wantedMeasure : SExpr :=
      .cons (.atom (.symbol { name := "acl2-count" }))
        (.cons (.atom (.symbol { name := measuredFormal.name })) .nil)
    unless just.measure == wantedMeasure do
      throwError "proveTotality: measure {repr just.measure} unsupported \
          (frontier: (acl2-count <measured-formal>) only)"
    -- D9: the (o-p (measure)) obligation is absorbed by the Nat-typed
    -- measure; SHAPE-CHECK it (hard-fail on anything unexpected)
    let opClause : SExpr :=
      .cons (.cons (.atom (.symbol { name := "o-p" }))
        (.cons wantedMeasure .nil)) .nil
    unless just.terminationClauses.any (· == opClause) do
      throwError "proveTotality: expected (o-p {repr wantedMeasure}) \
          obligation not found (emission shape changed?)"
    let countOf (e : Expr) : MetaM Expr := mkAppM ``SExpr.acl2Count #[e]
    match formals with
    | [f1] =>
      unless measuredFormal == f1 do
        throwError "proveTotality: measured formal mismatch"
      let step ← withLocalDeclD `av (mkConst ``SExpr) fun av => do
        let envEat := fun (bv : Expr) => do
          let formalsE ← mkListLit (mkConst ``Symbol) [reflectSymbol f1]
          let avsE ← mkListLit (mkConst ``SExpr) [bv]
          mkAppM ``bindArgs #[formalsE, avsE]
        let ihType ← withLocalDeclD `bv (mkConst ``SExpr) fun bv => do
          let lt ← mkAppM ``Nat.lt #[← countOf bv, ← countOf av]
          let envB ← envEat bv
          let conv ← mkConvPropEx cfg.worldExpr envB (reflectSExpr body)
          mkForallFVars #[bv] (← mkArrow lt conv)
        withLocalDeclD `ih ihType fun ih => do
          let envE ← envEat av
          let vals ← varProofs envE [av]
          let p ← totWalk cfg envE vals [] totalEnv
            (some (name, measuredFormal, ih, just)) body
          mkLambdaFVars #[av, ih] p
      mkAppM ``totality_1_rec
        #[cfg.worldExpr, reflectSymbol fs, reflectSymbol f1,
          reflectSExpr body, hNs, hDef, step]
    | [f1, f2] =>
      let envEat := fun (bv cv : Expr) => do
        let formalsE ← mkListLit (mkConst ``Symbol)
          [reflectSymbol f1, reflectSymbol f2]
        let avsE ← mkListLit (mkConst ``SExpr) [bv, cv]
        mkAppM ``bindArgs #[formalsE, avsE]
      if measuredFormal == f1 then
        let step ← withLocalDeclD `av1 (mkConst ``SExpr) fun av1 => do
          let ihType ← withLocalDeclD `bv (mkConst ``SExpr) fun bv => do
            let lt ← mkAppM ``Nat.lt #[← countOf bv, ← countOf av1]
            let inner ← withLocalDeclD `cv (mkConst ``SExpr) fun cv => do
              let envB ← envEat bv cv
              let conv ← mkConvPropEx cfg.worldExpr envB (reflectSExpr body)
              mkForallFVars #[cv] conv
            mkForallFVars #[bv] (← mkArrow lt inner)
          withLocalDeclD `ih ihType fun ih =>
            withLocalDeclD `av2 (mkConst ``SExpr) fun av2 => do
              let envE ← envEat av1 av2
              let vals ← varProofs envE [av1, av2]
              let p ← totWalk cfg envE vals [] totalEnv
                (some (name, measuredFormal, ih, just)) body
              mkLambdaFVars #[av1, ih, av2] p
        mkAppM ``totality_2_rec
          #[cfg.worldExpr, reflectSymbol fs, reflectSymbol f1, reflectSymbol f2,
            reflectSExpr body, hNs, hDef, step]
      else if measuredFormal == f2 then
        -- measured on the SECOND formal (e.g. (rm e x) / (memb a x) on x):
        -- strong induction on av2's count, av1 inner-∀ (totality_2_rec_snd)
        let step ← withLocalDeclD `av2 (mkConst ``SExpr) fun av2 => do
          let ihType ← withLocalDeclD `cv (mkConst ``SExpr) fun cv => do
            let lt ← mkAppM ``Nat.lt #[← countOf cv, ← countOf av2]
            let inner ← withLocalDeclD `bv (mkConst ``SExpr) fun bv => do
              let envB ← envEat bv cv
              let conv ← mkConvPropEx cfg.worldExpr envB (reflectSExpr body)
              mkForallFVars #[bv] conv
            mkForallFVars #[cv] (← mkArrow lt inner)
          withLocalDeclD `ih ihType fun ih =>
            withLocalDeclD `av1 (mkConst ``SExpr) fun av1 => do
              let envE ← envEat av1 av2
              let vals ← varProofs envE [av1, av2]
              let p ← totWalk cfg envE vals [] totalEnv
                (some (name, measuredFormal, ih, just)) body
              mkLambdaFVars #[av2, ih, av1] p
        mkAppM ``totality_2_rec_snd
          #[cfg.worldExpr, reflectSymbol fs, reflectSymbol f1, reflectSymbol f2,
            reflectSExpr body, hNs, hDef, step]
      else
        throwError "proveTotality: measured formal {measuredFormal.name} is \
            not among the formals (internal)"
    | _ => throwError "proveTotality: recursive arity {formals.length} \
        unsupported (frontier)"

/-- #37: the admission-derived totality environment — per fn (DEVELOPMENT
    order; `defs.entries` is insertion-reversed), try `proveTotality`,
    accumulating proofs for later fns' calls. A frontier failure leaves the
    fn out (it stays hypothesis-backed downstream — D6). -/
def buildTotalEnv (cfg : ReplayConfig)
    (justs : List (String × Justification))
    (upTo : Option String := none) :
    MetaM (List (String × Nat × Expr)) := do
  let mut totalEnv : List (String × Nat × Expr) := []
  for (s, formals, body) in cfg.worldVal.defs.entries.reverse do
    try
      let pf ← proveTotality cfg totalEnv s.name formals body
        (justs.lookup s.name)
      totalEnv := (s.name, formals.length, pf) :: totalEnv
    catch e =>
      -- keep ONLY the prover's own frontier-class failures (the fn stays
      -- hypothesis-backed — D6); anything else is a real defect: surface it
      let msg ← e.toMessageData.toString
      unless msg.startsWith "proveTotality:" do
        throw e
    if upTo == some s.name then
      break
  return totalEnv

/-- The CONDITIONAL generic mirror: bind the machine-generated hypothesis
    telescope (per defined fn: totality; plus the lifted TP corollary when one was
    emitted), replay the theorem under it, and λ-abstract. Returns the proof and
    the condition descriptions (the c2 pattern — obligations explicit in the
    type, discharged later by termination emission / Driver Stage 5). -/
def replayProofConditional (cfg : ReplayConfig) (tps : List (String × SExpr))
    (cp : ClauseProof) (justs : List (String × Justification) := [])
    (rules : List RuleSpec := []) :
    MetaM (Expr × List String) := do
  let fns := cfg.worldVal.defs.entries
  -- hypothesis declarations: totality for every defined fn, TP where
  -- emitted. #37 discharges USED totality hypotheses LAZILY after the
  -- replay (prove + substitute) — so theorems that consume no totality pay
  -- nothing, and the per-theorem prover cost is proportional to use.
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
  -- rule:<thm> hypothesis declarations — only rules created BEFORE this theorem
  -- can be cited by its proof, and the caller passes the development's rules in
  -- creation order, so the same list works for every theorem (unused offers are
  -- dropped by the used-filter below). Binder names are disambiguated by
  -- position when one defthm and-split into several rules of the same name.
  -- Only EQUAL-class rules are offered (the `liftable` TP precedent): an
  -- iff/user-equivalence rule's hypothesis shape is an L2 frontier — the fact
  -- is simply not offered, never mis-stated, and a node applying such a rule
  -- hard-fails at the use site ("no stored-rule hypothesis in scope").
  let rules := rules.filter (·.equiv == "equal")
  let ruleDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
    (rules.zipIdx.map fun (r, i) =>
      let nm := if (rules.filter (·.name == r.name)).length > 1 then
        s!"hrule_{r.name}_{i}" else s!"hrule_{r.name}"
      (Name.mkSimple nm, BinderInfo.default,
       fun (_ : Array Expr) => mkRuleHypType cfg r)).toArray
  let condsAll :=
    fns.map (fun (s, _, _) => s!"total:{s.name}") ++
    tpFns.map (fun (s, _, _) => s!"tp:{s.name}") ++
    rules.map (fun r => s!"rule:{r.name}")
  withLocalDecls totalDecls fun totalVs => do
    withLocalDecls tpDecls fun tpVs => do
     withLocalDecls ruleDecls fun ruleVs => do
      let ctx : ReplayCtx :=
        { totalHyps := (fns.map (fun (s, _, _) => s.name)).zip totalVs.toList,
          tpHyps := (tpFns.zip tpVs.toList).map fun ((s, _, cor), h) => (s.name, cor, h),
          ruleHyps := rules.zip ruleVs.toList }
      let some root := cp.root
        | throwError "replayProofConditional: theorem {cp.name} has no proof tree"
      let prf ← instantiateMVars (← replayClause cfg ctx root)
      -- defense-in-depth (audit 2026-07-06): PIN the replayed proof to the
      -- root clause's own mirror statement — fidelity must not rest solely
      -- on each handler targeting cn.inputClause
      let rootTy ← mkAppM ``EvTrue
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr (disjoinTerm root.inputClause)]
      let prf ← mkExpectedTypeHint prf rootTy
      -- bind only the hypotheses the replay ACTUALLY USED: an unconsumed offer must
      -- not weaken the statement (hypothesis types are mutually independent, so
      -- dropping unused ones is well-formed).
      let used := (condsAll.zip (totalVs ++ tpVs ++ ruleVs).toList).filter
        fun (_, v) => prf.containsFVar v.fvarId!
      -- #37 LAZY discharge: prove admission totality only for the USED
      -- total: hypotheses (the dev-order dependency prefix, once, up to the
      -- last used fn) and SUBSTITUTE; frontier failures keep the hypothesis
      -- (D6 — visible in the type).
      let usedTotalNames := used.filterMap fun (c, _) =>
        if c.startsWith "total:" then some ((c.drop "total:".length).toString) else none
      let totalEnv ←
        if usedTotalNames.isEmpty then pure []
        else
          let lastUsed? := (cfg.worldVal.defs.entries.reverse.filter
            (fun (s, _, _) => usedTotalNames.contains s.name)).getLast?
          buildTotalEnv cfg justs (upTo := lastUsed?.map (fun (s, _, _) => s.name))
      let mut prf := prf
      let mut kept : List (String × Expr) := []
      for (c, v) in used do
        match (if c.startsWith "total:" then
                totalEnv.find? (fun (n, _, _) => s!"total:{n}" == c)
              else none) with
        | some (_, _, pf) => prf := prf.replaceFVar v pf
        | none => kept := kept ++ [(c, v)]
      let p ← mkLambdaFVars (kept.map (·.2)).toArray prf
      return (p, kept.map (·.1))


/-! ## Importer front-end helpers (promoted from the test harness)

`derive_world` defines a `World` constant PROJECTED from a parsed
`Development` (the world the replay reasons over is derived from the log, not
hand-written); `findThm` extracts a theorem's reconstructed proof from a
development by name. -/

/-- Theorems of a development, each paired with the STORED rules created
    BEFORE it — the rules its proof could cite (creation order; ACL2's
    certification order makes citing a later rule impossible, so the offer
    is exactly the citable set). -/
partial def developmentTheoremsWithRules (dev : Development)
    (acc : List RuleSpec := []) : List (ClauseProof × List RuleSpec) :=
  match dev with
  | .bind (.theorem cp) rest => (cp, acc) :: developmentTheoremsWithRules rest acc
  | .bind (.rules specs) rest => developmentTheoremsWithRules rest (acc ++ specs)
  | .bind _ rest => developmentTheoremsWithRules rest acc
  | .done => []

/-- The stored rules created BEFORE the first theorem named `nm`
    (case-insensitive) — the `rules` argument for replaying it by name. -/
def rulesBefore (dev : Development) (nm : String) : List RuleSpec :=
  match (developmentTheoremsWithRules dev).find?
    (fun (cp, _) => cp.name.toLower == nm.toLower) with
  | some (_, rules) => rules
  | none => []

/-- All theorems matching a name (case-insensitive), in development order. -/
partial def findThms : Development → String → List ClauseProof
  | .bind (.theorem cp) rest, nm =>
    if cp.name.toLower == nm.toLower then cp :: findThms rest nm
    else findThms rest nm
  | .bind _ rest, nm => findThms rest nm
  | .done, _ => []

/-- The UNIQUE theorem named `nm` (case-insensitive). `none` when absent — and
    also when AMBIGUOUS (two theorems differing only in case): selecting the
    first match would silently pick a theorem the caller did not name, so we
    refuse to guess (fail-closed; audited 2026-06-10). -/
def findThm (dev : Development) (nm : String) : Option ClauseProof :=
  match findThms dev nm with
  | [cp] => some cp
  | _ => none

open Lean.Elab Lean.Elab.Command in
/-- `derive_world name from devTerm` — define `name : World` as the world
    PROJECTED from a `Development` (`Development.toWorld`), REFLECTED to a
    concrete (fast-reducing) def. -/
elab "derive_world " id:ident " from " t:term : command => do
  let ns ← Lean.getCurrNamespace
  liftTermElabM do
    let devE ← Lean.Elab.Term.elabTermAndSynthesize t (some (mkConst ``ACL2.Development))
    let dev ← unsafe Lean.Meta.evalExpr ACL2.Development (mkConst ``ACL2.Development) devE
    Lean.addAndCompile <| .defnDecl
      { name := ns ++ id.getId, levelParams := [], type := mkConst ``ACL2.World,
        value := ← reflectWorld dev.toWorld, hints := .abbrev, safety := .safe }
    Lean.enableRealizationsForConst (ns ++ id.getId)

end ACL2.Replay.Driver
