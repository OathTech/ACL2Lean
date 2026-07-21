/-
  Driver/NodeCore — split from the monolithic Driver.lean (WP2 Stage 1,
  2026-07-17; see docs/plans/2026-07-18_driver-modular-refactor.md).

  ReplayCtx/ReplayConfig, registries, value characterization, and the
  node-level recipes (replayRecognizer; the replayDefinition/replayNode/
  replayRewrites knot).
-/
import ACL2Lean.Replay.Driver.Reflect

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

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
  /-- The development's ground-zero SNAPSHOT defuns — (name, formals, emitted
      body) as EMITTED (`Development.groundZeroSnapshotDefs`, D3/WP1-WP2).
      Two consumers: the totality prover's lazy `upTo` bound treats these
      names as always-in-scope (they logically precede the whole
      development), and the D4 definition-fact route reads a builtin's
      recorded body from here (builtin-named snapshots are EXCLUDED from the
      world — no-shadow — so this is the only place their emission lives).
      Empty for synthetic test worlds. -/
  gzDefs : List (Symbol × List Symbol × SExpr) := []
  /-- The development's admission justifications (fn ↦ measure/wfrel/
      measured-subset + RAW termination clauses) — the I4 covering join
      reads a scheme fn's emitted decrease clauses from here (J2; the
      totality prover receives the same data as a parameter). Empty for
      synthetic test worlds — an induction replay then hard-fails at the
      covering check, never guesses. -/
  justs : List (String × Justification) := []

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
    if s.name == "EQUAL" && x == x' then some x else none
  | _ => none

def runeOf : ProofNode → Rune | .node r _ _ _ _ => r
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
  [("NOT",      ``Logic.not,      ``callBuiltin_not),
   ("ZP",       ``Logic.zp,       ``callBuiltin_zp),
   ("CONSP",    ``Logic.consp,    ``callBuiltin_consp),
   ("INTEGERP", ``Logic.integerp, ``callBuiltin_integerp),
   ("ACL2-NUMBERP", ``Logic.acl2Numberp, ``callBuiltin_acl2_numberp),
   ("TRUE-LISTP", ``Logic.trueListp, ``callBuiltin_true_listp),
   ("CAR",      ``Logic.car,      ``callBuiltin_car),
   ("CDR",      ``Logic.cdr,      ``callBuiltin_cdr),
   ("SYMBOLP",  ``Logic.symbolp,  ``callBuiltin_symbolp),
   ("STRINGP",  ``Logic.stringp,  ``callBuiltin_stringp),
   ("RATIONALP", ``Logic.rationalp, ``callBuiltin_rationalp),
   ("BOOLEANP", ``Logic.booleanp, ``callBuiltin_booleanp),
   ("NFIX",     ``Logic.nfix,     ``callBuiltin_nfix),
   ("FIX",      ``Logic.fix,      ``callBuiltin_fix),
   ("LEN",      ``Logic.len,      ``callBuiltin_len),
   ("ENDP",     ``Logic.endp,     ``callBuiltin_endp),
   ("ATOM",     ``Logic.atom,     ``callBuiltin_atom)]

/-- DP-lift primitives (binary). -/
def dpBinary : List (String × Name × Name) :=
  [("EQUAL",    ``Logic.equal,   ``callBuiltin_equal),
   ("<",        ``Logic.lt,      ``callBuiltin_lt),
   ("LEXORDER", ``ACL2.lexorder, ``callBuiltin_lexorder),
   ("BINARY-+", ``Logic.plus,    ``callBuiltin_plus),
   ("BINARY-*", ``Logic.times,   ``callBuiltin_times),
   ("CONS",     ``SExpr.cons,    ``callBuiltin_cons),
   ("IMPLIES",  ``Logic.implies, ``callBuiltin_implies),
   ("IFF",      ``Logic.iff,     ``callBuiltin_iff)]

-- INVARIANT (load-bearing — the G3 audit's dpOpqKeyOk↔collectOpaques matrix):
-- `dpLiftHeads` must be EXACTLY the names of `dpUnary ++ dpBinary`. The meta
-- walkers (`dpValExpr`, `collectOpaques` via `dpKnownHead`) dispatch off the
-- registries, while the verified lift (`dpLiftF`, `dpOpqKeyOk`) dispatches off
-- `dpLiftHeads`; extending one side without the other silently desynchronizes
-- the lift premise from the collected opaque set. Set equality, both directions:
#guard dpLiftHeads.all (fun n => (dpUnary.lookup n).isSome || (dpBinary.lookup n).isSome)
#guard (dpUnary.map (·.1) ++ dpBinary.map (·.1)).all (dpLiftHeads.contains ·)

/-- D4 DEFINITION-FACT registry (external-knowledge design §D4, WP2): builtins
    that ACL2 itself defines by defun. Their `(:DEFINITION <fn>)` runes replay
    through the registered `gz_def_<fn>` body lemma (EvalLemmas) instead of a
    world entry — builtin-named ground-zero snapshots are EXCLUDED from the
    world (no-shadow, `builtinNames`), so `evalOpt` dispatches them to
    `callBuiltin` and the unfold is the lemma's callBuiltin-vs-emitted-body
    agreement (`replayBuiltinDefUnfold`). Every entry must also be in
    `dpUnary` (which supplies the `Logic` value function and the `callBuiltin`
    rfl lemma) — guarded below. -/
def d4DefFacts : List (String × Name) :=
  [("TRUE-LISTP", ``gz_def_true_listp),
   ("LEN",        ``gz_def_len),
   ("NFIX",       ``gz_def_nfix),
   ("FIX",        ``gz_def_fix),
   ("BOOLEANP",   ``gz_def_booleanp),
   ("ENDP",       ``gz_def_endp),
   ("ATOM",       ``gz_def_atom)]

#guard d4DefFacts.all (fun e => (dpUnary.lookup e.1).isSome)
#guard d4DefFacts.all (fun e => builtinNames.contains e.1)

/-- Is this head a DP-lift special form or primitive? (Anything else with a symbol
    head is an OPAQUE user-fn application.) -/
def dpKnownHead (name : String) : Bool :=
  name == "QUOTE" || name == "IF" ||
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
    if qs.name == "QUOTE" then
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
    if fs.name == "IF" then
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
    if fs.name == "QUOTE" then return reflectSExpr a
    else match dpUnary.lookup fs.name with
      | some (fn, _) => return mkApp (mkConst fn) (← dpValExpr opq varVal a)
      | none => throwError "dpValExpr: unary {fs.name} is not a DP-lift primitive: {repr t}"
  | .cons (.atom (.symbol fs)) (.cons a (.cons b .nil)) =>
    match dpBinary.lookup fs.name with
    | some (fn, _) =>
      return mkApp2 (mkConst fn) (← dpValExpr opq varVal a) (← dpValExpr opq varVal b)
    | none => throwError "dpValExpr: binary {fs.name} is not a DP-lift primitive: {repr t}"
  | .cons (.atom (.symbol fs)) (.cons c (.cons th (.cons e .nil))) =>
    if fs.name == "IF" then
      let vc ← dpValExpr opq varVal c
      let vt ← dpValExpr opq varVal th
      let ve ← dpValExpr opq varVal e
      mkAppM ``cond #[mkApp (mkConst ``Logic.toBool) vc, vt, ve]
    else throwError "dpValExpr: ternary {fs.name} is not a DP-lift primitive: {repr t}"
  | .cons (.cons (.atom (.symbol lam)) _) _ =>
    -- a LAMBDA application (ACL2's translated LET) is WELL-FORMED input the
    -- DP-lift walkers do not support yet (surfaced by ground-zero snapshot
    -- bodies, e.g. SYMBOL< — WP1): a capability FRONTIER, not a defect.
    if lam.name == "LAMBDA" then
      throwFrontier m!"dpValExpr: LAMBDA (translated LET) application \
                      unsupported (frontier): {repr t}"
    else throwError "dpValExpr: unsupported term shape: {repr t}"
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
    if fs.name == "QUOTE" then
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
      if fs.name == "IF" then throwError "dpValProof: malformed if (2 args): {repr t}"
      else throwError "dpValProof: binary {fs.name} is not a DP-lift primitive"
  | .cons (.atom (.symbol fs)) (.cons c (.cons th (.cons e .nil))) =>
    if fs.name == "IF" then
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
  | .cons (.cons (.atom (.symbol lam)) _) _ =>
    -- LAMBDA application (translated LET): well-formed, unsupported —
    -- frontier, not defect (see the dpValExpr twin arm).
    if lam.name == "LAMBDA" then
      throwFrontier m!"dpValProof: LAMBDA (translated LET) application \
                      unsupported (frontier): {repr t}"
    else throwError "dpValProof: unsupported term shape: {repr t}"
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
  unless impS.name == "IMPLIES" do
    throwError "definition:implies — lhs head {impS.name}"
  let expectedRhs : SExpr :=
    .cons (.atom (.symbol { name := "IF" }))
      (.cons A (.cons (.cons (.atom (.symbol { name := "IF" }))
        (.cons B (.cons quoteT (.cons quoteNil .nil))))
        (.cons quoteT .nil)))
  unless rhs == expectedRhs do
    throwError "definition:implies — rhs {repr rhs} is not the unfold body instance"
  let vA ← ctxValExpr cfg ctx A
  let vB ← ctxValExpr cfg ctx B
  let pA ← ctxValProof cfg ctx A
  let pB ← ctxValProof cfg ctx B
  let hNs ← proveNotSpecial { name := "IMPLIES" }
  let hNo ← proveNoShadow cfg { name := "IMPLIES" }
  let hr ← mkAppM ``callBuiltin_implies #[vA, vB]
  let pL ← mkAppM ``conv_builtin2
    #[cfg.worldExpr, cfg.envExpr, reflectSymbol { name := "IMPLIES" },
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

/-! ## Shared composition helpers (de-dup pass, 2026-07-21)

Single homes for compositions that had grown near-clones across the clause
walkers — extracted behavior-preserving (see CLAUDE.md's engineering-quality
policy; the risk managed is a fix landing in one clone and missing its twin). -/

/-- Falsity of a segment literal from the composer's byCases `facts`:
    a ¬sign fact for the literal itself, or — for a `(not T)` literal — a
    sign fact for `T` lifted by `not_nil_of_truthy` (if-interp's
    convert-assumptions rule set). The FACTS-based core shared by the
    branch-selection and vacuous-residual paths; callers layer their own
    extra sources (the open leaf's own falsity, `ctx.litFactByTerm?`). -/
def segFactFalsity (facts : List (SExpr × Expr × Bool × Expr)) (L : SExpr) :
    MetaM (Option Expr) := do
  if let some (_, _, _, hf) :=
      facts.find? (fun (T, _, sign, _) => !sign && L == T) then
    return some hf
  match L with
  | .cons (.atom (.symbol ns)) (.cons T .nil) =>
    if ns.name == "NOT" then
      match facts.find? (fun (T', _, sign, _) => sign && T' == T) with
      | some (_, _, _, hf) => return some (← mkAppM ``not_nil_of_truthy #[hf])
      | none => return none
    else return none
  | _ => return none

/-- Ex-falso closure of a VACUOUS residual: the pushed child's clause
    (`expected`, proved as `pChild`) is all-false in scope — peel it to its
    last literal (`evtrue_extract_else`) and refute (`absurd`), producing
    `EvTrue goalTerm`. `deriveF` supplies each literal's falsity proof
    (throwing if unavailable). Shared by the spine walker's and
    composeSplit's vacuous arms. -/
def vacuousResidualClose (cfg : ReplayConfig) (ctx : ReplayCtx)
    (expected : List SExpr) (pChild : Expr) (goalTerm : SExpr)
    (deriveF : SExpr → MetaM Expr) : MetaM Expr := do
  let nilC := mkConst ``SExpr.nil
  let mut p := pChild
  for L in expected.dropLast do
    let hf ← deriveF L
    let pNil ← mkAppM ``re_val_cast
      #[cfg.worldExpr, cfg.envExpr, reflectSExpr L, ← ctxValExpr cfg ctx L,
        nilC, ← ctxValProof cfg ctx L, hf]
    p ← mkAppM ``evtrue_extract_else #[pNil, p]
  let some lastL := expected.getLast?
    | throwError "vacuousResidualClose: empty residual clause"
  let hfLast ← deriveF lastL
  let hNe ← mkAppM ``ne_nil_of_evtrue_conv #[p, ← ctxValProof cfg ctx lastL]
  let goalTy ← mkAppM ``EvTrue
    #[cfg.worldExpr, cfg.envExpr, reflectSExpr goalTerm]
  mkAppOptM ``absurd #[none, some goalTy, some hfLast, some hNe]

/-- `(if <c> thn els) ≡ <taken branch>` for a QUOTED-CONSTANT test `c`
    (quote term around value `cv`): `re_if_false` on nil (via `re_val_cast`),
    else `re_if_true`. Branch value/proof from the ctx pins. Returns the
    equality and the taken branch. Shared by the identity-arm and
    folded-collapse display-fold recipes and collapseEval's constant arm. -/
def mkConstTestCollapse (cfg : ReplayConfig) (ctx : ReplayCtx)
    (c cv thn els : SExpr) : MetaM (Expr × SExpr) := do
  let hc ← mkAppM ``re_val_quote
    #[cfg.worldExpr, cfg.envExpr, reflectSExpr cv]
  if cv == SExpr.nil then
    let hcNil ← mkAppM ``re_val_cast
      #[cfg.worldExpr, cfg.envExpr, reflectSExpr c, reflectSExpr cv,
        mkConst ``SExpr.nil, hc, ← proveByDecide
          (← mkEq (reflectSExpr cv) (mkConst ``SExpr.nil)) "cv is nil"]
    let vb ← ctxValExpr cfg ctx els
    let hb ← ctxValProof cfg ctx els
    let _ := vb
    let p ← mkAppM ``re_if_false
      #[cfg.worldExpr, cfg.envExpr, reflectSExpr c, reflectSExpr thn,
        reflectSExpr els, vb, hcNil, hb]
    return (p, els)
  else
    let hcv ← proveByDecide
      (← mkEq (mkApp (mkConst ``Logic.toBool) (reflectSExpr cv))
              (mkConst ``Bool.true)) "toBool of the constant test"
    let va ← ctxValExpr cfg ctx thn
    let ha ← ctxValProof cfg ctx thn
    let _ := va
    let p ← mkAppM ``re_if_true
      #[cfg.worldExpr, cfg.envExpr, reflectSExpr c, reflectSExpr thn,
        reflectSExpr els, reflectSExpr cv, va, hc, hcv, ha]
    return (p, thn)

/-- Close `EvTrue (disjoin (lit :: restLits))` from the closing literal's
    `pclose : ∃N∀f≥N, eval lit = some t`: bare literal when `restLits` is
    empty, else `conv_if_true` short-circuits the tail. Shared by the
    quoteT-closer and ground-'T-closer paths. -/
def closeOnTrueLit (cfg : ReplayConfig) (lit : SExpr) (restLits : List SExpr)
    (pclose : Expr) : MetaM Expr := do
  if restLits.isEmpty then
    mkAppM ``evtrue_of_eq_t #[pclose]
  else
    let restTerm := disjoinTerm restLits
    let hq ← mkAppM ``re_val_quote
      #[cfg.worldExpr, cfg.envExpr, reflectSExpr SExpr.t]
    let hcv ← proveByDecide
      (← mkEq (mkApp (mkConst ``Logic.toBool) (mkConst ``SExpr.t))
              (mkConst ``Bool.true)) "toBool t"
    let hIf ← mkAppM ``conv_if_true
      #[cfg.worldExpr, cfg.envExpr, reflectSExpr lit, reflectSExpr quoteT,
        reflectSExpr restTerm, mkConst ``SExpr.t, mkConst ``SExpr.t, pclose,
        hcv, hq]
    mkAppM ``evtrue_of_eq_t #[hIf]


/-- PIN the value of every user-fn application occurring in `t` (bottom-up) from
    the bound totality hypotheses, refining to the int-atom shape when the fn's
    emitted TP corollary has the standard `(IF (INTEGERP app) … 'NIL)` shape. -/
partial def pinTermOpaques (cfg : ReplayConfig) (envExpr : Expr) (ctx : ReplayCtx)
    (t : SExpr) : MetaM ReplayCtx := do
  match t with
  | .cons (.atom (.symbol fs)) argSpine =>
    if fs.name == "QUOTE" then return ctx
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
        unless ifS.name == "IF" && intS.name == "INTEGERP" do
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
    if q.name == "QUOTE" then (if pat == t then some σ else none)
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
def mkForallMemProof (entryTy P : Expr) (entries : List (Expr × Expr)) :
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

/-- The D4 BUILTIN-DEFINITION unfold (design §D4, WP2): `(fn a) ⇒ body[a]` for a
    `callBuiltin` builtin ABSENT from the world, where `body` is the fn's EMITTED
    ground-zero snapshot body (the only record of it — builtin-named snapshots
    are excluded from the world by `builtinNames`, no-shadow). The unfold is
    `fuel_eq_of_conv` of (a) the application's convergence to the builtin value
    (`conv_builtin1` — the world does not define fn, so `evalOpt` dispatches to
    `callBuiltin`) and (b) the body instance's value convergence (the ordinary
    value walker over the emitted body), bridged by the registered
    `gz_def_<fn>` lemma: `Logic.<fn> v = <body value composition>`. The bridge
    applies ONLY if the emitted body's composition unifies with the lemma's
    rhs — the fail-closed recompute-check against the emission; a drifted
    snapshot hard-fails here. Returns (formals, emitted body, unfold) for
    `replayDefinition`'s shared children-chaining tail. -/
def replayBuiltinDefUnfold (cfg : ReplayConfig) (ctx : ReplayCtx)
    (fn : Symbol) (args : List SExpr) : MetaM (List Symbol × SExpr × Expr) := do
  let some bodyLemma := d4DefFacts.lookup fn.name
    | throwError "definition: {fn.name} is not defined in the world and has no \
                  registered D4 definition fact (frontier)"
  let some (logicFn, cbLemma) := dpUnary.lookup fn.name
    | throwError "definition: D4 entry {fn.name} missing from dpUnary (internal)"
  let some (_, formals, body) := cfg.gzDefs.find? (fun e => e.1 == fn)
    | throwError "definition: builtin {fn.name} has no emitted ground-zero \
                  snapshot (emission gap, frontier)"
  let [f1] := formals
    | throwError "definition: D4 builtin {fn.name} snapshot arity \
                  {formals.length} ≠ 1 (frontier)"
  let [a] := args
    | throwError "definition: {fn.name} arity 1 ≠ {args.length} args"
  let substBody := ACL2.Replay.substTerm [f1] [a] body
  let va ← ctxValExpr cfg ctx a
  let pa ← ctxValProof cfg ctx a
  let pBody ← ctxValProof cfg ctx substBody
  let hNs ← proveNotSpecial fn
  let hNo ← proveNoShadow cfg fn
  let rv := mkApp (mkConst logicFn) va
  let hr ← mkAppM cbLemma #[va]
  let pL ← mkAppM ``conv_builtin1
    #[cfg.worldExpr, cfg.envExpr, reflectSymbol fn, reflectSExpr a, va, rv,
      hNs, hNo, pa, hr]
  let valueEq ← mkAppM bodyLemma #[va]
  let unfold ← mkAppM ``fuel_eq_of_conv #[pL, pBody, valueEq]
  return ([f1], body, unfold)

/-- The `(TRUE-LISTP …)` term and its CONS-peels, outermost first:
    `(TRUE-LISTP (CONS a d))` also lists `(TRUE-LISTP d)` (recursively). Each
    peel is a DEFINITIONAL reduction on the value side (`trueListp (cons a d) =
    trueListp d` is a match-arm equation), so a spine fact about any peel
    discharges the original term — the type-set reasoning ACL2 records as
    `fake-rune-for-type-set` on recognizer/true nodes. -/
partial def trueListpConsPeels (term : SExpr) : List SExpr :=
  term :: match term with
  | .cons r@(.atom (.symbol rs))
      (.cons (.cons (.atom (.symbol cs)) (.cons _ (.cons d .nil))) .nil) =>
    if rs.name == "TRUE-LISTP" && cs.name == "CONS" then
      trueListpConsPeels (.cons r (.cons d .nil))
    else []
  | _ => []

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
  -- not-literal elimination, searched over the term AND its true-listp
  -- CONS-peels (each peel definitional on the value side — see
  -- `trueListpConsPeels`): the spine's (not REC)-falsity fact at any peel
  -- depth discharges the original recognizer.
  let notOf (t : SExpr) : SExpr :=
    .cons (.atom (.symbol { name := "NOT" })) (.cons t .nil)
  let hit? := (trueListpConsPeels term).findSome? fun c =>
    (ctx.litFactByTerm? (notOf c)).map (c, ·)
  if let some (cterm, hNil) := hit? then
    match cterm with
    | .cons (.atom (.symbol rs)) _ =>
      -- TWO-VALUED recognizer registry: the spine's (not REC)-falsity fact
      -- forces REC ≠ nil, and a boolean-range lemma lifts that to = t. Each
      -- entry pairs the recognizer's trusted-core lift with its proved
      -- ne-nil→t lemma; an unlisted recognizer stays a named frontier.
      let entry? : Option (Name × Name) :=
        if rs.name == "CONSP" then
          some (``Logic.consp, ``logic_consp_ne_nil_t)
        else if rs.name == "TRUE-LISTP" then
          some (``Logic.trueListp, ``logic_trueListp_ne_nil_t)
        else none
      let some (liftC, neLemma) := entry?
        | throwError "replayRecognizer: not-literal elimination has no \
                      two-valued entry for {rs.name} (frontier)"
      unless verdict == SExpr.t do
        throwError "replayRecognizer: not-literal elimination of {rs.name} \
                    needs verdict t (got {repr verdict})"
      let v ← ctxValExpr cfg ctx cterm      -- <lift> xv, at the hit peel
      unless v.isAppOfArity liftC 1 do
        throwError "replayRecognizer: value of {repr cterm} is not ({liftC} _)"
      let xv := v.appArg!
      let hne ← mkAppM ``logic_not_nil_ne #[v, hNil]
      let hT ← mkAppM neLemma #[xv, hne]
      -- proof/value of the ORIGINAL term; its value is DEFEQ to the peel's
      -- (trueListp's cons match-arm), so the cast composes.
      let p ← ctxValProof cfg ctx term
      return ← mkAppM ``re_val_cast
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr term, v, verdictE, p, hT]
    | _ => throwError "replayRecognizer: not-literal over a non-application"
  match term with
  | .cons (.atom (.symbol rs)) (.cons z .nil) =>
    if rs.name == "ACL2-NUMBERP" then
      let some (vz, pz) := ctx.val? z
        | throwError "replayRecognizer: acl2-numberp argument {repr z} has no pinned value"
      let k ← intValExpr? vz
      unless verdict == SExpr.t do
        throwError "replayRecognizer: acl2-numberp of a pinned int must have verdict t"
      let hNo ← proveNoShadow cfg { name := "ACL2-NUMBERP" }
      mkAppM ``re_acl2_numberp_int #[cfg.worldExpr, cfg.envExpr, reflectSExpr z, k, hNo, pz]
    -- RECOGNIZER-VIA-TYPE-PRESCRIPTION: `(REC (fn args))` ⇒ t where the verdict
    -- comes from `fn`'s EMITTED :TYPE-PRESCRIPTION whose corollary is exactly
    -- `(REC (fn formals))` (e.g. `(CONSP (INSERT E X))` for INSERT — ACL2 tags
    -- this node `type-prescription:<fn>`). The value of `(REC (fn args))` is
    -- `<REC-lift> vz` on `fn`'s opaque pinned value `vz`, which will NOT reduce
    -- to t; the TP hypothesis is what discharges it. Consumed, not inferred —
    -- exactly the source ACL2 records. (fn must be a user application with a
    -- matching TP corollary; anything else falls through to the general case.)
    else if let .cons (.atom (.symbol fs)) argsSpine := z then
      if let some (_, cor, tpHyp) := ctx.tpHyps.find? (fun (nm, _, _) => nm == fs.name) then
        let some (formals, _) := cfg.worldVal.defs.get? fs
          | throwError "replayRecognizer: {fs.name} not defined in the world"
        let args := (argsSpine.toList?).getD []
        -- the corollary, instantiated at the actual args, must BE this term
        -- (so the TP fact proves exactly this recognizer's verdict).
        unless formals.length == args.length ∧
               ACL2.Replay.substTerm formals args cor == term ∧ verdict == SExpr.t do
          throwError "replayRecognizer: TP corollary of {fs.name} ({repr cor}) \
                      does not match {repr term} ⇒ {repr verdict} (frontier)"
        let some (vz, convz) := ctx.val? z
          | throwError "replayRecognizer: {repr z} has no pinned value (TP recognizer, frontier)"
        -- fact : <lifted corollary at args>[appPat ↦ vz] = t  =  (REC-lift vz) = t
        let fact := mkAppN tpHyp ((#[cfg.envExpr] : Array Expr)
          ++ (args.map reflectSExpr).toArray ++ #[vz, convz])
        let p ← ctxValProof cfg ctx term
        let v ← ctxValExpr cfg ctx term
        mkAppM ``re_val_cast
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr term, v, verdictE, p, fact]
      else
        let p ← ctxValProof cfg ctx term
        let v ← ctxValExpr cfg ctx term
        unless ← isDefEq v verdictE do
          throwError "replayRecognizer: value of {repr term} does not reduce to {repr verdict} \
                      (no TP hypothesis for {fs.name})"
        mkAppM ``re_val_cast
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr term, v, verdictE, p, ← mkEqRefl verdictE]
    else
      let p ← ctxValProof cfg ctx term
      let v ← ctxValExpr cfg ctx term
      unless ← isDefEq v verdictE do
        throwError "replayRecognizer: value of {repr term} does not reduce to {repr verdict}"
      let hv ← mkEqRefl verdictE
      mkAppM ``re_val_cast
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr term, v, verdictE, p, hv]
  | _ => throwError "replayRecognizer: not a recognizer application: {repr term}"

/-- The node-level recursion interface (WP2 Stage 2): the knot's entry
    points as a record, so node recipes are top-level defs taking `rec`
    instead of members of one `mutual` block (new recipes land additively).
    Tied ONCE below (`replayNode`/`replayRewrites` — the public names and
    signatures are unchanged from the pre-WP2 mutual). -/
structure NodeRec where
  /-- `replayNode` — the per-node rune dispatcher. -/
  node : ReplayConfig → ReplayCtx → ProofNode → Nat → MetaM Expr
  /-- `replayRewrites` — the chain walker (explicit depth AND strip). -/
  rewrites : ReplayConfig → ReplayCtx → SExpr → List ProofNode → Nat →
    List Nat → MetaM (Option Expr × SExpr)

/-- Bridge rewrite-equal's built-in NIL NORMALIZATION (rewrite.lisp:18089-92,
    unconditional/syntactic — ACL2 never records it): a chain-end mismatch of
    EXACTLY the shape `(EQUAL 'NIL x)` / `(EQUAL x 'NIL)` (reached) vs
    `(IF x 'NIL 'T)` (recorded), SAME `x`. Returns the fuel-eq chain
    `eval reached ≡ eval recorded`, or `none` when the shapes don't match
    (the caller's fail-closed mismatch error stands). -/
def bridgeEqualNilNorm (cfg : ReplayConfig) (ctx : ReplayCtx)
    (reached recorded : SExpr) : MetaM (Option Expr) := do
  let eqT (a b : SExpr) : SExpr :=
    .cons (.atom (.symbol { name := "EQUAL" })) (.cons a (.cons b .nil))
  let .cons (.atom (.symbol ifS)) (.cons x (.cons thn (.cons els .nil))) := recorded
    | return none
  unless ifS.name == "IF" do return none
  -- the NIL forms: recorded (IF x 'NIL 'T)
  if thn == quoteNil && els == quoteT then
    let some lem :=
        (if reached == eqT quoteNil x then some ``re_equal_nil_norm_l
         else if reached == eqT x quoteNil then some ``re_equal_nil_norm_r
         else none) | return none
    let ctx ← pinTermOpaques cfg cfg.envExpr ctx x
    let hNoEq ← proveNoShadow cfg { name := "EQUAL" }
    let hx ← proveConv cfg cfg.envExpr ctx x
    return some (← mkAppM lem #[cfg.worldExpr, cfg.envExpr, reflectSExpr x, hNoEq, hx])
  -- the EQUALITYP form (rewrite.lisp:18093): reached (EQUAL (EQUAL a b) r),
  -- recorded (IF (EQUAL a b) (EQUAL r 'T) (IF r 'NIL 'T))
  let .cons (.atom (.symbol xeS)) (.cons a (.cons b .nil)) := x | return none
  unless xeS.name == "EQUAL" do return none
  let .cons (.atom (.symbol thS)) (.cons r (.cons rtq .nil)) := thn | return none
  unless thS.name == "EQUAL" && rtq == quoteT do return none
  unless els == .cons (.atom (.symbol { name := "IF" }))
      (.cons r (.cons quoteNil (.cons quoteT .nil))) do return none
  unless reached == eqT x r do return none
  let ctx ← pinTermOpaques cfg cfg.envExpr ctx reached
  let hNoEq ← proveNoShadow cfg { name := "EQUAL" }
  let ha ← proveConv cfg cfg.envExpr ctx a
  let hb ← proveConv cfg cfg.envExpr ctx b
  let hr ← proveConv cfg cfg.envExpr ctx r
  return some (← mkAppM ``re_equal_equalityp_norm
    #[cfg.worldExpr, cfg.envExpr, reflectSExpr a, reflectSExpr b, reflectSExpr r,
      hNoEq, ha, hb, hr])

/-- The DEFINITION-node recipe, UNIFORM: unfold `(fn args) ⇒ substTerm formals args
    body`, then chain the node's children (recognizer / if-simplification / deeper
    rewrites) over the substituted body via the ordinary path-directed congruence
    machinery (`replayRewrites` at depth+1 — their `:PATH`s carry the boundary
    frame), checking the chain reaches the node's recorded rhs.

    Two unfold routes by where the definition lives: a WORLD defun unfolds via
    the world lemmas (body convergence from two ordered evidence sources: the
    application's PINNED value — totality, required for recursive fns — else
    the ∀-env convergence analyzer); a builtin ABSENT from the world takes the
    D4 definition-fact route (`replayBuiltinDefUnfold`). -/
partial def replayDefinition (rec : NodeRec) (cfg : ReplayConfig) (ctx : ReplayCtx) (n : ProofNode)
    (depth : Nat) : MetaM Expr := do
  let (lhs, rhs) := nodeLhsRhs n
  let .node _ _ _ children _ := n
  let .cons (.atom (.symbol fn)) argSpine := lhs
    | throwError "definition: lhs is not an application: {repr lhs}"
  let args := (argSpine.toList?).getD []
  let (formals, body, unfold) ←
    if (cfg.worldVal.defs.get? fn).isNone then
      -- D4 route: builtin definition fact against the emitted snapshot
      replayBuiltinDefUnfold cfg ctx fn args
    else do
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
          | [f1, f2, f3], [a1, a2, a3], [v1, v2, v3], [p1, p2, p3] =>
            let hbody ← mkAppM ``re_body_conv3
              #[cfg.worldExpr, cfg.envExpr, reflectSymbol fn, reflectSymbol f1,
                reflectSymbol f2, reflectSymbol f3, reflectSExpr di.body,
                reflectSExpr a1, reflectSExpr a2, reflectSExpr a3,
                v1, v2, v3, rv, hns, di.defFact, p1, p2, p3, papp]
            mkAppM ``evalOpt_unfold3_conv
              #[cfg.worldExpr, cfg.envExpr, reflectSymbol fn, reflectSymbol f1,
                reflectSymbol f2, reflectSymbol f3, reflectSExpr di.body,
                reflectSExpr a1, reflectSExpr a2, reflectSExpr a3, v1, v2, v3, rv,
                hns, di.defFact, di.closedFact, di.noLetFact, p1, p2, p3, hbody]
          | _, _, _, _ => throwError "definition: only 1/2/3-arg unfolds supported (frontier)"
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
          | [f1, f2, f3], [a1, a2, a3] =>
            let h1 ← proveConv cfg cfg.envExpr ctx a1
            let h2 ← proveConv cfg cfg.envExpr ctx a2
            let h3 ← proveConv cfg cfg.envExpr ctx a3
            mkAppM ``re_unfold3_conv
              #[cfg.worldExpr, cfg.envExpr, reflectSymbol fn, reflectSymbol f1,
                reflectSymbol f2, reflectSymbol f3, reflectSExpr di.body,
                reflectSExpr a1, reflectSExpr a2, reflectSExpr a3, hns,
                di.defFact, di.closedFact, di.noLetFact, h1, h2, h3, hbodyAll]
          | _, _ => throwError "definition: only 1/2/3-arg unfolds supported (frontier)"
      pure (di.formals, di.body, unfold)
  -- children chain over the substituted body (depth+1: their paths carry one more
  -- boundary frame), reaching the node's recorded rhs
  let substBody := ACL2.Replay.substTerm formals args body
  let (chainOpt, finalTerm) ← rec.rewrites cfg ctx substBody children (depth + 1) []
  let chainOpt ← do
    if finalTerm == rhs then pure chainOpt else
    -- rewrite-equal's unrecorded NIL normalization at the chain end
    match ← bridgeEqualNilNorm cfg ctx finalTerm rhs with
    | some br => match chainOpt with
      | none => pure (some br)
      | some ch => pure (some (← mkAppM ``fuel_chain_eq #[ch, br]))
    | none =>
      throwError "definition: children chain reached {repr finalTerm}, node rhs is {repr rhs}"
  match chainOpt with
  | none => return unfold
  | some ch => mkAppM ``fuel_chain_eq #[unfold, ch]

/-- Replay one rewrite node to its eval-equality `∃N∀f≥N, eval lhs = eval rhs`, by
    applying that rune's recipe. (equal-self is the literal closer, handled in
    `replayLiteral`, not here.) `depth` = the number of unfold/rule boundaries
    above this node (relativizes child `:PATH`s). Unhandled runes hard-fail. -/
partial def replayNodeWith (rec : NodeRec) (cfg : ReplayConfig) (ctx : ReplayCtx) (n : ProofNode)
    (depth : Nat := 0) : MetaM Expr := do
  let rune := runeOf n
  let (rty, rname) := (rune.ty, rune.name)
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
      | .typeSetDerived =>
        -- J6: the equivalence was believed by ACL2's TYPE-SET under the
        -- branch facts (verdict-class, no recorded derivation). The
        -- value-level discharge recipe (e.g. both sides nil under a
        -- ¬consp fact) is the named follow-up.
        throwFrontier m!"solidify: type-set-derived equivalence \
            {repr (prov.equivTerm.getD .nil)} — value-level discharge from \
            branch facts not yet implemented (J6 replay frontier)"
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
        unless eqS.name == "EQUAL" do
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
        unless eqS.name == "EQUAL" do
          throwError "solidify: segment equiv head {eqS.name} ≠ equal (frontier)"
        let mkNotEq (x y : SExpr) : SExpr :=
          .cons (.atom (.symbol { name := "NOT" }))
            (.cons (.cons (.atom (.symbol { name := "EQUAL" }))
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
        if ns.name == "NOT" && es.name == "EQUAL" then pure (litTerm0, hNil0)
        else pure (litTerm0, hNil0)
      | _ =>
        match prov.equivTerm with
        | some (.cons (.atom (.symbol eqS')) (.cons a' (.cons b' .nil))) => do
          unless eqS'.name == "EQUAL" do
            throwError "solidify: source literal is not (not (equal A B)) and \
                        equiv {repr prov.equivTerm} is not an equal equation: \
                        {repr litTerm0}"
          let mk (x y : SExpr) : SExpr :=
            .cons (.atom (.symbol { name := "NOT" }))
              (.cons (.cons (.atom (.symbol { name := "EQUAL" }))
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
    unless notS.name == "NOT" && eqS.name == "EQUAL" do
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
  | "rewrite", "CDR-CONS" =>
    -- `(cdr (cons a b)) ⇒ b`.
    match lhs with
    | .cons (.atom (.symbol cdrS))
        (.cons (.cons (.atom (.symbol consS)) (.cons a (.cons b .nil))) .nil) =>
      unless cdrS.name == "CDR" && consS.name == "CONS" do
        throwError "cdr-cons: lhs head not (cdr (cons …)): {repr lhs}"
      let ha ← proveConv cfg cfg.envExpr ctx a
      let hb ← proveConv cfg cfg.envExpr ctx b
      let hNoCdr ← proveNoShadow cfg { name := "CDR" }
      let hNoCons ← proveNoShadow cfg { name := "CONS" }
      let ruleEq ← mkAppM ``re_cdr_cons_conv
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr a, reflectSExpr b, hNoCdr, hNoCons, ha, hb]
      -- children may rewrite the rule's result further (see car-cons)
      let (chainOpt, finalTerm) ← rec.rewrites cfg ctx b children (depth + 1) []
      unless finalTerm == rhs do
        throwError "cdr-cons: children chain reached {repr finalTerm}, \
                    node rhs is {repr rhs}"
      match chainOpt with
      | none => return ruleEq
      | some ch => mkAppM ``fuel_chain_eq #[ruleEq, ch]
    | _ => throwError "cdr-cons: lhs not (cdr (cons a b)): {repr lhs}"
  | "rewrite", "CAR-CONS" =>
    -- `(car (cons a b)) ⇒ a`.
    match lhs with
    | .cons (.atom (.symbol carS))
        (.cons (.cons (.atom (.symbol consS)) (.cons a (.cons b .nil))) .nil) =>
      unless carS.name == "CAR" && consS.name == "CONS" do
        throwError "car-cons: lhs head not (car (cons …)): {repr lhs}"
      let ha ← proveConv cfg cfg.envExpr ctx a
      let hb ← proveConv cfg cfg.envExpr ctx b
      let hNoCar ← proveNoShadow cfg { name := "CAR" }
      let hNoCons ← proveNoShadow cfg { name := "CONS" }
      let ruleEq ← mkAppM ``re_car_cons_conv
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr a, reflectSExpr b, hNoCar, hNoCons, ha, hb]
      -- the rule's result may be FURTHER rewritten by children (e.g. a
      -- solidify inside the rule's RHS — their paths carry the (RHS . _)
      -- boundary, consumed at depth+1); the node's rhs is the NET result.
      let (chainOpt, finalTerm) ← rec.rewrites cfg ctx a children (depth + 1) []
      unless finalTerm == rhs do
        throwError "car-cons: children chain reached {repr finalTerm}, \
                    node rhs is {repr rhs}"
      match chainOpt with
      | none => return ruleEq
      | some ch => mkAppM ``fuel_chain_eq #[ruleEq, ch]
    | _ => throwError "car-cons: lhs not (car (cons a b)): {repr lhs}"
  | "rewrite", "UNICITY-OF-0" =>
    -- `(binary-+ '0 z) ⇒ z` via the REAL intermediate `(fix z)` (the def:fix child
    -- subtree is REPLAYED, not collapsed): (A) `(+ '0 z) ⇒ (fix z)` by both
    -- converging to z's pinned int value; (B) the child `(fix z) ⇒ z`.
    match lhs with
    | .cons (.atom (.symbol plusS)) (.cons q0 (.cons z .nil)) =>
      unless plusS.name == "BINARY-+" && rhs == z do
        throwError "unicity-of-0: unexpected shape {repr lhs} ⇒ {repr rhs}"
      let some (vz, pz) := ctx.val? z
        | throwError "unicity-of-0: {repr z} has no pinned value (need the TP int fact)"
      let k ← intValExpr? vz
      let some fixChild := children.find? (fun c => (runeOf c).ty == "definition")
        | throwError "unicity-of-0: missing the definition:fix child"
      let (_fixLhs, fixRhs) := nodeLhsRhs fixChild
      unless fixRhs == z do
        throwError "unicity-of-0: fix child rhs {repr fixRhs} ≠ {repr z}"
      let fixEq ← replayNodeWith rec cfg ctx fixChild (depth + 1)
      let fixConv ← mkAppM ``fuel_conv_of_eq #[fixEq, pz]
      let hq0 ← ctxValProof cfg ctx q0
      let vq0 ← ctxValExpr cfg ctx q0
      let hNoPlus ← proveNoShadow cfg { name := "BINARY-+" }
      let hNsPlus ← proveNotSpecial { name := "BINARY-+" }
      let hr ← mkAppM ``callBuiltin_plus #[vq0, vz]
      let plusConvRaw ← mkAppM ``conv_builtin2
        #[cfg.worldExpr, cfg.envExpr, reflectSymbol { name := "BINARY-+" },
          reflectSExpr q0, reflectSExpr z, vq0, vz,
          mkApp2 (mkConst ``Logic.plus) vq0 vz, hNsPlus, hNoPlus, hq0, pz, hr]
      let hzero ← mkAppM ``logic_plus_zero_int #[k]
      let plusConv ← mkAppM ``re_val_cast
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr lhs,
          mkApp2 (mkConst ``Logic.plus) vq0 vz, vz, plusConvRaw, hzero]
      let stepA ← mkAppM ``fuel_eq_of_conv #[plusConv, fixConv, ← mkEqRefl vz]
      mkAppM ``fuel_chain_eq #[stepA, fixEq]
    | _ => throwError "unicity-of-0: lhs not (binary-+ '0 z): {repr lhs}"
  | "rewrite", "COMMUTATIVITY-OF-+" =>
    -- `(+ a b) ⇒ (+ b a)`, then the node's children chain on the rule's rhs
    -- (their paths carry an `(RHS . …)` boundary frame — depth+1) to the recorded rhs.
    match lhs with
    | .cons (.atom (.symbol plusS)) (.cons a (.cons b .nil)) =>
      unless plusS.name == "BINARY-+" do
        throwError "commutativity-of-+: head {plusS.name}"
      let ha ← ctxValProof cfg ctx a
      let hb ← ctxValProof cfg ctx b
      let va ← ctxValExpr cfg ctx a
      let vb ← ctxValExpr cfg ctx b
      let hNoPlus ← proveNoShadow cfg { name := "BINARY-+" }
      let ruleEq ← mkAppM ``re_plus_comm
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr a, reflectSExpr b, va, vb, hNoPlus, ha, hb]
      let swapped : SExpr :=
        .cons (.atom (.symbol plusS)) (.cons b (.cons a .nil))
      let (chainOpt, finalTerm) ← rec.rewrites cfg ctx swapped children (depth + 1) []
      unless finalTerm == rhs do
        throwError "commutativity-of-+: children chain reached {repr finalTerm}, \
                    node rhs is {repr rhs}"
      match chainOpt with
      | none => return ruleEq
      | some ch => mkAppM ``fuel_chain_eq #[ruleEq, ch]
    | _ => throwError "commutativity-of-+: lhs not (binary-+ a b): {repr lhs}"
  | "rewrite", "COMMUTATIVITY-2-OF-+" =>
    -- `(+ a (+ b c)) ⇒ (+ b (+ a c))`, then the children chain on the rule's rhs
    -- at depth+1 to the recorded rhs.
    match lhs with
    | .cons (.atom (.symbol plusS))
        (.cons a (.cons (.cons (.atom (.symbol plusS2)) (.cons b (.cons c .nil))) .nil)) =>
      unless plusS.name == "BINARY-+" && plusS2.name == "BINARY-+" do
        throwError "commutativity-2-of-+: heads"
      let ha ← ctxValProof cfg ctx a
      let hb ← ctxValProof cfg ctx b
      let hc ← ctxValProof cfg ctx c
      let va ← ctxValExpr cfg ctx a
      let vb ← ctxValExpr cfg ctx b
      let vc ← ctxValExpr cfg ctx c
      let hNoPlus ← proveNoShadow cfg { name := "BINARY-+" }
      let ruleEq ← mkAppM ``re_plus_comm2
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr a, reflectSExpr b, reflectSExpr c,
          va, vb, vc, hNoPlus, ha, hb, hc]
      let swapped : SExpr :=
        .cons (.atom (.symbol plusS))
          (.cons b (.cons (.cons (.atom (.symbol plusS2)) (.cons a (.cons c .nil))) .nil))
      let (chainOpt, finalTerm) ← rec.rewrites cfg ctx swapped children (depth + 1) []
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
    if dname == "IMPLIES" && (cfg.worldVal.defs.get? { name := "IMPLIES" }).isNone then
      replayImpliesDef cfg ctx n
    else replayDefinition rec cfg ctx n depth
  | "fake-rune-for-anonymous-enabled-rule", _ =>
    -- recognizer node: term-eq form (eval lhs = eval rhs, rhs the quoted verdict).
    let verdictV := match rhs with
      | .cons (.atom (.symbol q)) (.cons v .nil) => if q.name == "QUOTE" then v else rhs
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
      unless ifS.name == "IF" do
        throwError "if-simplification: head {ifS.name}"
      if prov.origin == "if1/boolean" then
        unless thn == quoteT && els == quoteNil && rhs == c do
          throwError "if1/boolean: node is not (if tst 't 'nil) ⇒ tst: \
                      {repr lhs} ⇒ {repr rhs}"
        let vC ← ctxValExpr cfg ctx c
        let hBool ←
          if vC.isAppOfArity ``Logic.equal 2 then
            mkAppM ``cond_toBool_equal #[vC.appFn!.appArg!, vC.appArg!]
          else if vC.isAppOfArity ``ACL2.lexorder 2 then
            -- LEXORDER test: two-valuedness DIRECTLY from `lexorder_boolean`
            -- (a builtin boolean predicate — no TP hypothesis needed).
            mkAppM ``cond_toBool_lexorder #[vC.appFn!.appArg!, vC.appArg!]
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
      unless q.name == "QUOTE" do
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
      unless ifS.name == "IF" do
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
      let hNoEqual ← proveNoShadow cfg { name := "EQUAL" }
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
    unless q.name == "QUOTE" do
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
      let notLhs : SExpr := .cons (.atom (.symbol { name := "NOT" }))
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
    unless q.name == "QUOTE" do
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
    -- `abbreviation-expansion` is the SAME rule application recorded at
    -- preprocess's expand-abbreviations: ACL2's `abbreviation` subclass is
    -- hypothesis-free by construction (find-abbreviation-lemma), enforced
    -- below at the spec — the recipe is otherwise identical
    unless prov.origin == "with-lemma" ||
           prov.origin == "abbreviation-expansion" do
      throwError "rewrite rune ({rname}): origin {prov.origin} is not \
                  with-lemma (frontier)"
    let σvars ← prov.subst.mapM fun (v, _) => do
      let .atom (.symbol s) := v
        | throwError "rule {rname}: :SUBST binds a non-variable {repr v}"
      pure s
    let σterms := prov.subst.map (·.2)
    -- the matching stored rule: recompute-and-check joint —
    -- substTerm(:SUBST, rule lhs) must BE the node's lhs
    -- identity includes the multi-rule index (J7): a step citing
    -- (:REWRITE FOO . 2) matches only the idx-2 stored rule.
    let candidates := ctx.ruleHyps.filter fun (r, _) =>
      r.name == rname && r.idx == rune.idx
    if candidates.isEmpty then
      throwError "rule {rname}: no stored-rule hypothesis in scope (no \
                  (:RULES …) entry — emission gap or missing telescope)"
    let matched := candidates.filter fun (r, _) =>
      ACL2.Replay.substTerm σvars σterms r.lhs == lhs
    let [(spec, hypV)] := matched
      | throwError "rule {rname}: {matched.length} stored rules match \
                    substTerm(:SUBST, lhs) == {repr lhs} (need exactly 1)"
    if prov.origin == "abbreviation-expansion" && !spec.hyps.isEmpty then
      throwError "rule {rname}: abbreviation-expansion step cites a rule \
                  with {spec.hyps.length} hypotheses — abbreviations are \
                  hyp-free (record/world mismatch)"
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
      fun c => (runeOf c).ty == "hyp-relief"
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
    -- SYNP hyps are relieved by neither a marker nor a chain (they discharge
    -- definitionally below) — exclude them from the partition count
    -- (audit 2026-07-19 R1)
    let synpHyps := spec.hyps.countP fun h =>
      match h with
      | .cons (.atom (.symbol s)) _ => s.name == "SYNP"
      | _ => false
    if !chainKids.isEmpty &&
        spec.hyps.length != reliefMarkers.length + synpHyps + 1 then
      throwError "rule {rname}: {spec.hyps.length} hyps with one recorded \
                  relief chain, {reliefMarkers.length} markers, and \
                  {synpHyps} synp hyps — per-hyp partition (frontier)"
    let tNeNil ← proveByDecide
      (← mkAppM ``Ne #[mkConst ``SExpr.t, mkConst ``SExpr.nil]) "t ≠ nil"
    let mut prems : Array Expr := #[]
    for h in spec.hyps do
      let hσ := ACL2.Replay.substTerm σvars σterms h
      let hasMarker := reliefMarkers.any fun c => (nodeLhsRhs c).1 == hσ
      -- a SYNP hyp (syntaxp/bind-free): ACL2 relieves it by the meta-level
      -- syntactic check and records `(:DEFINITION SYNP)` in the ttree — in
      -- the LOGIC, `synp` ignores its (always-quoted) args and returns `t`,
      -- so the recorded relief IS the definitional ground evaluation
      let isSynp := match hσ with
        | .cons (.atom (.symbol s)) _ => s.name == "SYNP"
        | _ => false
      -- EVERY hyp must have an emitted relief RECORD — a silent-relief marker
      -- or a rewrite chain. No record at all is an emission gap (audit
      -- 2026-07-06 finding A): the clause context may well justify the hyp,
      -- but nothing in the tree says ACL2 relieved it that way — hard-fail
      -- and emit more, never paper over.
      if !hasMarker && chainKids.isEmpty && !isSynp then
        throwError "rule {rname}: hyp {repr hσ} has NO emitted relief record \
                    (no relieve-hyp marker, no relief chain) — emission gap \
                    (frontier)"
      let evTrueEnv ←
        if isSynp then do
          -- consistency check on the CUMULATIVE ttree rune set (it can only
          -- REJECT — ACL2 pushes (:DEFINITION SYNP) on every successful synp
          -- relief, but the set may also carry it from earlier steps; the
          -- honest relief record is the definitional evaluation below)
          unless prov.runes.any (fun r => r.ty == "definition" && r.name == "SYNP") do
            throwError "rule {rname}: SYNP hyp {repr hσ} but no \
                        (:DEFINITION SYNP) in the node's ttree runes \
                        (frontier)"
          -- re-run the same closed computation (`synp`'s world body is 'T):
          -- the exec-counterpart carve-out, exactly how ACL2 regards it
          let conv ← replayExecGround cfg hσ SExpr.t
          mkAppM ``evtrue_of_conv_ne_nil #[conv, tNeNil]
        else if hasMarker then do
          -- relieved SILENTLY from the clause context (the emitted marker
          -- names the instantiated hyp): the spine's (not hσ)-falsity fact
          -- (the type-alist source the type-alist recipe also consumes)
          let notH : SExpr := .cons (.atom (.symbol { name := "NOT" }))
            (.cons hσ .nil)
          let some hNotNil := ctx.litFactByTerm? notH
            | throwError "rule {rname}: marker-relieved hyp {repr hσ} has no \
                          (not …)-falsity fact in scope (frontier)"
          let vH ← ctxValExpr cfg ctx hσ
          let hne ← mkAppM ``logic_not_nil_ne #[vH, hNotNil]
          mkAppM ``evtrue_of_conv_ne_nil #[← ctxValProof cfg ctx hσ, hne]
        else if let some (notS, atm) := (match hσ with
            | .cons (.atom (.symbol s)) (.cons a .nil) =>
              if s.name == "NOT" then some (s, a) else none
            | _ => none) then do
          -- NEGATED hyp: ACL2's relieve-hyp strips the `not` and rewrites the
          -- ATM (obj flipped, NO gstack frame) — the recorded chain is
          -- atm-rooted and must land on 'nil. Lift the composed atm chain
          -- through the `not` wrapper by unary congruence and fold
          -- `(not 'nil) ⇒ 't` by re-running the same closed computation
          -- (the exec-counterpart carve-out), as `replayLiteralChain` does
          -- for :NOT-FLG literals.
          let (chainOpt, finalAtom) ← rec.rewrites cfg ctx atm chainKids (depth + 1) []
          unless finalAtom == quoteNil do
            throwError "rule {rname}: negated-hyp relief chain for {repr hσ} \
                        ends at {repr finalAtom}, not (quote nil)"
          let some ch := chainOpt
            | throwError "rule {rname}: negated-hyp relief chain for {repr hσ} \
                          composed to no steps"
          let ns ← proveNotSpecial notS
          let lifted := mkAppN (mkConst ``evalOpt_congr_unary)
            #[cfg.worldExpr, cfg.envExpr, reflectSymbol notS, reflectSExpr atm,
              reflectSExpr quoteNil, ns, ch]
          let notNil : SExpr := .cons (.atom (.symbol notS)) (.cons quoteNil .nil)
          let pNot ← replayExecGround cfg notNil SExpr.t
          let pQ ← mkAppM ``re_val_quote
            #[cfg.worldExpr, cfg.envExpr, reflectSExpr SExpr.t]
          let step ← mkAppM ``fuel_eq_of_conv
            #[pNot, pQ, ← mkEqRefl (reflectSExpr SExpr.t)]
          let chain ← mkAppM ``fuel_chain_eq #[lifted, step]
          let hconv ← mkAppM ``fuel_conv_of_eq #[chain, ← quoteTFact cfg]
          mkAppM ``evtrue_of_conv_ne_nil #[hconv, tNeNil]
        else do
          -- the recorded HYP chain rewrites hσ ⇒ … ⇒ 't (paths carry one
          -- more boundary frame, as definition-body children do)
          let (chainOpt, finalT) ← rec.rewrites cfg ctx hσ chainKids (depth + 1) []
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
    let (chainOpt, finalT) ← rec.rewrites cfg ctx rhsσ rhsKids (depth + 1) []
    unless finalT == rhs do
      throwError "rule {rname}: RHS chain reached {repr finalT}, node rhs is \
                  {repr rhs}"
    match chainOpt with
    | none => return pCore
    | some ch => mkAppM ``fuel_chain_eq #[pCore, ch]
  | _, _ =>
    throwError "replayNode: no rule for rune ({rty}, {rname}) — unimplemented frontier"

/-- The literal-clausify DECISION TREE, reconstructed from the flat
    `SplitDecision` trace (docs/notes/2026-07-03_branch-split-spine.md).
    `if-interp` pushes events else-branch-FIRST at splits; every event is
    self-located by its `path`, which the parser validates against its
    position (fail-closed). -/
inductive TraceTree where
  /-- `segment` (segment-* outcomes): the EMITTED clause segment for this
      leaf — the exact leaf→branch link the composer selects by. -/
  | leaf (value : SExpr) (outcome : String) (segment : Option (List SExpr))
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
  | .leaf v o p seg :: rest => do
    unless p == path do
      throw s!"parseTraceTree: leaf {repr v} at path {repr p}, expected \
               {repr path}"
    -- ∧-DECOMPOSITION (observed: ALL-REL-FILTER-1 literal 2): on a term
    -- `(if v X 'nil)`, if-interp emits the SEGMENT-OPEN leaf `v` (the
    -- `[v]`-segment child clause of `lit ≡ v ∧ X`) and CONTINUES
    -- enumerating X's segments at the SAME path — the leaf is not
    -- terminal. For the composer this is the decision split on `v`:
    -- under ¬v the literal is 'nil (and the `[v]` branch's segment —
    -- carried over from the open leaf's emitted :SEGMENT — is selected
    -- right there); under v the continuation's decisions apply.
    -- Synthesize exactly that split — every downstream check
    -- (collapse-vs-leaf-value, branch selection) stays fail-closed.
    let nextSamePath := match rest with
      | .test _ _ _ p' :: _ => p' == path
      | .leaf _ _ p' _ :: _ => p' == path
      | [] => false
    if o == "segment-open" && nextSamePath then
      let (k, rest') ← parseTraceTree path rest
      return (.split v (.leaf quoteNil "segment-false" seg) k, rest')
    return (.leaf v o seg, rest)

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
  if fs.name == "QUOTE" then return (none, t)
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
  -- EQUAL falsity via the spine facts (if-interp-assumed-value2's rule
  -- set): the commuted form, and ONE transport step through an in-scope
  -- segment EQUALITY (a `(not (equal a b))` literal's falsity, i.e. a = b —
  -- ACL2's type-alist canonicalizes the test through it; observed:
  -- (EQUAL D E) resolved from D = (CAR X) and (EQUAL (CAR X) E) = nil,
  -- ALL-REL-RM-2). All derivations are proof-carrying; anything beyond
  -- this bounded rule set stays unresolved and fail-closes downstream.
  if let .cons (.atom (.symbol eqS)) (.cons x (.cons y .nil)) := t then
    if eqS.name == "EQUAL" then
      let mkEqT (u v : SExpr) : SExpr :=
        .cons (.atom (.symbol eqS)) (.cons u (.cons v .nil))
      -- falsity of `(equal u v)` from a direct or commuted spine fact,
      -- stated over the given value exprs
      let eqFalsity (u v : SExpr) (vu vv : Expr) : MetaM (Option Expr) := do
        if let some h := ctx.litFactByTerm? (mkEqT u v) then
          return some h
        if let some h := ctx.litFactByTerm? (mkEqT v u) then
          return some (← mkAppM ``Eq.trans #[← mkAppM ``logic_equal_comm #[vu, vv], h])
        return none
      let vx ← ctxValExpr cfg ctx x
      let vy ← ctxValExpr cfg ctx y
      let mut hNil? ← eqFalsity x y vx vy
      if hNil?.isNone then
        -- one transport step through each in-scope segment equality a = b
        for (st, h) in ctx.segFacts do
          if hNil?.isSome then break
          let .cons (.atom (.symbol ns)) (.cons
              (.cons (.atom (.symbol es)) (.cons a (.cons b .nil))) .nil) := st
            | continue
          unless ns.name == "NOT" && es.name == "EQUAL" do continue
          let va ← ctxValExpr cfg ctx a
          let vb ← ctxValExpr cfg ctx b
          let hab ← mkAppM ``logic_not_equal_nil_eq #[va, vb, h]  -- va = vb
          -- try rewriting x (a→b / b→a), then y likewise
          let tryPos (isX : Bool) (frm tgt : SExpr) (hft : Expr) :
              MetaM (Option Expr) := do
            unless (if isX then x else y) == frm do return none
            let vto ← ctxValExpr cfg ctx tgt
            let some hf ← (if isX then eqFalsity tgt y vto vy
                           else eqFalsity x tgt vx vto) | return none
            -- v(equal x y) = v(equal [to/frm]) = nil
            let f ← withLocalDeclD `v (mkConst ``SExpr) fun vV =>
              mkLambdaFVars #[vV]
                (if isX then mkApp2 (mkConst ``Logic.equal) vV vy
                 else mkApp2 (mkConst ``Logic.equal) vx vV)
            let step ← mkAppM ``congrArg #[f, hft]
            return some (← mkAppM ``Eq.trans #[step, hf])
          let hba ← mkAppM ``Eq.symm #[hab]
          for (isX, frm, tgt, hft) in
              [(true, a, b, hab), (true, b, a, hba),
               (false, a, b, hab), (false, b, a, hba)] do
            if hNil?.isNone then
              hNil? ← tryPos isX frm tgt hft
      if let some hNil := hNil? then
        let pl ← ctxValProof cfg ctx t
        let pr ← mkAppM ``re_val_quote #[w, e, reflectSExpr SExpr.nil]
        let step ← mkAppM ``fuel_eq_of_conv #[pl, pr, hNil]
        return (some step, quoteNil)
  if fs.name == "IF" then
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
      -- the test collapsed to a QUOTED CONSTANT (an in-scope litFact or fold
      -- resolved it): take the branch, exactly as if-interp does
      if let .cons (.atom (.symbol q)) (.cons cv .nil) := c' then
        if q.name == "QUOTE" then
          let (step, sel) ← mkConstTestCollapse cfg ctx c' cv a b
          let acc' ← match acc with
            | none => pure step
            | some p => mkAppM ``fuel_chain_eq #[p, step]
          let (chSel, final) ← collapseEval cfg ctx facts sel
          match chSel with
          | none => return (some acc', final)
          | some m => return (some (← mkAppM ``fuel_chain_eq #[acc', m]), final)
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
    -- cons-term's GROUND-PRIMITIVE fold: an argument-ground application of
    -- an UNDEFINED (builtin) head folds to its value — e.g. (CAR 'NIL) ⇒
    -- 'NIL (CAR-RM). Re-run the same closed computation (the
    -- exec-counterpart carve-out); user-fn heads stay in place (cons-term
    -- folds primitives only).
    if curArgs.all (fun a => match a with
        | .cons (.atom (.symbol q)) (.cons _ .nil) => q.name == "QUOTE"
        | _ => false) &&
       cfg.worldVal.defs.get? fs == none && fs.name != "NOT" then
      let mut F := 8
      let mut v? : Option SExpr := none
      while v?.isNone && F ≤ 65536 do
        v? := ACL2.evalOpt F cfg.worldVal {} cur
        if v?.isNone then F := F * 2
      match v? with
      | none => pure none  -- leave in place; downstream checks fail-closed
      | some v =>
        let foldedT : SExpr :=
          .cons (.atom (.symbol { name := "QUOTE" })) (.cons v .nil)
        let p ← replayExecGround cfg cur v
        let pQ ← mkAppM ``re_val_quote #[w, e, reflectSExpr v]
        pure (some (← mkAppM ``fuel_eq_of_conv
          #[p, pQ, ← mkEqRefl (reflectSExpr v)], foldedT))
    else if fs.name == "NOT" then
      match curArgs.toList with
      | [.cons (.atom (.symbol q)) (.cons cc .nil)] =>
        if q.name == "QUOTE" then
          let foldedV : SExpr := if cc == SExpr.nil then SExpr.t else SExpr.nil
          let foldedT : SExpr :=
            .cons (.atom (.symbol { name := "QUOTE" })) (.cons foldedV .nil)
          let pNot ← replayExecGround cfg cur foldedV
          let pQ ← mkAppM ``re_val_quote #[w, e, reflectSExpr foldedV]
          pure (some (← mkAppM ``fuel_eq_of_conv
            #[pNot, pQ, ← mkEqRefl (reflectSExpr foldedV)], foldedT))
        else pure none
      | _ => pure none
    else if fs.name == "EQUAL" then
      let isEqualApp : SExpr → Bool := fun t =>
        match t with
        | .cons (.atom (.symbol es)) (.cons _ (.cons _ .nil)) => es.name == "EQUAL"
        | _ => false
      match curArgs.toList with
      | [x, y] =>
        if x == y then
          let hX ← proveConv cfg e ctx x
          let hNoEqual ← proveNoShadow cfg { name := "EQUAL" }
          let pEq ← mkAppM ``re_equal_self #[w, e, reflectSExpr x, hX, hNoEqual]
          let pQ ← mkAppM ``re_val_quote #[w, e, reflectSExpr SExpr.t]
          pure (some (← mkAppM ``fuel_eq_of_conv
            #[pEq, pQ, ← mkEqRefl (mkConst ``SExpr.t)], quoteT))
        else if y == quoteT && isEqualApp x then
          -- (equal (equal a b) 't) = (equal a b) — rewrite.lisp:3791
          let pl ← ctxValProof cfg ctx cur
          let pr ← ctxValProof cfg ctx x
          let .cons _ (.cons a (.cons b .nil)) := x
            | throwError "collapseEval: internal — isEqualApp shape"
          let va ← ctxValExpr cfg ctx a
          let vb ← ctxValExpr cfg ctx b
          pure (some (← mkAppM ``fuel_eq_of_conv
            #[pl, pr, ← mkAppM ``logic_equal_equal_t_r #[va, vb]], x))
        else if x == quoteT && isEqualApp y then
          -- (equal 't (equal a b)) = (equal a b) — rewrite.lisp:3785
          let pl ← ctxValProof cfg ctx cur
          let pr ← ctxValProof cfg ctx y
          let .cons _ (.cons a (.cons b .nil)) := y
            | throwError "collapseEval: internal — isEqualApp shape"
          let va ← ctxValExpr cfg ctx a
          let vb ← ctxValExpr cfg ctx b
          pure (some (← mkAppM ``fuel_eq_of_conv
            #[pl, pr, ← mkAppM ``logic_equal_equal_t_l #[va, vb]], y))
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


/-- Replay a chain of rewrite nodes, lifting each through the chain's start term by
    path-directed congruence (paths relativized to `depth`) and chaining. Returns
    the composed `∃N∀f≥N, eval start = eval finalTerm` (or `none` if the chain is
    empty) and the final term. -/
partial def replayRewritesWith (rec : NodeRec) (cfg : ReplayConfig) (ctx : ReplayCtx) (start : SExpr) :
    List ProofNode → Nat → List Nat →
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
    if lhs == rhs && (runeOf n).ty == "if-simplification" then
      if let .node _ _ _ [] _ := n then
        let rel ← relativizeAndStrip (nodePath n) depth strip
        let (_, S) ← ofExcept (navigateFrames start rel)
        if S == rhs then
          return ← replayRewritesWith rec cfg ctx start rest depth strip
        -- SYMBOLIC-test if resolved by an in-scope clause-context fact,
        -- record folded all the way past the constant (observed: 'T ⇒ 'T
        -- with running (IF (EQUAL (CAR X) E) 'NIL 'T) under that segment
        -- literal's falsity — ALL-REL-FILTER-1, Subgoal *1/2'). collapseEval
        -- re-derives the resolution from the SAME facts if-interp consulted;
        -- the rhs equality below fail-closes on any divergence.
        if let .cons (.atom (.symbol ifS')) (.cons c' _) := S then
          let symbolicTest := ifS'.name == "IF" &&
            (match c' with
             | .cons (.atom (.symbol q')) (.cons _ .nil) => q'.name != "QUOTE"
             | _ => true)
          if symbolicTest then
            let (chOpt, S') ← collapseEval cfg ctx [] S
            if let some ch := chOpt then
              if S' == rhs then
                let (lifted, newTerm) ←
                  emitCongruence cfg.worldExpr cfg.envExpr start (nodePath n) S S'
                    ch depth strip
                let (restProof, finalTerm) ←
                  replayRewritesWith rec cfg ctx newTerm rest depth strip
                match restProof with
                | none => return (some lifted, finalTerm)
                | some rp =>
                  return (some (← mkAppM ``fuel_chain_eq #[lifted, rp]), finalTerm)
        let .cons (.atom (.symbol ifS))
            (.cons (.cons (.atom (.symbol q)) (.cons cv .nil))
              (.cons thn (.cons els .nil))) := S
          | throwError "replayRewrites: identity if-simplification's running \
                        subterm {repr S} is neither rhs {repr rhs} nor a \
                        constant-test if (frontier; segFacts: \
                        {repr (ctx.segFacts.map (·.1))}, litFacts: \
                        {repr (ctx.litFacts.map (·.2.1))})"
        unless ifS.name == "IF" && q.name == "QUOTE" do
          throwError "replayRewrites: identity if-simplification's running \
                      subterm {repr S} is not a constant-test if (frontier)"
        let branch := if cv == SExpr.nil then els else thn
        unless branch == rhs do
          throwError "replayRewrites: folded constant-test collapse of \
                      {repr S} selects {repr branch}, node rhs is {repr rhs}"
        let c : SExpr := .cons (.atom (.symbol q)) (.cons cv .nil)
        let (nodeEq, _) ← mkConstTestCollapse cfg ctx c cv thn els
        let (lifted, newTerm) ←
          emitCongruence cfg.worldExpr cfg.envExpr start (nodePath n) S branch
            nodeEq depth strip
        -- a ROOT collapse selects a branch that ACL2's rewrite-if keeps on the
        -- gstack while rewriting inside it — record the branch frame for
        -- stripping, exactly like the generic root if-simplification below
        -- (this arm bypasses that rule because the recorded lhs is folded)
        let strip' := if rel.isEmpty then strip ++ [if cv == SExpr.nil then 3 else 2]
                      else strip
        let (restProof, finalTerm) ← replayRewritesWith rec cfg ctx newTerm rest depth strip'
        match restProof with
        | none => return (some lifted, finalTerm)
        | some rp => return (some (← mkAppM ``fuel_chain_eq #[lifted, rp]), finalTerm)
    -- DISPLAY-FOLDED constant-test collapses (docs/notes/2026-06-14_exec-
    -- counterpart-and-folding-wall.md; extended 2026-07-20): a constant-test
    -- if-simplification's recorded lhs went through sublis-var, whose
    -- cons-term folds ground applications inside the branches — (car 'c)/
    -- (cdr 'c) in the DISCARDED branch (data-ratified 2026-07-06), and ground
    -- (EQUAL 'c1 'c2) tests in the SURVIVING branch (the REL-unfold chains,
    -- qsort corpus) — logging-only, per ACL2's own comment. The RUNNING term
    -- is the ground truth: require the SAME test and a SELF-CONSISTENT record
    -- (rhs == the recorded taken branch), and replay the collapse on the
    -- RUNNING term, continuing the chain from the RUNNING surviving branch.
    -- Surviving-branch folds are reconciled by the SUBSEQUENT recorded steps
    -- (the exec-counterpart resolutions ACL2 logs right after), each with its
    -- own fail-closed redex check — a real divergence still throws there or
    -- at the chain's end-result check.
    if (runeOf n).ty == "if-simplification" && lhs != rhs then
      if let .node _ _ _ [] _ := n then
        if let .cons (.atom (.symbol ifS))
            (.cons c@(.cons (.atom (.symbol q)) (.cons cv .nil))
              (.cons thn (.cons els .nil))) := lhs then
          if ifS.name == "IF" && q.name == "QUOTE" then
            let rel ← relativizeAndStrip (nodePath n) depth strip
            let (_, S) ← ofExcept (navigateFrames start rel)
            -- take the relaxation ONLY on the folded-collapse shape: same
            -- test, recorded rhs == recorded taken branch. Anything else
            -- falls THROUGH to the normal machinery (if-finish/combined
            -- etc.), which handles or fails precisely.
            let compatible :=
              match S with
              | .cons (.atom (.symbol ifS')) (.cons c' (.cons _ (.cons _ .nil))) =>
                let taken := if cv == SExpr.nil then els else thn
                ifS'.name == "IF" && c' == c && rhs == taken
              | _ => false
            if S != lhs && compatible then
              let .cons _ (.cons _ (.cons thn' (.cons els' .nil))) := S
                | throwError "replayRewrites: internal — compatible running \
                              subterm lost its if shape"
              -- the collapse result is the RUNNING surviving branch (the
              -- recorded rhs may carry surviving-branch folds — see the arm
              -- doc above; nodeEq is exactly `eval S = eval taken'`)
              let (nodeEq, taken') ← mkConstTestCollapse cfg ctx c cv thn' els'
              let (lifted, newTerm) ←
                emitCongruence cfg.worldExpr cfg.envExpr start (nodePath n) S taken'
                  nodeEq depth strip
              -- ROOT collapse: record the surviving-branch frame for stripping
              -- (same gstack rule as the generic root if-simplification below —
              -- this arm bypasses it because the recorded lhs is dead-branch
              -- folded and so never equals the running chain term)
              let strip' := if rel.isEmpty then strip ++ [if cv == SExpr.nil then 3 else 2]
                            else strip
              let (restProof, finalTerm) ← replayRewritesWith rec cfg ctx newTerm rest depth strip'
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
    if (runeOf n).ty == "clause-context-resolution" then
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
    if let .node ⟨"if-simplification", _, _⟩ _ _ children prov := n then
      if prov.origin == "if-finish/combined" then
        let rel ← relativizeAndStrip (nodePath n) depth strip
        let (steps, S) ← ofExcept (navigateFrames start rel)
        let strip' := strip ++ steps.map (·.argIdx + 1)
        let .cons (.atom (.symbol ifS)) (.cons c (.cons thn (.cons els .nil))) := S
          | throwError "if-finish/combined: running subterm {repr S} is not a \
                        3-arg if"
        unless ifS.name == "IF" do
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
          let (chT, thn') ← replayRewritesWith rec cfg ctx' thn thenCh depth (strip' ++ [2])
          let prf ← match chT with
            | some p => pure p
            | none => mkIdEq thn
          pure (← mkLambdaFVars #[hNe] prf, thn')
        let (lamE, els') ← withLocalDeclD `hnil (← mkEq vC nilC) fun hNil => do
          let ctx' := { ctx with branchFacts := ctx.branchFacts ++ [(c, vC, false, hNil)] }
          let (chE, els') ← replayRewritesWith rec cfg ctx' els elseCh depth (strip' ++ [3])
          let prf ← match chE with
            | some p => pure p
            | none => mkIdEq els
          pure (← mkLambdaFVars #[hNil] prf, els')
        let target : SExpr := .cons (.atom (.symbol ifS))
          (.cons c (.cons thn' (.cons els' .nil)))
        -- whole-if finishing steps apply AFTER the branch congruence, on the
        -- rebuilt if
        let (postOpt, final) ← replayRewritesWith rec cfg ctx target postCh depth strip'
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
          return ← replayRewritesWith rec cfg ctx start rest depth strip
        let nodeProof ← chainEqs proofs
        let (lifted, newTerm) ←
          emitCongruence w e start (nodePath n) S final nodeProof depth strip
        let (restProof, finalTerm) ← replayRewritesWith rec cfg ctx newTerm rest depth strip
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
      if (runeOf n).ty == "if-simplification" then
        match lhs with
        | .cons (.atom (.symbol ifS))
            (.cons (.cons (.atom (.symbol q)) (.cons cv .nil)) _) =>
          if ifS.name == "IF" && q.name == "QUOTE" && cv == SExpr.nil then
            let rel ← relativizeAndStrip (nodePath n) depth strip
            let (steps, S) ← ofExcept (navigateFrames start rel)
            match S with
            | .cons (.atom (.symbol ifS'))
                (.cons T (.cons thn (.cons els .nil))) =>
              if ifS'.name == "IF" && S != lhs &&
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
                  .cons (.atom (.symbol { name := "EQUAL" }))
                    (.cons x (.cons y .nil))
                let directOrFlipped : SExpr → MetaM (Option Expr) := fun u => do
                  match nilFactFor u with
                  | some h => return some h
                  | none =>
                    match u with
                    | .cons (.atom (.symbol eqS)) (.cons x (.cons y .nil)) =>
                      if eqS.name == "EQUAL" then
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
                      if !(eqS.name == "EQUAL") then pure none else do
                      let mut found : Option Expr := none
                      for (st, hSeg) in ctx.segFacts do
                        if found.isSome then break
                        let .cons (.atom (.symbol ns))
                            (.cons pq@(.cons (.atom (.symbol eqS'))
                              (.cons p (.cons q .nil))) .nil) := st
                          | continue
                        unless ns.name == "NOT" && eqS'.name == "EQUAL" do
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
      let (restAll, finalT) ← replayRewritesWith rec cfg ctx start' (n :: rest) depth strip
      match restAll with
      | none => return (some testChain, finalT)
      | some rp =>
        return (some (← mkAppM ``fuel_chain_eq #[testChain, rp]), finalT)
    let nodeEq ← rec.node cfg ctx n depth
    let (lifted, newTerm) ←
      emitCongruence cfg.worldExpr cfg.envExpr start (nodePath n) lhs rhs nodeEq depth strip
    -- an if-simplification AT THE CHAIN ROOT selects a branch; ACL2's rewrite-if
    -- keeps the if on the gstack while rewriting inside that branch, so the
    -- remaining nodes' paths carry the branch frame — record it for stripping.
    let strip' ←
      -- BRANCH-SELECTING root if-simplifications only: an `if1/boolean`
      -- collapse replaces the if by its (boolean) test — no branch frame
      -- remains on the gstack, so nothing to strip.
      if (runeOf n).ty == "if-simplification" && lhs == start &&
         (nodeOrigin n) != "if1/boolean" then
        match lhs with
        | .cons _ (.cons _ (.cons thn (.cons els .nil))) =>
          if rhs == thn then pure (strip ++ [2])
          else if rhs == els then pure (strip ++ [3])
          else throwError "replayRewrites: root if-simplification rhs is neither branch"
        | _ => throwError "replayRewrites: root if-simplification lhs not a 3-arg if"
      else pure strip
    let (restProof, finalTerm) ← replayRewritesWith rec cfg ctx newTerm rest depth strip'
    match restProof with
    | none => return (some lifted, finalTerm)
    | some rp => return (some (← mkAppM ``fuel_chain_eq #[lifted, rp]), finalTerm)

/- The tied node-level knot — the ONLY remaining mutual at this layer.
   Public names/signatures identical to the pre-WP2 mutual members. -/
mutual

partial def replayNode (cfg : ReplayConfig) (ctx : ReplayCtx) (n : ProofNode)
    (depth : Nat := 0) : MetaM Expr :=
  replayNodeWith ⟨fun c x n' d => replayNode c x n' d,
                  fun c x s ns d st => replayRewrites c x s ns d st⟩ cfg ctx n depth

partial def replayRewrites (cfg : ReplayConfig) (ctx : ReplayCtx) (start : SExpr) :
    List ProofNode → (depth : Nat := 0) → (strip : List Nat := []) →
    MetaM (Option Expr × SExpr) :=
  fun ns depth strip =>
    replayRewritesWith ⟨fun c x n d => replayNode c x n d,
                       fun c x s' ns' d st => replayRewrites c x s' ns' d st⟩ cfg ctx start ns depth strip

end

/-- The tied record itself (recipes outside this file recurse through it). -/
def nodeRec : NodeRec :=
  ⟨fun cfg ctx n d => replayNode cfg ctx n d,
   fun cfg ctx s ns d st => replayRewrites cfg ctx s ns d st⟩


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
    unless notS.name == "NOT" do
      throwError "replayLiteralChain: notFlg literal head {notS.name} ≠ not"
    let (chainOpt, finalAtom) ← replayRewrites cfg ctx atm lp.nodes 0
    -- HIDDEN definitional `implies` unfold: rewrite-atm expands an implies
    -- atom with NO emitted node (only the literal's :RESULT shows it) —
    -- mirror it via the same ground-zero recipe as the preprocess step,
    -- record-directed (only when the plain chain does not already match).
    let (chainOpt, finalAtom) ←
      match finalAtom with
      | .cons (.atom (.symbol impS)) (.cons A (.cons B .nil)) =>
        if impS.name == "IMPLIES" &&
           SExpr.cons (.atom (.symbol notS)) (.cons finalAtom .nil) != lp.result then do
          let expanded : SExpr :=
            .cons (.atom (.symbol { name := "IF" }))
              (.cons A (.cons (.cons (.atom (.symbol { name := "IF" }))
                (.cons B (.cons quoteT (.cons quoteNil .nil))))
                (.cons quoteT .nil)))
          let step ← replayImpliesDef cfg ctx
            (.node ⟨"definition", "IMPLIES", none⟩ finalAtom expanded [] {})
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
      if q.name == "QUOTE" then
        let foldedV : SExpr := if c == SExpr.nil then SExpr.t else SExpr.nil
        let foldedT : SExpr :=
          .cons (.atom (.symbol { name := "QUOTE" })) (.cons foldedV .nil)
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
  | .node ⟨rty, _, _⟩ l rh children prov =>
    let notOf : SExpr → SExpr := fun t =>
      .cons (.atom (.symbol { name := "NOT" })) (.cons t .nil)
    (if rty == "hyp-relief" then [notOf l]
     else if rty == "type-alist" then
       if rh == quoteNil then [l]
       else if rh == quoteT then [notOf l]
       else []
     else if prov.origin == "recognizer/true" then
       -- a recognizer resolved TRUE from the clause context (a later
       -- literal is its negation — EQUAL-CONS Subgoal 4); hoisting is a
       -- no-op when the fact is derivable another way
       [notOf l]
     else if prov.origin == "recognizer/false" then [l]
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

end ACL2.Replay.Driver
