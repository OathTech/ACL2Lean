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
  /-- `WellScoped body = true`. -/
  wellScopedFact : Expr

/-- Ambient config: the `World` (as both an `Expr` for proof terms and a `World` value
    so the driver can read formals/bodies) and the `Env` `Expr`. The structural world
    facts (`defs.get? fn = …`, builtin-not-shadowed, freeVars⊆formals, WellScoped) are NOT
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
  /-- The development's ground-zero FORWARD-CHAINING rule snapshots
      (`(:GROUND-ZERO-FC-RULES …)`, emission arc 2026-07-21): trigger/hyps/
      concls verbatim. The FC-derived type-alist relief recipe pins its
      registered Lean lemma against the emitted shape (audit-F2 style) —
      an unlisted or drifted rule hard-fails. -/
  fcRules : List FcRuleSpec := []
  /-- RECORDED-TERMINATION mirrors (sorting arc 2026-07-28): per defun with
      a replayed admission waterfall, its replayed-statement constant, condition names,
      and root goal clause. Consumed by the totality prover (via the
      threaded `buildTotalEnv` params) AND the theorem-side induction's
      IH-decrease fallback (`replayInduction`, which resolves the conditions
      from the ambient `ReplayCtx`). -/
  termReplayed : List (String × Name × List String × List SExpr) := []
  /-- The development's emitted `:TYPE-PRESCRIPTION` corollaries for
      BUILTIN-NAMED ground-zero fns (world-defined fns get theirs as `tp:`
      hypotheses instead — `replayProofConditional`). Consumed by the builtin
      TP pin route in `pinTermOpaques`: a registered builtin (`builtinIntTps`)
      is int-pinned ONLY when its emitted corollary matches the registered
      shape exactly (type facts from ACL2, proof from the trusted core);
      an emitted-but-drifted corollary hard-fails. -/
  gzTps : List (String × SExpr) := []

/-- A CONGRUENCE rule consumed by the R-collapse (G2 rung 2), shape-parsed
    from a defcong-style defthm formula
    `(IMPLIES (R x y) (EQUAL (fn a₁…x…aₙ) (fn a₁…y…aₙ)))` — all args
    distinct variables, the two sides differing at exactly position `pos`
    (0-based), `y` fresh. The hypothesis states the WHOLE formula
    (`∀ env', EvTrue w env' formula` — `mkCongHypType`); nothing is derived
    from the shape except the (fn, pos, R) index and the σ construction at
    the use site, both recompute-and-checked there. -/
structure CongSpec where
  name : String
  formula : SExpr
  /-- The equivalence relation's fn symbol (the formula hyp's head). -/
  rel : Symbol
  /-- The congruent fn and the 0-based differing arg position. -/
  fn : Symbol
  pos : Nat
  /-- The lhs application's arg variables (x at `pos`) and the rhs-side
      variable y. -/
  argVars : List Symbol
  vy : Symbol
  /-- The formula pieces, for recompute-and-check at the use site. -/
  hyp : SExpr
  lhsApp : SExpr
  rhsApp : SExpr
  deriving BEq, Repr

/-- Shape-parse a defcong-style formula into a `CongSpec`. `none` when the
    formula is not congruence-shaped — the theorem is then simply not
    offered as a congruence (never mis-stated). -/
def congSpecOfFormula? (name : String) (formula : SExpr) : Option CongSpec := do
  let .cons (.atom (.symbol imp)) (.cons hyp (.cons concl .nil)) := formula
    | none
  guard (imp.name == "IMPLIES")
  let .cons (.atom (.symbol rel))
      (.cons (.atom (.symbol vx)) (.cons (.atom (.symbol vy)) .nil)) := hyp
    | none
  let .cons (.atom (.symbol eqS)) (.cons lhsApp (.cons rhsApp .nil)) := concl
    | none
  guard (eqS.name == "EQUAL")
  let .cons (.atom (.symbol fnL)) argsLs := lhsApp | none
  let .cons (.atom (.symbol fnR)) argsRs := rhsApp | none
  guard (fnL == fnR)
  let aL ← argsLs.toList?
  let aR ← argsRs.toList?
  guard (aL.length == aR.length)
  let argVars ← aL.mapM fun a => match a with
    | .atom (.symbol s) => some s
    | _ => none
  let argVarsR ← aR.mapM fun a => match a with
    | .atom (.symbol s) => some s
    | _ => none
  -- pairwise-distinct lhs vars; y fresh; sides differ at exactly one
  -- position, with x left / y right there
  guard (argVars.length == argVars.eraseDups.length)
  guard (!argVars.contains vy && vx != vy)
  let diffs := (argVars.zip argVarsR).zipIdx.filter fun ((l, r), _) => l != r
  let [((l, r), pos)] := diffs | none
  guard (l == vx && r == vy)
  return { name, formula, rel, fn := fnL, pos, argVars, vy,
           hyp, lhsApp, rhsApp }

/-- An EQUIVALENCE rule's REFLEXIVITY component (sorting-completion-2
    Class A, ORDERED-PERMS): shape-parsed from the RAW equivalence defthm
    formula `(AND (BOOLEANP (R x y)) (R x x) …)` — ACL2's defequiv shape.
    The offered hypothesis states only the reflexivity conjunct
    (`∀ env', EvTrue w env' (R x x)`) — the stored :EQUIVALENCE rule's
    refl content, consumed by the type-alist truthy arm on a syntactically
    reflexive application. -/
structure EquivReflSpec where
  name : String
  rel : Symbol
  vx : Symbol
  deriving BEq, Repr

/-- Shape-parse a RAW equivalence formula. `none` if not the defequiv
    shape (never mis-stated). -/
def equivReflSpecOfFormula? (name : String) (formula : SExpr) :
    Option EquivReflSpec := do
  let .cons (.atom (.symbol andS)) (.cons c1 (.cons c2 _)) := formula | none
  guard (andS.name == "AND")
  let .cons (.atom (.symbol bS))
      (.cons (.cons (.atom (.symbol rel1))
        (.cons (.atom (.symbol vx1)) (.cons (.atom (.symbol _)) .nil))) .nil)
      := c1 | none
  guard (bS.name == "BOOLEANP")
  let .cons (.atom (.symbol rel2))
      (.cons (.atom (.symbol vx2)) (.cons (.atom (.symbol vx3)) .nil)) := c2
    | none
  guard (rel1 == rel2 && vx1 == vx2 && vx2 == vx3)
  return { name, rel := rel1, vx := vx1 }

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
  /-- Harness-offered DP-FACT hypotheses (condition threading): clause term ↦
      the `hdpfact` fvar whose type is that discharge leaf's obligation
      (`dpFactStmtOfClause`). Consulted by `replayDischargeNode` when the
      obligation is unprovable — the row then reports ASSUMED:dp-fact. -/
  dpFactHyps : List (SExpr × Expr) := []
  /-- The bound CONDITIONAL hypotheses (the generic mirror's telescope):
      per defined fn, its totality hypothesis; and — when the development emitted
      a :TYPE-PRESCRIPTION — its lifted-corollary hypothesis (with the corollary
      term). The pinning step consumes these. -/
  totalHyps : List (String × Expr) := []
  tpHyps : List (String × SExpr × Expr) := []
  /-- ARGS-VALUED TP hypotheses (G1 arc 2026-07-29): (fn, corollary, hyp
      fvar) for emitted corollaries whose scrubbed residue mentions FORMALS
      bare (the BINARY-APPEND `(EQUAL (fn X Y) Y)` disjunct class) — the
      hypothesis binds the argument VALUES alongside the application's
      (`mkTpHypTypeAv`), so those occurrences lift to them. -/
  tpHypsAv : List (String × SExpr × Expr) := []
  /-- Theorem-dependency hypotheses (`rule:<thm>`, the third telescope
      species): per emitted STORED rewrite rule, the spec and the bound
      hypothesis stating its mirror (`mkRuleHypType`). Consumed by the
      with-lemma node recipe; discharged lazily from the dependency's own
      replayed statement (docs/plans/2026-07-05_theorem-dependency-hypotheses.md). -/
  ruleHyps : List (RuleSpec × Expr) := []
  /-- Congruence-rule hypotheses (`cong:<thm>`, G2 rung 2): per
      congruence-shaped in-scope defthm, the spec and the bound hypothesis
      stating its whole-formula mirror (`mkCongHypType`). Consumed by the
      R-collapse at a user-equivalence step's congruence frame; discharged
      lazily from the dependency's replayed statement like `rule:` hyps. -/
  congHyps : List (CongSpec × Expr) := []
  /-- Equivalence-REFLEXIVITY hypotheses (`equivrefl:<thm>`): per
      equivalence-shaped in-scope defthm (incl. INCLUDE-BOOK'd ones), the
      spec and the bound hypothesis `∀ env', EvTrue w env' (R x x)`.
      Include-book instances stay KEPT conditions (D6-honest). -/
  equivReflHyps : List (EquivReflSpec × Expr) := []
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

/-- `litFactByTerm?` with each candidate proof's TYPE checked against the
    expected proposition (G1 arc 2026-07-29): a term-keyed hit whose proof
    lives in ANOTHER env context (e.g. a pre-elim fact surviving an env
    change) is skipped instead of crashing the composition — and a
    well-typed fact later in the lists still wins. -/
def ReplayCtx.litFactByTermChecked? (ctx : ReplayCtx) (t : SExpr)
    (expectedTy : Expr) : Lean.Meta.MetaM (Option Expr) := do
  let cands := (ctx.litFacts.filterMap fun (_, lt, p) =>
      if lt == t then some p else none)
    ++ (ctx.segFacts.filterMap fun (st, p) => if st == t then some p else none)
  for p in cands do
    if ← Lean.Meta.isDefEq (← Lean.Meta.inferType p) expectedTy then
      return some p
  return none

/-- Consp EVIDENCE for a term's pinned value (G1 arc 2026-07-29): the value
    is a SYNTACTIC cons, or the clause context holds `(consp t)` — a
    `(not (consp t))`-falsity fact or a positive branch fact — exactly the
    type-alist entries ACL2's type-set consults. Returns
    `Logic.consp v = SExpr.t` (or `none`). Shared by the args-valued-TP
    recognizer derivation and the type-set-equality cell. -/
def conspEvidence? (ctx : ReplayCtx) (t : SExpr) (v : Expr) :
    Lean.Meta.MetaM (Option Expr) := do
  if v.isAppOfArity ``SExpr.cons 2 then
    return some (← mkAppM ``logic_consp_cons_t #[v.appFn!.appArg!, v.appArg!])
  let conspT : SExpr := .cons (.atom (.symbol { name := "CONSP" })) (.cons t .nil)
  let vC := mkApp (mkConst ``Logic.consp) v
  let notC : SExpr := .cons (.atom (.symbol { name := "NOT" })) (.cons conspT .nil)
  match ← ctx.litFactByTermChecked? notC
      (← mkEq (mkApp (mkConst ``Logic.not) vC) (mkConst ``SExpr.nil)) with
  | some hNotNil =>
    let hne ← mkAppM ``logic_not_nil_ne #[vC, hNotNil]
    return some (← mkAppM ``logic_consp_ne_nil_t #[v, hne])
  | none =>
    match ctx.branchFacts.find? (fun (bt, _, sign, _) => bt == conspT && sign) with
    | some (_, vB, _, hNe) =>
      if ← isDefEq vB vC then
        return some (← mkAppM ``logic_consp_ne_nil_t #[v, hNe])
      else return none
    | none =>
      -- a truthy (CDR t) clause fact: cdr non-nil forces a cons
      -- (ORDERED-PERMS Subgoal *1/2.2's (NOT (CDR B)) literal)
      let cdrT : SExpr := .cons (.atom (.symbol { name := "CDR" }))
        (.cons t .nil)
      let notCdr : SExpr := .cons (.atom (.symbol { name := "NOT" }))
        (.cons cdrT .nil)
      let vCdr := mkApp (mkConst ``Logic.cdr) v
      match ← ctx.litFactByTermChecked? notCdr
          (← mkEq (mkApp (mkConst ``Logic.not) vCdr) (mkConst ``SExpr.nil)) with
      | some hNotNil =>
        let hne ← mkAppM ``logic_not_nil_ne #[vCdr, hNotNil]
        return some (← mkAppM ``logic_consp_of_cdr_ne_nil #[hne])
      | none => return none

/-- View `(equal X X)` as `X`. -/
def asEqualSelf : SExpr → Option SExpr
  | .cons (.atom (.symbol s)) (.cons x (.cons x' .nil)) =>
    if s.name == "EQUAL" && x == x' then some x else none
  | _ => none

def runeOf : ProofNode → Rune | .node r _ _ _ _ => r
def nodeLhsRhs : ProofNode → SExpr × SExpr | .node _ lhs rhs _ _ => (lhs, rhs)
def nodePath : ProofNode → List PathFrame | .node _ _ _ _ p => p.path
def nodeOrigin : ProofNode → String | .node _ _ _ _ p => p.origin
/-- The node's enclosing-window kind ("" = none / literal level). -/
def innerKindOf : ProofNode → String | .node _ _ _ _ p => p.innerKind
/-- The node's enclosing-window input term (path-emission Phase 1). -/
def innerTermOf : ProofNode → Option SExpr | .node _ _ _ _ p => p.innerTerm
/-- The node's enclosing-window entry path (path-emission Phase 1). -/
def innerPathOf : ProofNode → List PathFrame | .node _ _ _ _ p => p.innerPath
/-- Strip the window tag — recipes that CONSUME a window (the if-finish
    branch partition; the inline-window group handler) clear it before
    handing the nodes to a sub-walk anchored at the window term. -/
def clearWindowTag : ProofNode → ProofNode
  | .node rune lhs rhs children prov =>
    .node rune lhs rhs children
      { prov with innerKind := "", innerTerm := none, innerPath := [] }
/-- RE-ROOT a whole-if finishing child at the if: keep the path's entry
    frame, drop the `k` window→if frames after it, so the post-walk's
    uniform drop-1 navigates from the if itself. VALIDATED by the caller
    (the child's window-local path must equal the if-finish node's own)
    — an `if-post` fork window would retire this (fold-back audit note). -/
def retargetAtIf (n : ProofNode) (k : Nat) : ProofNode :=
  match n with
  | .node rune lhs rhs children prov =>
    .node rune lhs rhs children
      { prov with path := prov.path.take 1 ++ prov.path.drop (1 + k) }

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
    - `wellScopedFact` : `WellScoped body = true`
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
    -- wellScopedFact : WellScoped body = true
    let wellScopedFact ← proveByDecide
      (← mkEq (← mkAppM ``ACL2.Replay.WellScoped #[bodyE]) (mkConst ``Bool.true)) s!"well-scoped {fn.name}"
    return { formal, body, defFact, closedFact, wellScopedFact }

/-- Prove `s.isNamed name = false` by kernel decision. -/
def proveIsNamedFalse (s : Symbol) (name : String) : MetaM Expr :=
  proveByDecide
    (mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
      (mkApp2 (mkConst ``Symbol.isNamed) (reflectSymbol s) (mkStrLit name)) (mkConst ``Bool.false))
    s!"{s.name}.isNamed {name} = false"

/-- Prove `s.isNamed name = true` by kernel decision. -/
def proveIsNamedTrue (s : Symbol) (name : String) : MetaM Expr :=
  proveByDecide
    (mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
      (mkApp2 (mkConst ``Symbol.isNamed) (reflectSymbol s) (mkStrLit name)) (mkConst ``Bool.true))
    s!"{s.name}.isNamed {name} = true"

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
   ("ATOM",     ``Logic.atom,     ``callBuiltin_atom),
   ("NUMERATOR", ``Logic.numerator, ``callBuiltin_numerator),
   ("DENOMINATOR", ``Logic.denominator, ``callBuiltin_denominator),
   ("UNARY--",  ``Logic.neg,      ``callBuiltin_unary_minus),
   ("REALPART", ``Logic.realpart, ``callBuiltin_realpart),
   ("IMAGPART", ``Logic.imagpart, ``callBuiltin_imagpart),
   ("COMPLEX-RATIONALP", ``Logic.complexRationalp,
    ``callBuiltin_complex_rationalp)]

/-- DP-lift primitives (binary). -/
def dpBinary : List (String × Name × Name) :=
  [("EQUAL",    ``Logic.equal,   ``callBuiltin_equal),
   ("<",        ``Logic.lt,      ``callBuiltin_lt),
   ("LEXORDER", ``ACL2.lexorder, ``callBuiltin_lexorder),
   ("BINARY-+", ``Logic.plus,    ``callBuiltin_plus),
   ("BINARY-*", ``Logic.times,   ``callBuiltin_times),
   ("COERCE",   ``Logic.coerce,  ``callBuiltin_coerce),
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
   ("NOT",        ``gz_def_not),
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
  | .cons (.cons (.atom (.symbol lam)) (.cons formalsE (.cons lamBody .nil))) argsExpr =>
    -- LAMBDA application (translated `let`, S2b): converges because its
    -- actuals and its beta-reduct do (`re_conv_lam*` — the same shape and
    -- certificates as the dpValProof arm; arity dispatch FIRST).
    if lam.name == "LAMBDA" then
      unless ACL2.Replay.WellScoped lamBody do
        throwError "proveConv: LAMBDA body is not closed/regular (WellScoped \
                    fails) — malformed input: {repr t}"
      match ACL2.lamFormals? formalsE, argsExpr.toList? with
      | some lformals, some actuals =>
        let certs (lfs : List Symbol) : MetaM (Expr × Expr × Expr) := do
          let lformalsE ← mkListLit (mkConst ``Symbol) (lfs.map reflectSymbol)
          let hlam ← proveIsNamedTrue lam "LAMBDA"
          let hform ← proveByDecide
            (← mkEq (← mkAppM ``ACL2.lamFormals? #[reflectSExpr formalsE])
                    (← mkAppM ``Option.some #[lformalsE])) "conv-lambda formals"
          let hnl ← proveByDecide
            (← mkEq (← mkAppM ``ACL2.Replay.WellScoped #[reflectSExpr lamBody])
                    (mkConst ``Bool.true)) "conv-lambda body scoped"
          return (hlam, hform, hnl)
        match lformals, actuals with
        | [lf], [a1] =>
          let (hlam, hform, hnl) ← certs [lf]
          let ha ← proveConv cfg envExpr ctx a1
          let hsub ← proveConv cfg envExpr ctx
            (ACL2.Replay.substTerm [lf] [a1] lamBody)
          mkAppM ``re_conv_lam1
            #[cfg.worldExpr, envExpr, reflectSymbol lam, reflectSExpr formalsE,
              reflectSExpr lamBody, reflectSExpr a1, reflectSymbol lf,
              hlam, hform, hnl, ha, hsub]
        | [f1, f2], [a1, a2] =>
          let (hlam, hform, hnl) ← certs [f1, f2]
          let ha ← proveConv cfg envExpr ctx a1
          let hb ← proveConv cfg envExpr ctx a2
          let hsub ← proveConv cfg envExpr ctx
            (ACL2.Replay.substTerm [f1, f2] [a1, a2] lamBody)
          mkAppM ``re_conv_lam2
            #[cfg.worldExpr, envExpr, reflectSymbol lam, reflectSExpr formalsE,
              reflectSExpr lamBody, reflectSExpr a1, reflectSExpr a2,
              reflectSymbol f1, reflectSymbol f2, hlam, hform, hnl, ha, hb, hsub]
        | _, _ =>
          throwError "proveConv: LAMBDA binder of {lformals.length} formals / \
                      {actuals.length} actuals unsupported (frontier): {repr t}"
      | _, _ => throwError "proveConv: malformed LAMBDA application: {repr t}"
    else throwError "proveConv: no convergence rule for {repr t}"
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
      | none =>
        -- a head KNOWN at another arity is malformed input, not a capability
        -- limit (S2 audit F2-narrowing, 2026-07-25): keep it loud
        if dpKnownHead fs.name then
          throwError "dpValExpr: {fs.name} applied at arity 1 but registered at a \
                      different arity — malformed application: {repr t}"
        else throwFrontier m!"dpValExpr: unary {fs.name} is not a DP-lift primitive (frontier): {repr t}"
  | .cons (.atom (.symbol fs)) (.cons a (.cons b .nil)) =>
    match dpBinary.lookup fs.name with
    | some (fn, _) =>
      return mkApp2 (mkConst fn) (← dpValExpr opq varVal a) (← dpValExpr opq varVal b)
    | none =>
      if dpKnownHead fs.name then
        throwError "dpValExpr: {fs.name} applied at arity 2 but registered at a \
                    different arity — malformed application: {repr t}"
      else throwFrontier m!"dpValExpr: binary {fs.name} is not a DP-lift primitive (frontier): {repr t}"
  | .cons (.atom (.symbol fs)) (.cons c (.cons th (.cons e .nil))) =>
    if fs.name == "IF" then
      let vc ← dpValExpr opq varVal c
      let vt ← dpValExpr opq varVal th
      let ve ← dpValExpr opq varVal e
      mkAppM ``cond #[mkApp (mkConst ``Logic.toBool) vc, vt, ve]
    else if dpKnownHead fs.name then
      throwError "dpValExpr: {fs.name} applied at arity 3 but registered at a \
                  different arity — malformed application: {repr t}"
    else throwFrontier m!"dpValExpr: ternary {fs.name} is not a DP-lift primitive (frontier): {repr t}"
  | .cons (.cons (.atom (.symbol lam)) (.cons formalsE (.cons lamBody .nil))) argsExpr =>
    -- a LAMBDA application (ACL2's translated LET) has the value of its
    -- BETA-REDUCT (`re_lam_beta*_val`), so the walker descends into the
    -- substituted body — the very term the rewriter records at the
    -- LAMBDA-BODY frame. Malformed binders hard-fail; a wider binder is a
    -- capability FRONTIER, not a defect.
    if lam.name == "LAMBDA" then
      -- the SAME scoping certificate the proof twin discharges by kernel
      -- decision (S2 audit F3, 2026-07-25): a non-`WellScoped` body means the
      -- substitution below could capture — malformed input (ACL2's translate
      -- closes every lambda body), never descend
      unless ACL2.Replay.WellScoped lamBody do
        throwError "dpValExpr: LAMBDA body is not closed/regular (WellScoped fails) — \
                    malformed input (translate closes lambda bodies): {repr t}"
      match ACL2.lamFormals? formalsE, argsExpr.toList? with
      | some lformals, some actuals =>
        if lformals.length == actuals.length
            && 1 ≤ lformals.length && lformals.length ≤ 2 then
          dpValExpr opq varVal (ACL2.Replay.substTerm lformals actuals lamBody)
        else
          throwFrontier m!"dpValExpr: LAMBDA binder of {lformals.length} formals / \
                          {actuals.length} actuals unsupported (frontier): {repr t}"
      | _, _ => throwError "dpValExpr: malformed LAMBDA application: {repr t}"
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
      | none =>
        if dpKnownHead fs.name then
          throwError "dpValProof: {fs.name} applied at arity 1 but registered at a \
                      different arity — malformed application: {repr t}"
        else throwFrontier m!"dpValProof: unary {fs.name} is not a DP-lift primitive (frontier)"
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
      if dpKnownHead fs.name then
        throwError "dpValProof: {fs.name} applied at arity 2 but registered at a \
                    different arity — malformed application: {repr t}"
      else throwFrontier m!"dpValProof: binary {fs.name} is not a DP-lift primitive (frontier)"
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
    else if dpKnownHead fs.name then
      throwError "dpValProof: {fs.name} applied at arity 3 but registered at a \
                  different arity — malformed application: {repr t}"
    else throwFrontier m!"dpValProof: ternary {fs.name} is not a DP-lift primitive (frontier)"
  | .cons (.cons (.atom (.symbol lam)) (.cons formalsE (.cons lamBody .nil))) argsExpr =>
    -- LAMBDA application (translated LET): the BETA-REDUCT's convergence,
    -- lifted by `re_lam_beta*_val` (see the dpValExpr twin arm).
    if lam.name == "LAMBDA" then
      match ACL2.lamFormals? formalsE, argsExpr.toList? with
      | some lformals, some actuals => do
        -- arity dispatch FIRST (S2 audit F4, 2026-07-25): a mismatched or
        -- unsupported binder must not recurse into a bogus reduct before the
        -- shape is checked — the walkers state the same predicate
        match lformals, actuals with
        | [lf], [a1] =>
          let (hlam, hform, hnl) ← lamCerts lam formalsE lamBody [lf]
          let substBody := ACL2.Replay.substTerm [lf] [a1] lamBody
          let pSub ← dpValProof cfg envExpr opq opqP varP substBody
          let vSub ← dpValExpr opq (dpVarVal envExpr varP) substBody
          let pa ← dpValProof cfg envExpr opq opqP varP a1
          let va ← dpValExpr opq (dpVarVal envExpr varP) a1
          mkAppM ``re_lam_beta1_val
            #[cfg.worldExpr, envExpr, reflectSymbol lam, reflectSExpr formalsE,
              reflectSExpr lamBody, reflectSExpr a1,
              reflectSymbol lf, va, vSub, hlam, hform, hnl, pa, pSub]
        | [f1, f2], [a1, a2] =>
          let (hlam, hform, hnl) ← lamCerts lam formalsE lamBody [f1, f2]
          let substBody := ACL2.Replay.substTerm [f1, f2] [a1, a2] lamBody
          let pSub ← dpValProof cfg envExpr opq opqP varP substBody
          let vSub ← dpValExpr opq (dpVarVal envExpr varP) substBody
          let pa ← dpValProof cfg envExpr opq opqP varP a1
          let pb ← dpValProof cfg envExpr opq opqP varP a2
          let va ← dpValExpr opq (dpVarVal envExpr varP) a1
          let vb ← dpValExpr opq (dpVarVal envExpr varP) a2
          mkAppM ``re_lam_beta2_val
            #[cfg.worldExpr, envExpr, reflectSymbol lam, reflectSExpr formalsE,
              reflectSExpr lamBody, reflectSExpr a1,
              reflectSExpr a2, reflectSymbol f1, reflectSymbol f2, va, vb, vSub,
              hlam, hform, hnl, pa, pb, pSub]
        | _, _ =>
          throwFrontier m!"dpValProof: LAMBDA binder of {lformals.length} formals / \
                          {actuals.length} actuals unsupported (frontier): {repr t}"
      | _, _ => throwError "dpValProof: malformed LAMBDA application: {repr t}"
    else throwError "dpValProof: unsupported term shape: {repr t}"
  | _ => throwError "dpValProof: unsupported term shape: {repr t}"
where
  /-- Variable values consistent with `varP` (fall back to the env lookup). -/
  dpVarVal (envExpr : Expr) (varP : Symbol → Option (Expr × Expr)) (s : Symbol) :
      MetaM Expr :=
    match varP s with
    | some (v, _) => pure v
    | none => dpConcVar envExpr s
  /-- The three kernel-decided beta certificates: head is LAMBDA, formals as
      recorded, body regular/closed (`WellScoped`). -/
  lamCerts (lam : Symbol) (formalsE lamBody : SExpr) (lformals : List Symbol) :
      MetaM (Expr × Expr × Expr) := do
    let lformalsE ← mkListLit (mkConst ``Symbol) (lformals.map reflectSymbol)
    let hlam ← proveIsNamedTrue lam "LAMBDA"
    let hform ← proveByDecide
      (← mkEq (← mkAppM ``ACL2.lamFormals? #[reflectSExpr formalsE])
              (← mkAppM ``Option.some #[lformalsE])) "lambda-val formals"
    let hnl ← proveByDecide
      (← mkEq (← mkAppM ``ACL2.Replay.WellScoped #[reflectSExpr lamBody]) (mkConst ``Bool.true))
      "well-scoped lambda-val body"
    return (hlam, hform, hnl)

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


/-- TWO-VALUEDNESS disjunction (`v = t ∨ v = nil`) for a test term's pinned
    value (G1 rung 1, inc-2 — the IF-headed `if1/boolean` test): quoted
    t/nil constants, `equal`/`lexorder` values, boolean-TP fn applications,
    and IFs with two-valued branches (recursively). `none` when no source
    applies — the caller names the frontier (never a silent success). -/
partial def boolDisj? (cfg : ReplayConfig) (ctx : ReplayCtx) (t : SExpr) :
    MetaM (Option Expr) := do
  if t == quoteT then return some (mkConst ``t_t_or_nil)
  if t == quoteNil then return some (mkConst ``nil_t_or_nil)
  let v ← ctxValExpr cfg ctx t
  if v.isAppOfArity ``Logic.equal 2 then
    return some (← mkAppM ``logic_equal_t_or_nil #[v.appFn!.appArg!, v.appArg!])
  if v.isAppOfArity ``ACL2.lexorder 2 then
    return some (← mkAppM ``lexorder_boolean #[v.appFn!.appArg!, v.appArg!])
  if v.isAppOfArity ``Logic.lt 2 then
    return some (← mkAppM ``logic_lt_t_or_nil #[v.appFn!.appArg!, v.appArg!])
  match t with
  | .cons (.atom (.symbol hs)) (.cons c (.cons a (.cons b .nil))) =>
    if hs.name == "IF" then do
      let some ha ← boolDisj? cfg ctx a | return none
      let some hb ← boolDisj? cfg ctx b | return none
      let vc ← ctxValExpr cfg ctx c
      try
        return some (← mkAppM ``cond_t_or_nil
          #[mkApp (mkConst ``Logic.toBool) vc, ha, hb])
      catch _ => return none
    else boolDisjFnTp t
  | .cons (.atom (.symbol _)) _ => boolDisjFnTp t
  | _ => return none
where
  /-- fn application with a boolean-TP hypothesis (the emitted
      `(IF (EQUAL (fn X) 'T) 'T (EQUAL (fn X) 'NIL))` corollary shape). -/
  boolDisjFnTp (t : SExpr) : MetaM (Option Expr) := do
    let .cons (.atom (.symbol fs)) argsSpine := t | return none
    let some (_, _, tpHyp) := ctx.tpHyps.find? (fun (nm, _, _) => nm == fs.name)
      | return none
    let some (formals, _) := cfg.worldVal.defs.get? fs | return none
    let args := (argsSpine.toList?).getD []
    unless formals.length == args.length do return none
    let some (v, conv) := ctx.val? t | return none
    let fact := mkAppN tpHyp ((#[cfg.envExpr] : Array Expr)
      ++ (args.map reflectSExpr).toArray ++ #[v, conv])
    try
      return some (← mkAppM ``tp_boolean_t_or_nil #[v, fact])
    catch _ => return none

/-- N-ary definition info (the c3 generalization of `DefInfo`). -/
structure DefInfoN where
  formals : List Symbol
  body : SExpr
  defFact : Expr
  closedFact : Expr
  wellScopedFact : Expr

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
    let wellScopedFact ← proveByDecide
      (← mkEq (← mkAppM ``ACL2.Replay.WellScoped #[bodyE]) (mkConst ``Bool.true)) s!"well-scoped {fn.name}"
    return { formals, body, defFact, closedFact, wellScopedFact }

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

/-- The `(:DEFINITION iff)` GROUND-ZERO recipe: `(iff A B) ⇒
    (if A (if B 't 'nil) (if B 'nil 't))` — the preprocess boot-strap
    non-rec arm's body adoption (`emit/expand-abbreviations/nonrec-body`,
    G1 iff rung), proved against the BUILTIN semantics (`Logic.iff` +
    `logic_iff_cond`) exactly as `replayImpliesDef` does for `implies`.
    The recorded rhs must be EXACTLY the unfold body instance. -/
def replayIffDef (cfg : ReplayConfig) (ctx : ReplayCtx) (n : ProofNode) :
    MetaM Expr := do
  let (lhs, rhs) := nodeLhsRhs n
  let .node _ _ _ children _ := n
  unless children.isEmpty do
    throwError "definition:iff — children on the ground-zero unfold (frontier)"
  let .cons (.atom (.symbol iffS)) (.cons A (.cons B .nil)) := lhs
    | throwError "definition:iff — lhs is not (iff A B): {repr lhs}"
  unless iffS.name == "IFF" do
    throwError "definition:iff — lhs head {iffS.name}"
  let expectedRhs : SExpr :=
    .cons (.atom (.symbol { name := "IF" }))
      (.cons A (.cons (.cons (.atom (.symbol { name := "IF" }))
        (.cons B (.cons quoteT (.cons quoteNil .nil))))
        (.cons (.cons (.atom (.symbol { name := "IF" }))
          (.cons B (.cons quoteNil (.cons quoteT .nil)))) .nil)))
  unless rhs == expectedRhs do
    throwError "definition:iff — rhs {repr rhs} is not the unfold body instance"
  let vA ← ctxValExpr cfg ctx A
  let vB ← ctxValExpr cfg ctx B
  let pA ← ctxValProof cfg ctx A
  let pB ← ctxValProof cfg ctx B
  let hNs ← proveNotSpecial { name := "IFF" }
  let hNo ← proveNoShadow cfg { name := "IFF" }
  let hr ← mkAppM ``callBuiltin_iff #[vA, vB]
  let pL ← mkAppM ``conv_builtin2
    #[cfg.worldExpr, cfg.envExpr, reflectSymbol { name := "IFF" },
      reflectSExpr A, reflectSExpr B, vA, vB,
      mkApp2 (mkConst ``Logic.iff) vA vB, hNs, hNo, pA, pB, hr]
  let pR ← ctxValProof cfg ctx rhs
  let valueEq ← mkAppM ``logic_iff_cond #[vA, vB]
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

/-- Chain a fuel-eq with an OPTIONAL continuation: `a` alone, or
    `fuel_chain_eq a b`. The ubiquitous chain-tail idiom (quality pass Q1). -/
def chainWith (a : Expr) (b? : Option Expr) : MetaM Expr :=
  match b? with
  | none => pure a
  | some b => mkAppM ``fuel_chain_eq #[a, b]

/-- Chain an OPTIONAL accumulated fuel-eq BEFORE a step: `b` alone, or
    `fuel_chain_eq a b`. -/
def chainAfter (a? : Option Expr) (b : Expr) : MetaM Expr :=
  match a? with
  | none => pure b
  | some a => mkAppM ``fuel_chain_eq #[a, b]

/-- Combine two OPTIONAL fuel-eq chains. -/
def chainOptWith (a? b? : Option Expr) : MetaM (Option Expr) :=
  match a?, b? with
  | none, b? => pure b?
  | some a, none => pure (some a)
  | some a, some b => some <$> mkAppM ``fuel_chain_eq #[a, b]

/-- `EvTrue` transport along an OPTIONAL R-TAGGED chain (backward: the
    chain's START is proved true from its END — `evtrue_of_fuel_eq` /
    `evtrue_of_evrel_siff` per relation). -/
def evtrueWithR (ch? : Option (Expr × Bool)) (p : Expr) : MetaM Expr :=
  match ch? with
  | none => pure p
  | some (ch, false) => mkAppM ``evtrue_of_fuel_eq #[ch, p]
  | some (ch, true) => mkAppM ``evtrue_of_evrel_siff #[ch, p]

/-- Chain an IFF head with an optional R-TAGGED rest (the rest's FINAL
    term's convergence injects an eq rest into the SIff lane). -/
def chainIffWithR (cfg : ReplayConfig) (ctx : ReplayCtx) (head : Expr)
    (final : SExpr) (rest : Option (Expr × Bool)) : MetaM (Expr × Bool) := do
  match rest with
  | none => return (head, true)
  | some (r, true) =>
    return (← mkAppM ``evrel_trans #[mkConst ``siff_trans, head, r], true)
  | some (r, false) => do
    let pConv ← ctxValProof cfg ctx final
    let rS ← mkAppM ``evrel_of_fuel_eq #[mkConst ``siff_refl, r, pConv]
    return (← mkAppM ``evrel_trans #[mkConst ``siff_trans, head, rS], true)

/-- Require an EVAL-EQUALITY chain (G1 rung 1, inc-2b): the chain payload
    carries its relation flag (`false` = fuel-eq, `true` = `EvRel SIff`);
    a consumer that composes with eq-only machinery names the frontier
    instead of mis-composing. -/
def chainReqEq (c? : Option (Expr × Bool)) : MetaM (Option Expr) :=
  match c? with
  | none => pure none
  | some (c, false) => pure (some c)
  | some (_, true) => throwError "chain: IFF composite where an \
      eval-equality is required (G1 rung-1 frontier)"

/-- Chain an EQ head with an optional R-TAGGED rest: eq·eq stays eq;
    eq·iff injects the head into the SIff lane via the MID term's
    convergence (the preprocess chain core's mixed compose). -/
def chainWithR (cfg : ReplayConfig) (ctx : ReplayCtx) (head : Expr)
    (mid : SExpr) (rest : Option (Expr × Bool)) : MetaM (Expr × Bool) := do
  match rest with
  | none => return (head, false)
  | some (r, false) => return (← mkAppM ``fuel_chain_eq #[head, r], false)
  | some (r, true) => do
    let pConv ← ctxValProof cfg ctx mid
    let headS ← mkAppM ``evrel_of_fuel_eq #[mkConst ``siff_refl, head, pConv]
    return (← mkAppM ``evrel_trans #[mkConst ``siff_trans, headS, r], true)

/-- `EvTrue` transport along an OPTIONAL fuel-eq chain:
    `p` alone, or `evtrue_of_fuel_eq ch p`. -/
def evtrueWith (ch? : Option Expr) (p : Expr) : MetaM Expr :=
  match ch? with
  | none => pure p
  | some ch => mkAppM ``evtrue_of_fuel_eq #[ch, p]

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

/-- `eval t` converges to `nil`: the pinned convergence cast along a falsity
    fact `hf : v(t) = nil` (`re_val_cast` plumbing, quality pass Q2). -/
def castConvToNil (cfg : ReplayConfig) (ctx : ReplayCtx) (t : SExpr)
    (hf : Expr) : MetaM Expr := do
  mkAppM ``re_val_cast
    #[cfg.worldExpr, cfg.envExpr, reflectSExpr t, ← ctxValExpr cfg ctx t,
      mkConst ``SExpr.nil, ← ctxValProof cfg ctx t, hf]

/-- Peel the leading literals of a proved disjunction along their falsity
    facts (`evtrue_extract_else` fold), leaving `EvTrue` of the LAST
    literal. `deriveF` supplies each peeled literal's falsity proof
    (throwing if unavailable). Shared by the residual-peel paths. -/
def peelToLast (cfg : ReplayConfig) (ctx : ReplayCtx) (lits : List SExpr)
    (pChild : Expr) (deriveF : SExpr → MetaM Expr) : MetaM Expr := do
  let mut p := pChild
  for L in lits.dropLast do
    p ← mkAppM ``evtrue_extract_else
      #[← castConvToNil cfg ctx L (← deriveF L), p]
  return p

/-- Ex-falso closure of a VACUOUS residual: the pushed child's clause
    (`expected`, proved as `pChild`) is all-false in scope — peel it to its
    last literal and refute (`absurd`), producing `EvTrue goalTerm`.
    Shared by the spine walker's and composeSplit's vacuous arms. -/
def vacuousResidualClose (cfg : ReplayConfig) (ctx : ReplayCtx)
    (expected : List SExpr) (pChild : Expr) (goalTerm : SExpr)
    (deriveF : SExpr → MetaM Expr) : MetaM Expr := do
  let p ← peelToLast cfg ctx expected pChild deriveF
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


/-- Unary BUILTINS whose ground-zero `:TYPE-PRESCRIPTION` corollary is the
    standard nonneg-int shape `(IF (INTEGERP (fn v)) (NOT (< (fn v) '0)) 'NIL)`,
    with the kernel lemma proving the lifted `Logic.integerp` fact against the
    builtin's own `Logic` semantics. The pin route applies an entry ONLY when
    the development EMITTED that exact corollary for the fn (`cfg.gzTps`) —
    the type fact is consumed from ACL2's emission; only its proof is the
    trusted core's (for a builtin, the `Logic` fn IS its semantics here). -/
def builtinIntTps : List (String × Name) :=
  [("LEN", ``logic_len_integerp)]

#guard builtinIntTps.all (fun e => (dpUnary.lookup e.1).isSome)

/-- The standard nonneg-int TP corollary at application `app`:
    `(IF (INTEGERP app) (NOT (< app '0)) 'NIL)`. -/
def intTpCorollary (app : SExpr) : SExpr :=
  .cons (.atom (.symbol { name := "IF" }))
    (.cons (.cons (.atom (.symbol { name := "INTEGERP" })) (.cons app .nil))
      (.cons (.cons (.atom (.symbol { name := "NOT" }))
          (.cons (.cons (.atom (.symbol { name := "<" }))
              (.cons app (.cons (.cons (.atom (.symbol { name := "QUOTE" }))
                (.cons (.atom (.number (.int 0))) .nil)) .nil))) .nil))
        (.cons quoteNil .nil)))

/-- Can the DP value walkers (`dpValExpr`/`dpValProof`) produce a value for `t`
    from the ctx pins, env variable lookups, and builtin registries alone?
    PROVISIONING guard for the builtin TP pin arm: declining just means no pin
    is offered (a replay that needs it fails at its use site) — provisioning
    itself must never throw on an unsupported shape. -/
partial def valueOfferable (ctx : ReplayCtx) (t : SExpr) : Bool :=
  (ctx.val? t).isSome ||
  match t with
  | .atom (.symbol s) => s.name != "T"   -- `re_val_var` needs ¬isNamed "t"
  | .cons (.atom (.symbol fs)) (.cons a .nil) =>
    fs.name == "QUOTE" ||
    ((dpUnary.lookup fs.name).isSome && valueOfferable ctx a)
  | .cons (.atom (.symbol fs)) (.cons a (.cons b .nil)) =>
    (dpBinary.lookup fs.name).isSome && valueOfferable ctx a && valueOfferable ctx b
  | .cons (.atom (.symbol fs)) (.cons c (.cons th (.cons e .nil))) =>
    fs.name == "IF" && valueOfferable ctx c && valueOfferable ctx th &&
      valueOfferable ctx e
  | _ => false

/-- Derive the INT-ATOM value + convergence proof of a registered unary
    BUILTIN's application (`builtinIntTps`), gated on the development having
    EMITTED the standard nonneg-int TP corollary for it (`cfg.gzTps`). Used as
    a LOCAL fallback at the use sites that need an int-shaped value for a term
    with no ctx pin (the unicity-of-0 recipe, the acl2-numberp recognizer) —
    deliberately NOT a `pinTermOpaques` arm: entering the shared `ctx.vals`
    map would make every later `dpValExpr` of the term opaque, breaking
    consumers that compute the builtin's STRUCTURAL value (e.g. the
    `definition:LEN` unfold against `gz_def_len`). Returns `none` when not
    registered / not emitted / the argument value is unofferable (the caller's
    existing hard-fail stands); an emitted corollary that DRIFTS from the
    registered shape hard-fails. -/
def builtinIntVal? (cfg : ReplayConfig) (ctx : ReplayCtx) (t : SExpr) :
    MetaM (Option (Expr × Expr)) := do
  let .cons (.atom (.symbol fs)) argSpine := t | return none
  let some intLemma := builtinIntTps.lookup fs.name | return none
  let some cor := cfg.gzTps.lookup fs.name | return none
  -- recover the corollary's formal application from the INTEGERP arm, then
  -- pin the WHOLE corollary to the standard shape at it (drift hard-fails)
  let .cons _ (.cons (.cons _ (.cons app _)) _) := cor
    | throwError "builtinIntVal?: emitted TP corollary of {fs.name} does not \
                  destructure: {repr cor}"
  unless cor == intTpCorollary app do
    throwError "builtinIntVal?: emitted TP corollary of {fs.name} drifted from \
                the registered nonneg-int shape: {repr cor}"
  let .cons arg .nil := argSpine
    | throwError "builtinIntVal?: {fs.name} not applied to exactly one arg: {repr t}"
  unless valueOfferable ctx arg do return none
  let opq := ctx.vals.map fun (o, v, _) => (o, v)
  let opqP := ctx.vals.map fun (o, _, p) => (o, p)
  let varP := fun s =>
    (ctx.varVals.find? (fun (v, _, _) => v == s)).map fun (_, v, p) => (v, p)
  let varVal := fun s => match varP s with
    | some (v, _) => pure v
    | none => dpConcVar cfg.envExpr s
  let conv ← dpValProof cfg cfg.envExpr opq opqP varP t
  let value ← dpValExpr opq varVal t
  let hInt ← mkAppM intLemma #[← dpValExpr opq varVal arg]
  let hkEx ← mkAppM ``logic_integerp_int #[value, hInt]
  let k ← mkAppM ``Exists.choose #[hkEx]
  let hvk ← mkAppM ``Exists.choose_spec #[hkEx]
  let value' := mkApp (mkConst ``SExpr.atom)
    (mkApp (mkConst ``Atom.number) (mkApp (mkConst ``Number.int) k))
  let conv' ← mkAppM ``re_val_cast
    #[cfg.worldExpr, cfg.envExpr, reflectSExpr t, value, value', conv, hvk]
  return some (value', conv')

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

/-- Derive `v(t) = nil` from the in-scope facts by a BOUNDED value-level
    type-set closure (sorting-completion-2 Class A): direct falsity facts
    (lit/seg/false-branch), EQUATION transport (a false `(not (equal p q))`
    pins vp = vq), and the car/cdr-of-non-cons COMPLETION defaults — the
    entry compositions ACL2's assume-true-false performs on the same
    assumptions (such entries emit `:PARENTS NIL :RUNES NIL/fake` — an
    assumption-composed entry with no rune provenance to consume).
    Depth-bounded, deterministic, type-checked at every fact use,
    fail-closed (`none`). -/
partial def deriveNilFact (cfg : ReplayConfig) (ctx : ReplayCtx)
    (t : SExpr) (depth : Nat := 3) : MetaM (Option Expr) := do
  let ctx ← pinTermOpaques cfg cfg.envExpr ctx t
  let vT ← ctxValExpr cfg ctx t
  let expected ← mkEq vT (mkConst ``SExpr.nil)
  -- direct, type-checked
  if let some h ← ctx.litFactByTermChecked? t expected then
    return some h
  if let some h := (ctx.branchFacts.find? (fun (bt, _, sign, _) =>
      bt == t && !sign)).map (·.2.2.2) then
    if ← Lean.Meta.isDefEq (← Lean.Meta.inferType h) expected then
      return some h
  if depth == 0 then return none
  -- car/cdr of a NON-cons (the completion defaults)
  match t with
  | .cons (.atom (.symbol cs)) (.cons u .nil) =>
    if cs.name == "CAR" || cs.name == "CDR" then
      let conspU : SExpr :=
        .cons (.atom (.symbol { name := "CONSP" })) (.cons u .nil)
      if let some hc ← deriveNilFact cfg ctx conspU (depth - 1) then
        let ctxU ← pinTermOpaques cfg cfg.envExpr ctx conspU
        let vC ← ctxValExpr cfg ctxU conspU
        if vC.isAppOfArity ``Logic.consp 1 then
          let vu := vC.appArg!
          let lem := if cs.name == "CAR" then ``logic_car_of_consp_nil
                     else ``logic_cdr_of_consp_nil
          let hDef ← Lean.Meta.mkAppM lem #[hc]
          let target := mkApp
            (mkConst (if cs.name == "CAR" then ``Logic.car else ``Logic.cdr)) vu
          if ← Lean.Meta.isDefEq vT target then
            return some hDef
  | _ => pure ()
  -- TRUE-LISTP ∧ ¬CONSP → 'NIL (TRUE-LISTP-MSORT's `MT ⇒ 'NIL`): a
  -- TRUTHY true-listp fact (a false `(not (true-listp t))`) composed with
  -- consp-false evidence pins the value to exactly nil
  let notTlp : SExpr := .cons (.atom (.symbol { name := "NOT" }))
    (.cons (.cons (.atom (.symbol { name := "TRUE-LISTP" })) (.cons t .nil))
      .nil)
  let tlpT : SExpr := .cons (.atom (.symbol { name := "TRUE-LISTP" }))
    (.cons t .nil)
  let tlpSources : List (SExpr × Expr) :=
    ctx.segFacts ++ ctx.litFacts.map (fun (_, l, h) => (l, h)) ++
    ctx.branchFacts.filterMap (fun (bt, _, sign, h) =>
      if !sign then some (bt, h) else none)
  for (st, hf) in tlpSources do
    unless st == notTlp do continue
    let ctxT2 ← pinTermOpaques cfg cfg.envExpr ctx tlpT
    let vTlp ← ctxValExpr cfg ctxT2 tlpT
    unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType hf)
        (← mkEq (mkApp (mkConst ``Logic.not) vTlp) (mkConst ``SExpr.nil)) do
      continue
    unless vTlp.isAppOfArity ``Logic.trueListp 1 do continue
    let conspT' : SExpr :=
      .cons (.atom (.symbol { name := "CONSP" })) (.cons t .nil)
    if let some hc ← deriveNilFact cfg ctxT2 conspT' (depth - 1) then
      let vC ← ctxValExpr cfg (← pinTermOpaques cfg cfg.envExpr ctxT2 conspT')
        conspT'
      if vC.isAppOfArity ``Logic.consp 1 &&
          (← Lean.Meta.isDefEq vC.appArg! vTlp.appArg!) &&
          (← Lean.Meta.isDefEq vT vTlp.appArg!) then
        let hne ← Lean.Meta.mkAppM ``logic_not_nil_ne #[vTlp, hf]
        return some (← Lean.Meta.mkAppM ``logic_nil_of_trueListp_consp_nil
          #[hne, hc])
  -- equation transport: a false (not (equal p q)) with t on one side
  let eqSources : List (SExpr × Expr) :=
    ctx.segFacts ++ ctx.litFacts.map (fun (_, l, h) => (l, h)) ++
    ctx.branchFacts.filterMap (fun (bt, _, sign, h) =>
      if !sign then some (bt, h) else none)
  for (st, hSeg) in eqSources do
    let .cons (.atom (.symbol ns))
        (.cons pq@(.cons (.atom (.symbol eqS))
          (.cons p (.cons q .nil))) .nil) := st
      | continue
    unless ns.name == "NOT" && eqS.name == "EQUAL" do continue
    unless t == p || t == q do continue
    let other := if t == p then q else p
    let ctxE ← pinTermOpaques cfg cfg.envExpr ctx pq
    let vPQ ← ctxValExpr cfg ctxE pq
    unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType hSeg)
        (← mkEq (mkApp (mkConst ``Logic.not) vPQ) (mkConst ``SExpr.nil)) do
      continue
    if let some hOther ← deriveNilFact cfg ctxE other (depth - 1) then
      let hne ← Lean.Meta.mkAppM ``logic_not_nil_ne #[vPQ, hSeg]
      let heq ← Lean.Meta.mkAppM ``Logic.eq_of_equal_ne_nil #[hne]  -- vp = vq
      let heqO ← if t == p then pure heq else Lean.Meta.mkAppM ``Eq.symm #[heq]
      -- vt = vother; vother = nil
      return some (← Lean.Meta.mkAppM ``Eq.trans #[heqO, hOther])
  return none

/-- Prove `Logic.consp v(w) = SExpr.t` from the value shape and the clause
    context (sorting-completion-2 Class A closure kit, the CONSP twin of
    `deriveNilFact`): a syntactic-cons VALUE; direct clause evidence
    (`conspEvidence?`, incl. the truthy-(CDR w) route); an IF with BOTH
    branches conses (`logic_consp_if_branches`); or `(CDR u)` of an in-scope
    proper list (`logic_trueListp_cdr_t` + `logic_consp_of_trueListp_ne_nil`
    — the truthy trueListp fact direct on `(CDR u)` or transported from
    `u`). -/
partial def deriveConspT (cfg : ReplayConfig) (ctx : ReplayCtx) (w : SExpr) :
    MetaM (Option Expr) := do
  let ctx ← pinTermOpaques cfg cfg.envExpr ctx w
  let vW ← ctxValExpr cfg ctx w
  if vW.isAppOfArity ``SExpr.cons 2 then
    return some (← Lean.Meta.mkAppM ``logic_consp_cons_t
      #[vW.appFn!.appArg!, vW.appArg!])
  if let some h ← conspEvidence? ctx w vW then
    return some h
  if let .cons (.atom (.symbol ifS)) (.cons c (.cons a (.cons b .nil))) := w then
    if ifS.name == "IF" then
      if let some ha ← deriveConspT cfg ctx a then
        if let some hb ← deriveConspT cfg ctx b then
          let vC ← ctxValExpr cfg ctx c
          return some (← Lean.Meta.mkAppM ``logic_consp_if_branches
            #[mkApp (mkConst ``Logic.toBool) vC, ha, hb])
  -- GENERAL truthy + proper-list route: (NOT (TRUE-LISTP w)) false in scope
  -- plus w-truthy evidence — a false `(NOT w)` fact or a false expanded
  -- `(IF w 'NIL 'T)` literal (ORDERED-PERMS Subgoal 3's (CONSP B))
  do
    let notOf (t : SExpr) : SExpr :=
      .cons (.atom (.symbol { name := "NOT" })) (.cons t .nil)
    let tlpW : SExpr := .cons (.atom (.symbol { name := "TRUE-LISTP" }))
      (.cons w .nil)
    let ifNilT : SExpr := .cons (.atom (.symbol { name := "IF" }))
      (.cons w (.cons quoteNil (.cons quoteT .nil)))
    let vTlpW := mkApp (mkConst ``Logic.trueListp) vW
    let sources : List (SExpr × Expr) :=
      ctx.segFacts ++ ctx.litFacts.map (fun (_, l, h) => (l, h)) ++
      ctx.branchFacts.filterMap (fun (bt, _, sign, h) =>
        if !sign then some (bt, h) else none)
    let findFact (st : SExpr) (expected : Expr) : MetaM (Option Expr) := do
      let mut r : Option Expr := none
      for (t', h) in sources do
        if r.isNone && t' == st then
          if ← Lean.Meta.isDefEq (← Lean.Meta.inferType h) expected then
            r := some h
      pure r
    let hTlp? ← findFact (notOf tlpW)
      (← mkEq (mkApp (mkConst ``Logic.not) vTlpW) (mkConst ``SExpr.nil))
    if let some hTlpF := hTlp? then do
      let hTlpNe ← Lean.Meta.mkAppM ``logic_not_nil_ne #[vTlpW, hTlpF]
      let hWne? ← do
        match ← findFact (notOf w)
            (← mkEq (mkApp (mkConst ``Logic.not) vW) (mkConst ``SExpr.nil)) with
        | some hf =>
          pure (some (← Lean.Meta.mkAppM ``logic_not_nil_ne #[vW, hf]))
        | none =>
          match ← findFact ifNilT
              (← mkEq (← Lean.Meta.mkAppM ``cond
                  #[mkApp (mkConst ``Logic.toBool) vW, mkConst ``SExpr.nil,
                    mkConst ``SExpr.t])
                (mkConst ``SExpr.nil)) with
          | some hf =>
            pure (some (← Lean.Meta.mkAppM ``logic_ne_nil_of_if_nil_t_nil #[hf]))
          | none => pure none
      if let some hWne := hWne? then
        return some (← Lean.Meta.mkAppM ``logic_consp_of_trueListp_ne_nil
          #[hTlpNe, hWne])
  if let .cons (.atom (.symbol fs)) (.cons u .nil) := w then
    if fs.name == "CDR" then do
      let ctx ← pinTermOpaques cfg cfg.envExpr ctx u
      let vU ← ctxValExpr cfg ctx u
      let vCdrU := mkApp (mkConst ``Logic.cdr) vU
      let vTlpU := mkApp (mkConst ``Logic.trueListp) vU
      let vTlpCdrU := mkApp (mkConst ``Logic.trueListp) vCdrU
      let notOf (t : SExpr) : SExpr :=
        .cons (.atom (.symbol { name := "NOT" })) (.cons t .nil)
      let tlpOf (t : SExpr) : SExpr :=
        .cons (.atom (.symbol { name := "TRUE-LISTP" })) (.cons t .nil)
      let sources : List (SExpr × Expr) :=
        ctx.segFacts ++ ctx.litFacts.map (fun (_, l, h) => (l, h)) ++
        ctx.branchFacts.filterMap (fun (bt, _, sign, h) =>
          if !sign then some (bt, h) else none)
      let findFact (st : SExpr) (expected : Expr) : MetaM (Option Expr) := do
        let mut r : Option Expr := none
        for (t', h) in sources do
          if r.isNone && t' == st then
            if ← Lean.Meta.isDefEq (← Lean.Meta.inferType h) expected then
              r := some h
        pure r
      let some hCdrF ← findFact (notOf w)
          (← mkEq (mkApp (mkConst ``Logic.not) vCdrU) (mkConst ``SExpr.nil))
        | return none
      let hCdrNe ← Lean.Meta.mkAppM ``logic_not_nil_ne #[vCdrU, hCdrF]
      let hTlpCdrNe? ← do
        match ← findFact (notOf (tlpOf w))
            (← mkEq (mkApp (mkConst ``Logic.not) vTlpCdrU)
              (mkConst ``SExpr.nil)) with
        | some hf =>
          pure (some (← Lean.Meta.mkAppM ``logic_not_nil_ne #[vTlpCdrU, hf]))
        | none =>
          match ← findFact (notOf (tlpOf u))
              (← mkEq (mkApp (mkConst ``Logic.not) vTlpU)
                (mkConst ``SExpr.nil)) with
          | some hf => do
            let hTlpNe ← Lean.Meta.mkAppM ``logic_not_nil_ne #[vTlpU, hf]
            let hTlpCdrT ← Lean.Meta.mkAppM ``logic_trueListp_cdr_t #[hTlpNe]
            let tNeNil ← proveByDecide
              (← Lean.Meta.mkAppM ``Ne
                #[mkConst ``SExpr.t, mkConst ``SExpr.nil]) "t ≠ nil"
            pure (some (← Lean.Meta.mkAppM ``ne_of_eq_of_ne #[hTlpCdrT, tNeNil]))
          | none => pure none
      let some hTlpCdrNe := hTlpCdrNe? | return none
      return some (← Lean.Meta.mkAppM ``logic_consp_of_trueListp_ne_nil
        #[hTlpCdrNe, hCdrNe])
  return none

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

/-- Instantiate a PREMISE-FREE `∀ env', EvTrue w env' t`-shaped hypothesis
    at the current env under σ: returns `EvTrue w env (substTerm σ t)` via
    the substN bridge (the with-lemma scaffold's premise-free slice — G2
    rung 2; used for user-equivalence rule conclusions and `cong:` formula
    instances). Also returns the pinned ctx (σ-term opaques). -/
def instantiateEvTrueHypAt (cfg : ReplayConfig) (ctx : ReplayCtx) (hypV : Expr)
    (σvars : List Symbol) (σterms : List SExpr) (t : SExpr) :
    MetaM (Expr × ReplayCtx) := do
  let w := cfg.worldExpr
  let env := cfg.envExpr
  let tσ := ACL2.Replay.substTerm σvars σterms t
  let mut ctx ← pinTermOpaques cfg env ctx tσ
  for tt in σterms do
    ctx ← pinTermOpaques cfg env ctx tt
  let vals ← σterms.mapM (ctxValExpr cfg ctx)
  let convs ← σterms.mapM (ctxValProof cfg ctx)
  let formalsE ← mkListLit (mkConst ``Symbol) (σvars.map reflectSymbol)
  let argsE ← mkListLit (mkConst ``SExpr) (σterms.map reflectSExpr)
  let valsE ← mkListLit (mkConst ``SExpr) vals
  let env' ← mkAppM ``bindArgsOver #[env, formalsE, valsE]
  let hlenPf ← proveByDecide
    (← mkEq (← mkAppM ``List.length #[argsE]) (← mkAppM ``List.length #[valsE]))
    "instantiateEvTrueHypAt: substN lengths"
  let prodTy ← mkAppM ``Prod #[mkConst ``SExpr, mkConst ``SExpr]
  let pFn ← withLocalDeclD `pr prodTy fun prV => do
    let fst ← mkAppM ``Prod.fst #[prV]
    let snd ← mkAppM ``Prod.snd #[prV]
    mkLambdaFVars #[prV] (← mkValConvPropEx w env fst snd)
  let entries ← (σterms.zip vals).mapM fun (tt, v) =>
    mkAppM ``Prod.mk #[reflectSExpr tt, v]
  let (_, hargsRaw) ← mkForallMemProof prodTy pFn (entries.zip convs)
  let zipE ← mkAppM ``List.zip #[argsE, valsE]
  let hargsTy ← withLocalDeclD `pr prodTy fun prV => do
    let mem ← mkAppM ``Membership.mem #[zipE, prV]
    mkForallFVars #[prV] (← mkArrow mem (mkApp pFn prV).headBeta)
  let hargs ← mkExpectedTypeHint hargsRaw hargsTy
  let hWellScoped ← proveByDecide
    (← mkEq (← mkAppM ``ACL2.Replay.WellScoped #[reflectSExpr t])
       (mkConst ``Bool.true))
    "instantiateEvTrueHypAt: WellScoped"
  -- pB : eval env (substTerm σ t) ≡ eval env' t
  let pB ← mkAppM ``evalOpt_substTerm_substN
    #[w, env, formalsE, argsE, valsE, reflectSExpr t, hWellScoped, hlenPf, hargs]
  let happ := mkApp hypV env'
  return (← mkAppM ``evtrue_of_fuel_eq #[pB, happ], ctx)

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
        else if rs.name == "INTEGERP" then
          some (``Logic.integerp, ``logic_integerp_ne_nil_t)
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
  -- if-branch assumption facts (rewrite-if-finish's assume-true-false):
  -- registered derivation ATOM-from-CONSP-false — ACL2's typeset resolution
  -- of `(ATOM u) ⇒ 'T` inside the FALSE branch of an if on `(CONSP u)`.
  if let .cons (.atom (.symbol rs)) (.cons u .nil) := term then
    if rs.name == "ATOM" then
      let conspU : SExpr :=
        .cons (.atom (.symbol { name := "CONSP" })) (.cons u .nil)
      if let some (_, vC, _, hNil) := ctx.branchFacts.find?
          (fun (t, _, sign, _) => t == conspU && !sign) then
        unless verdict == SExpr.t do
          throwError "replayRecognizer: (ATOM _) under a false (CONSP _) branch \
                      fact needs verdict t (got {repr verdict})"
        unless vC.isAppOfArity ``Logic.consp 1 do
          throwError "replayRecognizer: branch-fact value of {repr conspU} is \
                      not (Logic.consp _)"
        let vu := vC.appArg!
        let hT ← mkAppM ``logic_atom_of_consp_nil #[vu, hNil]
        let v ← ctxValExpr cfg ctx term
        unless ← isDefEq v (mkApp (mkConst ``Logic.atom) vu) do
          throwError "replayRecognizer: value of {repr term} does not match the \
                      branch fact's (Logic.atom _) instance"
        let p ← ctxValProof cfg ctx term
        return ← mkAppM ``re_val_cast
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr term, v, verdictE, p, hT]
  match term with
  | .cons (.atom (.symbol rs)) (.cons z .nil) =>
    if rs.name == "ACL2-NUMBERP" then
      let pin? ← match ctx.val? z with
        | some p => pure (some p)
        | none => builtinIntVal? cfg ctx z   -- gz-builtin TP route (e.g. LEN)
      let some (vz, pz) := pin?
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
        let inst := ACL2.Replay.substTerm formals args cor
        -- REGISTERED TP-LATTICE derivation (recognizer/false via TP): ACL2's
        -- type-set closes `(CONSP app) ⇒ 'NIL` from the fn's TP whose TYPE
        -- part is `(INTEGERP app)` (the standard corollary encoding
        -- `(IF (INTEGERP app) <bound> 'NIL)`) — type-bit disjointness, the
        -- trusted-core theorem `logic_consp_nil_of_tp_integerp`. Consumed,
        -- not inferred: the node's recorded runes cite the TP (e.g.
        -- `(CONSP (ACL2-COUNT …)) ⇒ 'NIL` in admission waterfalls).
        let intTpShape : Bool := match inst with
          | .cons (.atom (.symbol ifS))
              (.cons (.cons (.atom (.symbol intS)) (.cons z' .nil))
                (.cons _ (.cons elseB .nil))) =>
            ifS.name == "IF" && intS.name == "INTEGERP" && z' == z
              && elseB == quoteNil
          | _ => false
        let latticeRoute :=
          rs.name == "CONSP" && verdict == SExpr.nil && intTpShape
        -- otherwise the corollary, instantiated at the actual args, must BE
        -- this term (so the TP fact proves exactly this recognizer's verdict).
        unless formals.length == args.length ∧
               ((inst == term ∧ verdict == SExpr.t) ∨ latticeRoute) do
          throwError "replayRecognizer: TP corollary of {fs.name} ({repr cor}) \
                      does not match {repr term} ⇒ {repr verdict} (frontier)"
        let some (vz, convz) := ctx.val? z
          | throwError "replayRecognizer: {repr z} has no pinned value (TP recognizer, frontier)"
        -- fact : <lifted corollary at args>[appPat ↦ vz] = t  =  (REC-lift vz) = t
        let fact := mkAppN tpHyp ((#[cfg.envExpr] : Array Expr)
          ++ (args.map reflectSExpr).toArray ++ #[vz, convz])
        let hVerdict ← if latticeRoute then
            mkAppM ``logic_consp_nil_of_tp_integerp #[fact]
          else pure fact
        let p ← ctxValProof cfg ctx term
        let v ← ctxValExpr cfg ctx term
        mkAppM ``re_val_cast
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr term, v, verdictE, p, hVerdict]
      else
        let p ← ctxValProof cfg ctx term
        let v ← ctxValExpr cfg ctx term
        if ← isDefEq v verdictE then
          mkAppM ``re_val_cast
            #[cfg.worldExpr, cfg.envExpr, reflectSExpr term, v, verdictE, p,
              ← mkEqRefl verdictE]
        else if let some (_, cor, tpHyp) :=
            ctx.tpHypsAv.find? (fun (nm, _, _) => nm == fs.name) then
          -- REGISTERED ARGS-VALUED-TP derivation (recognizer/true,
          -- disjunctive-cons class; G1 arc 2026-07-29): fn's emitted TP
          -- corollary is `(IF (CONSP appPat) 'T (EQUAL appPat formalₖ))`
          -- (the BINARY-APPEND shape) and the k-th ACTUAL's value is a
          -- CONS — either disjunct forces CONSP, exactly ACL2's type-set
          -- leaf union under the cited TP rune. Consumed, not inferred.
          let some (formals, _) := cfg.worldVal.defs.get? fs
            | throwError "replayRecognizer: {fs.name} not defined in the world"
          let args := (argsSpine.toList?).getD []
          unless formals.length == args.length do
            throwError "replayRecognizer: args-valued TP — arity mismatch on {fs.name}"
          let appPat : SExpr :=
            .cons (.atom (.symbol fs))
              ((formals.map (SExpr.atom ∘ Atom.symbol)).foldr SExpr.cons .nil)
          -- the corollary's disjunct chain: (IF (CONSP appPat) 'T rest)
          -- with rest = (EQUAL appPat formal) | (IF (EQUAL appPat formal)
          -- 'T rest') — collect the disjunct formals in order
          let rec disjFormals : SExpr → Option (List Symbol)
            | .cons (.atom (.symbol eqS))
                (.cons ap2 (.cons (.atom (.symbol fv)) .nil)) =>
              if eqS.name == "EQUAL" && ap2 == appPat then some [fv] else none
            | .cons (.atom (.symbol ifS))
                (.cons (.cons (.atom (.symbol eqS))
                    (.cons ap2 (.cons (.atom (.symbol fv)) .nil)))
                  (.cons qt' (.cons rest .nil))) =>
              if ifS.name == "IF" && eqS.name == "EQUAL" && ap2 == appPat
                  && qt' == quoteT then
                (disjFormals rest).map (fv :: ·)
              else none
            | _ => none
          let fvs? : Option (List Symbol) := match cor with
            | .cons (.atom (.symbol ifS))
                (.cons (.cons (.atom (.symbol cS)) (.cons ap .nil))
                  (.cons qt (.cons rest .nil))) =>
              if ifS.name == "IF" && cS.name == "CONSP" && ap == appPat
                  && qt == quoteT then disjFormals rest
              else none
            | _ => none
          let some fvs := fvs?
            | throwError "replayRecognizer: args-valued TP corollary of {fs.name} \
                ({repr cor}) is not the disjunctive-cons shape (frontier)"
          unless rs.name == "CONSP" && verdict == SExpr.t do
            throwError "replayRecognizer: args-valued TP of {fs.name} supports only \
                (CONSP _) ⇒ 'T (got {repr term} ⇒ {repr verdict}, frontier)"
          let argVals ← args.mapM (ctxValExpr cfg ctx ·)
          let argConvs ← args.mapM (ctxValProof cfg ctx ·)
          -- per-disjunct consp evidence: the actual's value is a SYNTACTIC
          -- cons, or the clause context holds `(consp arg)` (a (not (consp
          -- arg))-falsity fact or a positive branch fact) — exactly the
          -- type-alist entries ACL2's type-set consults for the leaf union
          let evidence ← fvs.mapM fun fv => do
            let some k := formals.findIdx? (· == fv)
              | throwError "replayRecognizer: args-valued TP of {fs.name} — \
                  disjunct var {fv.name} is not a formal"
            let some vk := argVals[k]?
              | throwError "replayRecognizer: args-valued TP — no value for arg {k}"
            let some argk := args[k]?
              | throwError "replayRecognizer: args-valued TP — no arg {k}"
            match ← conspEvidence? ctx argk vk with
            | some h => pure h
            | none =>
              throwError "replayRecognizer: args-valued TP of {fs.name} — \
                  no consp evidence for disjunct arg {repr argk} (frontier)"
          let some (vz, convz) := ctx.val? z
            | throwError "replayRecognizer: {repr z} has no pinned value \
                (args-valued TP recognizer, frontier)"
          let fact := mkAppN tpHyp ((#[cfg.envExpr] : Array Expr)
            ++ (args.map reflectSExpr).toArray ++ argVals.toArray
            ++ #[vz] ++ argConvs.toArray ++ #[convz])
          let hVerdict ← match evidence with
            | [e1] => mkAppM ``logic_consp_t_of_tp_disj2 #[fact, e1]
            | [e1, e2] => mkAppM ``logic_consp_t_of_tp_disj3 #[fact, e1, e2]
            | _ => throwError "replayRecognizer: args-valued TP of {fs.name} — \
                {evidence.length} disjuncts unsupported (frontier)"
          unless ← isDefEq v (mkApp (mkConst ``Logic.consp) vz) do
            throwError "replayRecognizer: value of {repr term} does not match \
                (Logic.consp _) on the pinned application value"
          mkAppM ``re_val_cast
            #[cfg.worldExpr, cfg.envExpr, reflectSExpr term, v, verdictE, p, hVerdict]
        else
          -- REGISTERED BUILTIN-RANGE derivation: ACL2's type-set knows each
          -- primitive's return type natively (`type-set-binary-+` …), so a
          -- recognizer verdict on a BUILTIN application is the primitive's
          -- RANGE — a trusted-core theorem, keyed (recognizer, builtin head).
          -- The value is opaque-argument-blocked (`Logic.plus vz …` does not
          -- reduce), which is exactly why the range fact is a lemma.
          let range? : Option Name :=
            if rs.name == "CONSP" && verdict == SExpr.nil
                && fs.name == "BINARY-+" then
              some ``logic_consp_plus_nil
            else none
          match range? with
          | some lem =>
            unless v.isAppOfArity ``Logic.consp 1
                && v.appArg!.isAppOfArity ``Logic.plus 2 do
              throwError "replayRecognizer: value of {repr term} does not match \
                          the registered builtin-range shape (frontier)"
            let arg := v.appArg!
            let h ← mkAppM lem #[arg.appFn!.appArg!, arg.appArg!]
            mkAppM ``re_val_cast
              #[cfg.worldExpr, cfg.envExpr, reflectSExpr term, v, verdictE, p, h]
          | none =>
            -- TRUE-LISTP/CDR closure (sorting-completion-2 Class A,
            -- ORDERED-PERMS): (TRUE-LISTP (CDR u)) ⇒ 'T from an in-scope
            -- TRUTHY true-listp fact on u (a false `(not (true-listp u))`
            -- lit/seg/branch fact) — ACL2's type-set closure, value-level
            -- (`logic_trueListp_cdr_t`).
            if rs.name == "TRUE-LISTP" && verdict == SExpr.t
                && fs.name == "CDR" then do
              let .cons _ (.cons (.cons _ (.cons u .nil)) .nil) := term
                | throwError "replayRecognizer: TRUE-LISTP/CDR closure — \
                    unexpected term shape {repr term}"
              let notTlpU : SExpr := .cons (.atom (.symbol { name := "NOT" }))
                (.cons (.cons (.atom (.symbol { name := "TRUE-LISTP" }))
                  (.cons u .nil)) .nil)
              let tlpU : SExpr := .cons (.atom (.symbol { name := "TRUE-LISTP" }))
                (.cons u .nil)
              let ctxU ← pinTermOpaques cfg cfg.envExpr ctx tlpU
              let vTlpU ← ctxValExpr cfg ctxU tlpU
              let sources : List (SExpr × Expr) :=
                ctxU.segFacts ++ ctxU.litFacts.map (fun (_, l, h) => (l, h)) ++
                ctxU.branchFacts.filterMap (fun (bt, _, sign, h) =>
                  if !sign then some (bt, h) else none)
              let mut hFact? : Option Expr := none
              for (st, hf) in sources do
                if hFact?.isNone && st == notTlpU then
                  if ← isDefEq (← inferType hf)
                      (← mkEq (mkApp (mkConst ``Logic.not) vTlpU)
                        (mkConst ``SExpr.nil)) then
                    hFact? := some hf
              -- EQUATION-transport evidence (the observed ORDERED-PERMS
              -- route): u equation-equals (CONS a d) via a false
              -- (NOT (EQUAL …)) fact, and d carries the truthy true-listp
              -- fact (the elim RESTRICTION literal) — trueListp vu then
              -- reduces to trueListp vd definitionally.
              let hT ← do
                match hFact? with
                | some hf => do
                  let hne ← mkAppM ``logic_not_nil_ne #[vTlpU, hf]
                  mkAppM ``logic_trueListp_cdr_t #[hne]
                | none => do
                  -- CONS-fact route (the hoisted `tlpCons` demand): a false
                  -- `(NOT (TRUE-LISTP (CONS a w)))` fact on the recognizer's
                  -- inner term w = (CDR u) — `trueListp (cons a w)` IS
                  -- `trueListp w` definitionally, and two-valuedness gives
                  -- the 'T verdict (ORDERED-PERMS Subgoal *1/7'5').
                  let wT : SExpr := .cons (.atom (.symbol { name := "CDR" }))
                    (.cons u .nil)
                  let mut viaCons? : Option Expr := none
                  for (st, hf) in sources do
                    if viaCons?.isNone then
                      let inner? : Option SExpr :=
                        match st with
                        | .cons (.atom (.symbol ns))
                            (.cons (.cons (.atom (.symbol rs2))
                              (.cons (.cons (.atom (.symbol cs))
                                (.cons a2 (.cons d2 .nil))) .nil)) .nil) =>
                          if ns.name == "NOT" && rs2.name == "TRUE-LISTP" &&
                              cs.name == "CONS" && d2 == wT then
                            some (.cons (.atom (.symbol { name := "CONS" }))
                              (.cons a2 (.cons d2 .nil)))
                          else none
                        | _ => none
                      if let some consT := inner? then do
                        let tlpC : SExpr :=
                          .cons (.atom (.symbol { name := "TRUE-LISTP" }))
                            (.cons consT .nil)
                        let ctxC ← pinTermOpaques cfg cfg.envExpr ctxU tlpC
                        let vTlpC ← ctxValExpr cfg ctxC tlpC
                        if ← isDefEq (← inferType hf)
                            (← mkEq (mkApp (mkConst ``Logic.not) vTlpC)
                              (mkConst ``SExpr.nil)) then
                          let hne ← mkAppM ``logic_not_nil_ne #[vTlpC, hf]
                          viaCons? := some (← mkAppM
                            ``logic_trueListp_ne_nil_t #[vTlpC.appArg!, hne])
                  if let some h := viaCons? then pure h else do
                  let mut viaEq? : Option Expr := none
                  for (st, hf) in sources do
                    if viaEq?.isNone then
                      let eqSides? : Option (SExpr × SExpr) := do
                        let .cons (.atom (.symbol ns))
                            (.cons (.cons (.atom (.symbol eqS))
                              (.cons p (.cons q .nil))) .nil) := st | none
                        guard (ns.name == "NOT" && eqS.name == "EQUAL")
                        if q == u then some (p, q)
                        else if p == u then some (q, p)
                        else none
                      if let some (c, _) := eqSides? then
                        if let .cons (.atom (.symbol cS))
                            (.cons a2 (.cons d2 .nil)) := c then
                          if cS.name == "CONS" then do
                            let notTlpD : SExpr :=
                              .cons (.atom (.symbol { name := "NOT" }))
                                (.cons (.cons
                                  (.atom (.symbol { name := "TRUE-LISTP" }))
                                  (.cons d2 .nil)) .nil)
                            let tlpD : SExpr :=
                              .cons (.atom (.symbol { name := "TRUE-LISTP" }))
                                (.cons d2 .nil)
                            let ctxD ← pinTermOpaques cfg cfg.envExpr ctxU
                              (.cons (.atom (.symbol { name := "CONS" }))
                                (.cons a2 (.cons d2 .nil)))
                            let vTlpD ← ctxValExpr cfg ctxD tlpD
                            let mut hD? : Option Expr := none
                            for (st2, hf2) in sources do
                              if hD?.isNone && st2 == notTlpD then
                                if ← isDefEq (← inferType hf2)
                                    (← mkEq (mkApp (mkConst ``Logic.not) vTlpD)
                                      (mkConst ``SExpr.nil)) then
                                  hD? := some hf2
                            if let some hfD := hD? then do
                              let pq : SExpr :=
                                .cons (.atom (.symbol { name := "EQUAL" }))
                                  (.cons c (.cons u .nil))
                              -- the fact's own equality orientation
                              let stEq := match st with
                                | .cons _ (.cons e .nil) => e
                                | _ => pq
                              let ctxE ← pinTermOpaques cfg cfg.envExpr ctxD stEq
                              let vPQ ← ctxValExpr cfg ctxE stEq
                              if ← isDefEq (← inferType hf)
                                  (← mkEq (mkApp (mkConst ``Logic.not) vPQ)
                                    (mkConst ``SExpr.nil)) then
                                let hneEq ← mkAppM ``logic_not_nil_ne #[vPQ, hf]
                                let heq ← mkAppM ``Logic.eq_of_equal_ne_nil
                                  #[hneEq]  -- vp = vq (record orientation)
                                -- orient to vu = v(CONS a d)
                                let .cons _ (.cons pT (.cons _ .nil)) := stEq
                                  | pure ()
                                let heqU ← if pT == u then pure heq
                                  else mkAppM ``Eq.symm #[heq]
                                let vd ← ctxValExpr cfg ctxE d2
                                let va ← ctxValExpr cfg ctxE a2
                                let _ := va
                                -- trueListp vu = trueListp (cons va vd)
                                --             ≡ trueListp vd (defeq)
                                -- trueListp vu = trueListp (cons va vd)
                                -- ≡ trueListp vd (defeq); ≠ nil from d
                                let hcong ← mkAppM ``congrArg
                                  #[mkConst ``Logic.trueListp, heqU]
                                let hDne ← mkAppM ``logic_not_nil_ne
                                  #[vTlpD, hfD]
                                let _ := vd
                                viaEq? := some (← mkAppM ``ne_of_eq_of_ne
                                  #[hcong, hDne])
                  match viaEq? with
                  | some h => mkAppM ``logic_trueListp_cdr_t #[h]
                  | none =>
                    throwError "replayRecognizer: TRUE-LISTP/CDR closure — no \
                        truthy true-listp fact for {repr u} in scope \
                        (direct, cons-fact, or equation-transport; frontier)"
              unless vTlpU.isAppOfArity ``Logic.trueListp 1 do
                throwError "replayRecognizer: value of {repr tlpU} is not \
                    (Logic.trueListp _)"
              unless ← isDefEq v (mkApp (mkConst ``Logic.trueListp)
                  (mkApp (mkConst ``Logic.cdr) vTlpU.appArg!)) do
                throwError "replayRecognizer: value of {repr term} does not \
                    match (Logic.trueListp (Logic.cdr _))"
              mkAppM ``re_val_cast
                #[cfg.worldExpr, cfg.envExpr, reflectSExpr term, v, verdictE,
                  p, hT]
            else if rs.name == "CONSP" && verdict == SExpr.t then do
              -- CONSP closure (sorting-completion-2, ORDERED-PERMS):
              -- `deriveConspT` — syntactic-cons value, clause evidence,
              -- IF-branch split, or (CDR u)-of-a-proper-list
              let .cons _ (.cons w .nil) := term
                | throwError "replayRecognizer: CONSP closure — \
                    unexpected term shape {repr term}"
              let ctxU ← pinTermOpaques cfg cfg.envExpr ctx term
              let some hT ← deriveConspT cfg ctxU w
                | throwError "replayRecognizer: CONSP closure — no consp \
                    derivation for {repr w} in scope (frontier)"
              let vW ← ctxValExpr cfg (← pinTermOpaques cfg cfg.envExpr ctxU w) w
              unless ← isDefEq v (mkApp (mkConst ``Logic.consp) vW) do
                throwError "replayRecognizer: value of {repr term} does not \
                    match (Logic.consp _)"
              mkAppM ``re_val_cast
                #[cfg.worldExpr, cfg.envExpr, reflectSExpr term, v, verdictE,
                  p, hT]
            else
              throwError "replayRecognizer: value of {repr term} does not reduce to {repr verdict} \
                        (no TP hypothesis for {fs.name})"
    else
      let p ← ctxValProof cfg ctx term
      let v ← ctxValExpr cfg ctx term
      if ← isDefEq v verdictE then
        let hv ← mkEqRefl verdictE
        mkAppM ``re_val_cast
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr term, v, verdictE, p, hv]
      else if rs.name == "CONSP" && verdict == SExpr.t then do
        -- CONSP of a variable/simple inner resolved from the clause context
        -- (ORDERED-PERMS: (CONSP B) ⇒ 'T from the truthy-(CDR B) evidence)
        let .cons _ (.cons w .nil) := term
          | throwError "replayRecognizer: CONSP closure — unexpected term \
              shape {repr term}"
        let ctxU ← pinTermOpaques cfg cfg.envExpr ctx term
        let some hT ← deriveConspT cfg ctxU w
          | throwError "replayRecognizer: CONSP closure — no consp \
              derivation for {repr w} in scope (frontier); lit \
              {repr (ctxU.litFacts.map (·.2.1))}; seg \
              {repr (ctxU.segFacts.map (·.1))}; branch \
              {repr (ctxU.branchFacts.map (fun (t,_,sg,_) => (t, sg)))}"
        let vW ← ctxValExpr cfg (← pinTermOpaques cfg cfg.envExpr ctxU w) w
        unless ← isDefEq v (mkApp (mkConst ``Logic.consp) vW) do
          throwError "replayRecognizer: value of {repr term} does not \
              match (Logic.consp _)"
        mkAppM ``re_val_cast
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr term, v, verdictE, p, hT]
      else
        throwError "replayRecognizer: value of {repr term} does not reduce to {repr verdict}"
  | _ => throwError "replayRecognizer: not a recognizer application: {repr term}"

/-- The node-level recursion interface (WP2 Stage 2): the knot's entry
    points as a record, so node recipes are top-level defs taking `rec`
    instead of members of one `mutual` block (new recipes land additively).
    Tied ONCE below (`replayNode`/`replayRewrites` — the public names and
    signatures are unchanged from the pre-WP2 mutual). -/
structure NodeRec where
  /-- `replayNode` — the per-node rune dispatcher. -/
  node : ReplayConfig → ReplayCtx → ProofNode → Nat → MetaM Expr
  /-- `replayRewrites` — the chain walker (explicit depth AND strip; strip
      entries tagged with the appending node's block kind — pass-local). -/
  rewrites : ReplayConfig → ReplayCtx → SExpr → List ProofNode → Nat →
    List (Option String × Nat) → MetaM (Option (Expr × Bool) × SExpr)

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

/-- `bridgeEqualNilNorm` at DEPTH: descend the UNIQUE-difference path of
    reached vs recorded (same head/arity along it), bridge the mismatching
    subterm, and lift through the common frames (sorting-completion-2,
    ORDERED-PERMS Subgoal *1/2'5' literal 4: the normalization fires INSIDE
    an if-finish/combined branch after the 'NIL substitution). More than one
    differing child at any level → `none` (the caller's fail-closed
    mismatch error stands). -/
partial def bridgeEqualNilNormDeep (cfg : ReplayConfig) (ctx : ReplayCtx)
    (reached recorded : SExpr) : MetaM (Option Expr) := do
  if let some h ← bridgeEqualNilNorm cfg ctx reached recorded then
    return some h
  let .cons (.atom (.symbol f1)) args1 := reached | return none
  let .cons (.atom (.symbol f2)) args2 := recorded | return none
  unless f1 == f2 && f1.name != "QUOTE" do return none
  let some l1 := args1.toList? | return none
  let some l2 := args2.toList? | return none
  unless l1.length == l2.length do return none
  let diffs := (l1.zip l2).zipIdx.filter fun ((x, y), _) => x != y
  let [((x, y), i)] := diffs | return none
  let some inner ← bridgeEqualNilNormDeep cfg ctx x y | return none
  let st : PathStep := { fn := f1, arity := l1.length, argIdx := i,
                         siblings := l1.eraseIdx i }
  return some (← applyStep cfg.worldExpr cfg.envExpr st x y inner)

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
                di.defFact, di.closedFact, di.wellScopedFact, p1, hbody]
          | [f1, f2], [a1, a2], [v1, v2], [p1, p2] =>
            let hbody ← mkAppM ``re_body_conv2
              #[cfg.worldExpr, cfg.envExpr, reflectSymbol fn, reflectSymbol f1, reflectSymbol f2,
                reflectSExpr di.body, reflectSExpr a1, reflectSExpr a2, v1, v2, rv, hns,
                di.defFact, p1, p2, papp]
            mkAppM ``evalOpt_unfold2_conv
              #[cfg.worldExpr, cfg.envExpr, reflectSymbol fn, reflectSymbol f1, reflectSymbol f2,
                reflectSExpr di.body, reflectSExpr a1, reflectSExpr a2, v1, v2, rv, hns,
                di.defFact, di.closedFact, di.wellScopedFact, p1, p2, hbody]
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
                hns, di.defFact, di.closedFact, di.wellScopedFact, p1, p2, p3, hbody]
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
                di.defFact, di.closedFact, di.wellScopedFact, harg, hbodyAll]
          | [f1, f2], [a1, a2] =>
            let h1 ← proveConv cfg cfg.envExpr ctx a1
            let h2 ← proveConv cfg cfg.envExpr ctx a2
            mkAppM ``re_unfold2_conv
              #[cfg.worldExpr, cfg.envExpr, reflectSymbol fn, reflectSymbol f1, reflectSymbol f2,
                reflectSExpr di.body, reflectSExpr a1, reflectSExpr a2, hns,
                di.defFact, di.closedFact, di.wellScopedFact, h1, h2, hbodyAll]
          | [f1, f2, f3], [a1, a2, a3] =>
            let h1 ← proveConv cfg cfg.envExpr ctx a1
            let h2 ← proveConv cfg cfg.envExpr ctx a2
            let h3 ← proveConv cfg cfg.envExpr ctx a3
            mkAppM ``re_unfold3_conv
              #[cfg.worldExpr, cfg.envExpr, reflectSymbol fn, reflectSymbol f1,
                reflectSymbol f2, reflectSymbol f3, reflectSExpr di.body,
                reflectSExpr a1, reflectSExpr a2, reflectSExpr a3, hns,
                di.defFact, di.closedFact, di.wellScopedFact, h1, h2, h3, hbodyAll]
          | _, _ => throwError "definition: only 1/2/3-arg unfolds supported (frontier)"
      pure (di.formals, di.body, unfold)
  -- children chain over the substituted body (depth+1: their paths carry one more
  -- boundary frame), reaching the node's recorded rhs
  let substBody := ACL2.Replay.substTerm formals args body
  let (chainOpt, finalTerm) ← rec.rewrites cfg ctx substBody children (depth + 1) []
  let chainOpt ← chainReqEq chainOpt
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

/-- Replay a `lambda-body` node — the BETA step of a translated `let`/`mv-let`
    (emitted at `rewrite-fncall`'s lambda case, S2 2026-07-24). Structurally
    the definition-unfold recipe with the binder in place of a defun: the node
    replaces the lambda application (actuals already rewritten by earlier chain
    steps) by its body under `formals ↦ actuals`, and the adopted LAMBDA-BODY
    block rewrites that substituted body on to the node's recorded rhs. The
    scoping side conditions are ACL2's own translate invariant, re-checked here
    by kernel decision (`WellScoped` / freeVars ⊆ formals). -/
partial def replayLambdaBody (rec : NodeRec) (cfg : ReplayConfig) (ctx : ReplayCtx)
    (n : ProofNode) (depth : Nat) : MetaM Expr := do
  let (lhs, rhs) := nodeLhsRhs n
  let .node _ _ _ children _ := n
  let some (head, lam, actuals) := asLamApp lhs
    | throwError "lambda-body: lhs is not a lambda application: {repr lhs}"
  let some (_, formalsE, lamBody) := asLamHead head
    | throwError "lambda-body: malformed LAMBDA head: {repr head}"
  let some lformals := ACL2.lamFormals? formalsE
    | throwError "lambda-body: malformed LAMBDA formals: {repr formalsE}"
  let lamE := reflectSymbol lam
  let formalsSE := reflectSExpr formalsE
  let bodyE := reflectSExpr lamBody
  let lformalsE ← mkListLit (mkConst ``Symbol) (lformals.map reflectSymbol)
  let hlam ← proveIsNamedTrue lam "LAMBDA"
  let hform ← proveByDecide
    (← mkEq (← mkAppM ``ACL2.lamFormals? #[formalsSE]) (← mkAppM ``Option.some #[lformalsE]))
    "lambda-body formals"
  let hnl ← proveByDecide
    (← mkEq (← mkAppM ``ACL2.Replay.WellScoped #[bodyE]) (mkConst ``Bool.true)) "well-scoped lambda body"
  let hbodyAll ← proveConvAllEnv cfg ctx lamBody
  let unfold ← match lformals, actuals with
    | [lf], [a1] =>
      let h1 ← proveConv cfg cfg.envExpr ctx a1
      mkAppM ``re_lam_beta1_conv
        #[cfg.worldExpr, cfg.envExpr, lamE, formalsSE, bodyE, reflectSExpr a1,
          reflectSymbol lf, hlam, hform, hnl, h1, hbodyAll]
    | [f1, f2], [a1, a2] =>
      let h1 ← proveConv cfg cfg.envExpr ctx a1
      let h2 ← proveConv cfg cfg.envExpr ctx a2
      mkAppM ``re_lam_beta2_conv
        #[cfg.worldExpr, cfg.envExpr, lamE, formalsSE, bodyE, reflectSExpr a1,
          reflectSExpr a2, reflectSymbol f1, reflectSymbol f2,
          hlam, hform, hnl, h1, h2, hbodyAll]
    | _, _ =>
      throwError "lambda-body: binder of {lformals.length} formals / {actuals.length} \
                  actuals is a frontier — only 1- and 2-actual translated lets are emitted"
  -- the adopted LAMBDA-BODY block rewrites the substituted body (depth+1: its
  -- paths carry the LAMBDA-BODY boundary frame)
  let substBody := ACL2.Replay.substTerm lformals actuals lamBody
  let (chainOpt, finalTerm) ← rec.rewrites cfg ctx substBody children (depth + 1) []
  let chainOpt ← chainReqEq chainOpt
  unless finalTerm == rhs do
    throwError "lambda-body: children chain reached {repr finalTerm}, node rhs is {repr rhs}"
  match chainOpt with
  | none => return unfold
  | some ch => mkAppM ``fuel_chain_eq #[unfold, ch]

/-- A clause-context equation literal `(not (equal A B))`, viewed as its sides. -/
def notEqualSides? : SExpr → Option (SExpr × SExpr)
  | .cons (.atom (.symbol ns))
      (.cons (.cons (.atom (.symbol es)) (.cons a (.cons b .nil))) .nil) =>
    if ns.name == "NOT" && es.name == "EQUAL" then some (a, b) else none
  | _ => none

/-- The in-scope clause-context EQUATIONS: every litFact/segFact of shape
    `(not (equal A B))`, as side pairs with the recorded falsity proof. This
    set's equivalence closure IS ACL2's type-alist class structure over the
    clause (assume-true-false on every literal). -/
def inScopeEquations (ctx : ReplayCtx) :
    List (SExpr × SExpr × Expr × Bool) :=
  -- an edge is (a, b, proof, truthy): a FALSE `(not (equal a b))` fact
  -- (proof : v(not(equal a b)) = nil), or — truthy = true — a TRUE
  -- `(equal a b)` branch fact (proof : v(equal a b) ≠ nil, the assumed
  -- if-test of an enclosing branch — PERM-CONS's (EQUAL X1 A) then-branch)
  (ctx.litFacts.filterMap fun (_, t, h) =>
    (notEqualSides? t).map fun (a, b) => (a, b, h, false)) ++
  (ctx.segFacts.filterMap fun (t, h) =>
    (notEqualSides? t).map fun (a, b) => (a, b, h, false)) ++
  (ctx.branchFacts.filterMap fun (bt, _, sign, h) =>
    if sign then
      match bt with
      | .cons (.atom (.symbol es)) (.cons a (.cons b .nil)) =>
        if es.name == "EQUAL" then some (a, b, h, true) else none
      | _ => none
    else none)

/-- BFS a chain `src → dst` through the equation edges, each usable in either
    orientation. DETERMINISTIC, not search: the closure of a finite equation
    set is canonical, edges are tried in fact order, and the first (shortest)
    path is taken — any valid chain proves the same pinned equation. Each step
    is `(a, b, falsityProof, flipped)` (`flipped` = walked b→a). -/
def eqChain? (eqs : List (SExpr × SExpr × Expr × Bool)) (src dst : SExpr) :
    Option (List (SExpr × SExpr × Expr × Bool × Bool)) := Id.run do
  if src == dst then return some []
  let mut paths : List (SExpr × List (SExpr × SExpr × Expr × Bool × Bool)) :=
    [(src, [])]
  let mut visited : List SExpr := [src]
  for _ in List.range (eqs.length + 1) do
    let mut next : List (SExpr × List (SExpr × SExpr × Expr × Bool × Bool)) := []
    for (t, path) in paths do
      for (a, b, h, truthy) in eqs do
        let step? :=
          if a == t && !visited.contains b then
            some (b, (a, b, h, truthy, false))
          else if b == t && !visited.contains a then
            some (a, (a, b, h, truthy, true))
          else none
        if let some (t', edge) := step? then
          let path' := path ++ [edge]
          if t' == dst then return some path'
          visited := visited ++ [t']
          next := next ++ [(t', path')]
    paths := next
  return none

/-- Compose the value-level equality `val(src) = val(dst)` along an equation
    chain (TRANSITIVE type-alist equivalence, MDD-ratified 2026-07-23: ACL2's
    type-alist stores equivalence CLASSES, never a chain — the composition is
    derived deterministically here, its target pinned by the solidify node's
    emitted `:EQUIV-TERM`). Returns `none` on an empty chain. -/
def composeEqChain (cfg : ReplayConfig) (ctx : ReplayCtx)
    (chain : List (SExpr × SExpr × Expr × Bool × Bool)) :
    MetaM (Option Expr) := do
  let mut acc : Option Expr := none
  for (a, b, hf, truthy, flipped) in chain do
    let va ← ctxValExpr cfg ctx a
    let vb ← ctxValExpr cfg ctx b
    let hEq ←
      if truthy then
        -- a TRUE (equal a b) branch fact: v(equal a b) ≠ nil decodes to
        -- va = vb directly
        mkAppM ``Logic.eq_of_equal_ne_nil #[hf]
      else
        mkAppM ``logic_not_equal_nil_eq #[va, vb, hf]
    let hEq ← if flipped then mkAppM ``Eq.symm #[hEq] else pure hEq
    acc := some (← match acc with
      | none => pure hEq
      | some p => mkAppM ``Eq.trans #[p, hEq])
  return acc

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
  -- route through the R-parameterized judgment, not the eval-equality recipes.
  -- EXEMPT the COMPOSITE node classes (definition unfolds and lambda betas,
  -- S2b 2026-07-25): their :EQUIV is the geneqv-derived strength of ACL2's
  -- CLAIM for the whole lhs⇒rhs composite (honest emission, option B), but
  -- the replay never uses that label — it composes the recorded child chain
  -- and hard-checks it reaches the recorded rhs, so what it proves is the
  -- kernel-checked EQUALITY of its own composition (stronger than an iff
  -- claim is sound; a genuinely-iff CHILD still gates at its own node, and a
  -- composite whose rhs needs an unrecorded iff-only normalization fails the
  -- rhs check — fail-closed either way).
  unless prov.equiv == "equal" || rty == "definition" || rty == "lambda-body" do
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
        -- J6 → S1 (MDD-ratified 2026-07-23): the type-set believed the
        -- equivalence under the clause context (verdict-class, no recorded
        -- derivation — ACL2 has nothing more to emit). When the equation
        -- lies in the context's equivalence CLOSURE, the closure chain IS
        -- the derivation — the same deterministic route as the transitive
        -- literal case. Verdicts beyond the equation closure (genuine
        -- type-set reasoning, e.g. both sides nil under ¬consp) remain the
        -- named J6 frontier.
        let eqs := inScopeEquations ctx
        let some chain := eqChain? eqs lhs rhs
          | throwFrontier m!"solidify: type-set-derived equivalence \
              {repr (prov.equivTerm.getD .nil)} — not in the clause context's \
              equation closure ({eqs.length} in-scope equation(s)); \
              value-level type-set discharge not implemented (J6 replay \
              frontier)"
        let some valueEq ← composeEqChain cfg ctx chain
          | throwError "solidify: internal — empty equation chain for \
                        type-set-derived {repr lhs} ⇒ {repr rhs}"
        let pl ← ctxValProof cfg ctx lhs
        let pr ← ctxValProof cfg ctx rhs
        return ← mkAppM ``fuel_eq_of_conv #[pl, pr, valueEq]
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
    if lhs == ta && rhs == tb || lhs == tb && rhs == ta then
      let flip := lhs == tb && rhs == ta
      let va ← ctxValExpr cfg ctx ta
      let vb ← ctxValExpr cfg ctx tb
      -- hNil : Logic.not (Logic.equal va vb) = nil  (the spine built the literal's
      -- value with the same builder, so this is its exact type)
      let hEq ← mkAppM ``logic_not_equal_nil_eq #[va, vb, hNil]   -- va = vb
      let valueEq ← if flip then mkAppM ``Eq.symm #[hEq] else pure hEq
      let pl ← ctxValProof cfg ctx lhs
      let pr ← ctxValProof cfg ctx rhs
      mkAppM ``fuel_eq_of_conv #[pl, pr, valueEq]
    else
      -- TRANSITIVE type-alist equivalence (MDD-ratified 2026-07-23): the
      -- node's equation is a composition across the clause's equations —
      -- ACL2's type-alist unions equivalence classes and records no chain
      -- (there is nothing more to emit), so derive the chain as the
      -- deterministic closure of the in-scope equations. The three
      -- E-equations of HOW-MANY-EVENS-AND-ODDS *1/2.8 are the anchor case.
      let eqs := inScopeEquations ctx
      let some chain := eqChain? eqs lhs rhs
        | throwError "solidify: node sides {repr lhs} ⇒ {repr rhs} match \
                      neither the source equation ({repr ta} = {repr tb}) nor \
                      any equation chain of the clause context \
                      ({eqs.length} in-scope equation(s)) (frontier)"
      let some valueEq ← composeEqChain cfg ctx chain
        | throwError "solidify: internal — empty equation chain for distinct \
                      sides {repr lhs} ⇒ {repr rhs}"
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
      let chainOpt ← chainReqEq chainOpt
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
      let chainOpt ← chainReqEq chainOpt
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
      let pin? ← match ctx.val? z with
        | some p => pure (some p)
        | none => builtinIntVal? cfg ctx z   -- gz-builtin TP route (e.g. LEN)
      let some (vz, pz) := pin?
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
      let chainOpt ← chainReqEq chainOpt
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
      let chainOpt ← chainReqEq chainOpt
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
    else if dname == "IFF" && (cfg.worldVal.defs.get? { name := "IFF" }).isNone then
      -- `iff` is likewise an evalOpt BUILTIN (the preprocess boot-strap
      -- non-rec arm's body adoption, G1 iff rung)
      replayIffDef cfg ctx n
    else replayDefinition rec cfg ctx n depth
  | "lambda-body", _ => replayLambdaBody rec cfg ctx n depth
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
          else if vC.isAppOfArity ``Logic.lt 2 then
            -- `<` test (G1 rung 1, p6): two-valued builtin — same closer
            -- via the disjunction form.
            mkAppM ``cond_toBool_of_t_or_nil
              #[← mkAppM ``logic_lt_t_or_nil #[vC.appFn!.appArg!, vC.appArg!]]
          else if (match c with
                   | .cons (.atom (.symbol s)) (.cons _ (.cons _ (.cons _ .nil))) =>
                     s.name == "IF"
                   | _ => false) then do
            -- IF-headed test (G1 rung 1, inc-2 — p3-conj-mid-literal):
            -- two-valuedness derived STRUCTURALLY from the branches
            -- (quoted constants / equal / lexorder / boolean-TP fns,
            -- recursively through nested ifs) — the same sources ACL2's
            -- type-set unions over the if's leaves.
            let some hd ← boolDisj? cfg ctx c
              | throwError "if1/boolean: IF-headed test {repr c} has a \
                  branch with no two-valuedness source (frontier)"
            mkAppM ``cond_toBool_of_t_or_nil #[hd]
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
  | "compound-recognizer", "ZP-COMPOUND-RECOGNIZER" =>
    -- registered COMPOUND-RECOGNIZER recipe, pinned to the one ground-zero
    -- rule the corpus cites: `(ZP u) ⇒ 'T` believed by type-set from the
    -- in-scope FALSITY of `(INTEGERP u)` (zp is t on non-integers — kernel
    -- `logic_zp_of_integerp_nil`). Any other shape is a named frontier.
    unless prov.origin == "recognizer/true" do
      throwError "compound-recognizer: origin {prov.origin} ≠ recognizer/true \
                  (frontier)"
    let .cons (.atom (.symbol zs)) (.cons u .nil) := lhs
      | throwError "compound-recognizer: lhs {repr lhs} is not (zp u)"
    unless zs.name == "ZP" && rhs == quoteT do
      throwError "compound-recognizer: expected (zp u) ⇒ 't, got \
                  {repr lhs} ⇒ {repr rhs}"
    let intU : SExpr :=
      .cons (.atom (.symbol { name := "INTEGERP" })) (.cons u .nil)
    let some hNil := ctx.litFactByTerm? intU
      | throwError "compound-recognizer: no in-scope falsity fact for \
                    {repr intU} (frontier)"
    let vInt ← ctxValExpr cfg ctx intU
    unless vInt.isAppOfArity ``Logic.integerp 1 do
      throwError "compound-recognizer: value of {repr intU} is not \
                  (Logic.integerp _)"
    let hT ← mkAppM ``logic_zp_of_integerp_nil #[vInt.appArg!, hNil]
    let v ← ctxValExpr cfg ctx lhs
    unless ← isDefEq v (mkApp (mkConst ``Logic.zp) vInt.appArg!) do
      throwError "compound-recognizer: value of {repr lhs} does not match \
                  the (Logic.zp _) instance"
    let p ← ctxValProof cfg ctx lhs
    let pQ ← mkAppM ``re_val_quote
      #[cfg.worldExpr, cfg.envExpr, reflectSExpr SExpr.t]
    mkAppM ``fuel_eq_of_conv #[p, pQ, hT]
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
      -- sources (sorting-completion-2 Class A): the bounded value-level
      -- type-set closure — direct falsity facts, equation transport, the
      -- car/cdr completion defaults (ORDEREDP-MEMB's `E ⇒ 'NIL` composes
      -- a segment equation E = (CAR (CDR A)) with (CONSP (CDR A)) false;
      -- such entries emit :PARENTS NIL :RUNES NIL/fake — assumption-
      -- composed, no rune provenance to consume)
      let some hNil ← deriveNilFact cfg ctx lhs
        | throwError "type-alist: no spine falsity fact for {repr lhs}             (frontier; lit-facts {repr (ctx.litFacts.map (·.2.1))};             seg-facts {repr (ctx.segFacts.map (·.1))};             branch-facts {repr (ctx.branchFacts.map (fun (t,_,sg,_) => (t, sg)))})"
      let pl ← ctxValProof cfg ctx lhs
      let pr ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr cv]
      mkAppM ``fuel_eq_of_conv #[pl, pr, hNil]
    else if cv == SExpr.t then
      -- TRUTHY verdict: the spine's `(not lhs)`-false fact gives ≠ nil; the
      -- fn's EMITTED :TYPE-PRESCRIPTION (the rune is on the node) pins the
      -- non-nil value to exactly `t` (two-valuedness — consumed, not inferred)
      let notLhs : SExpr := .cons (.atom (.symbol { name := "NOT" }))
        (.cons lhs .nil)
      -- EQUIVALENCE-REFLEXIVITY route (sorting-completion-2 Class A,
      -- ORDERED-PERMS): a syntactically REFLEXIVE application (R u u) of an
      -- in-scope equivalence relation is truthy by the rule's reflexivity
      -- component (`equivrefl:<thm>` — instantiated premise-free at u);
      -- the fn's emitted TP pins the non-nil value to exactly t below.
      -- NOTE: the emitted record's ttree does not name the equivalence
      -- rune (the entry's own derivation is untracked) — this discharge
      -- is the replayed-fact route for a derivation ACL2 did not record.
      let reflHyp? : Option Expr ← do
        match lhs with
        | .cons (.atom (.symbol rS)) (.cons u (.cons u2 .nil)) =>
          if u == u2 then
            match ctx.equivReflHyps.find? (fun (sp, _) => sp.rel == rS) with
            | some (sp, hypV) => do
              let (h, _) ← instantiateEvTrueHypAt cfg ctx hypV [sp.vx] [u]
                (.cons (.atom (.symbol sp.rel))
                  (.cons (.atom (.symbol sp.vx))
                    (.cons (.atom (.symbol sp.vx)) .nil)))
              pure (some h)
            | none => pure none
          else pure none
        | _ => pure none
      if let some hRefl := reflHyp? then
        -- hRefl : EvTrue w env (R u u) → value ≠ nil; TP pins to t
        let vL ← ctxValExpr cfg ctx lhs
        let hne ← mkAppM ``ne_nil_of_evtrue_conv
          #[hRefl, ← ctxValProof cfg ctx lhs]
        let .cons (.atom (.symbol fs)) argSpine := lhs
          | throwError "type-alist: internal — refl lhs not an application"
        let some (_, _, tpHyp) := ctx.tpHyps.find? (fun (nm, _, _) => nm == fs.name)
          | throwError "type-alist: refl route needs {fs.name}'s emitted \
              :TYPE-PRESCRIPTION to pin the exact value (frontier)"
        let args := (argSpine.toList?).getD []
        let some (vLL, convL) := ctx.val? lhs
          | throwError "type-alist: refl lhs {repr lhs} has no pinned value \
              (frontier)"
        let fact := mkAppN tpHyp ((#[cfg.envExpr] : Array Expr)
          ++ (args.map reflectSExpr).toArray ++ #[vLL, convL])
        let hT ← mkAppM ``tp_cond_boolean_t #[vLL, fact, hne]
        let _ := vL
        let pl ← ctxValProof cfg ctx lhs
        let pr ← mkAppM ``re_val_quote
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr cv]
        return ← mkAppM ``fuel_eq_of_conv #[pl, pr, hT]
      let some hNotNil := ctx.litFactByTerm? notLhs
        | throwError "type-alist: no spine (not …)-falsity fact for \
                      {repr lhs} (frontier; \
                      lit-facts {repr (ctx.litFacts.map (·.2.1))}; \
                      seg-facts {repr (ctx.segFacts.map (·.1))}; \
                      branch-facts {repr (ctx.branchFacts.map
                        (fun (t,_,sg,_) => (t, sg)))})"
      let vL ← ctxValExpr cfg ctx lhs
      let hne ← mkAppM ``logic_not_nil_ne #[vL, hNotNil]
      -- TWO-VALUED BUILTIN lhs (G1 rung 1, p6): a `<`-valued term's truthy
      -- pin needs no TP — the builtin's provable two-valuedness resolves
      -- ≠ nil to = t directly.
      if vL.isAppOfArity ``Logic.lt 2 then
        let hd ← mkAppM ``logic_lt_t_or_nil #[vL.appFn!.appArg!, vL.appArg!]
        let hT ← mkAppM ``Or.resolve_right #[hd, hne]
        let pl ← ctxValProof cfg ctx lhs
        let pr ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr cv]
        return ← mkAppM ``fuel_eq_of_conv #[pl, pr, hT]
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
    -- equiv is part of the match (audit F5): ruleHyps is heterogeneous
    -- since G2 (equal rules carry eval-equality hypotheses, user-R rules
    -- the interpreted-relation shape) — this eq-composing consumer must
    -- never select a non-equal hypothesis it cannot compose
    let candidates := ctx.ruleHyps.filter fun (r, _) =>
      r.name == rname && r.idx == rune.idx && r.equiv == prov.equiv
    if candidates.isEmpty then
      throwError "rule {rname}: no stored-rule hypothesis in scope (no \
                  (:RULES …) entry — emission gap or missing telescope)"
    let matched := candidates.filter fun (r, _) =>
      ACL2.Replay.substTerm σvars σterms r.lhs == lhs
    -- an EQUAL-headed rule lhs may match the target equality COMMUTED —
    -- ACL2's `one-way-unify1` tries both argument orders for EQUAL patterns
    -- (the CAR-APPEND class). Recompute-and-check against the commuted node
    -- lhs; the proof prepends the `re_equal_comm` bridge below.
    let commutedLhs? : Option SExpr := match lhs with
      | .cons (.atom (.symbol eqS)) (.cons x (.cons y .nil)) =>
        if eqS.name == "EQUAL" then
          some (.cons (.atom (.symbol eqS)) (.cons y (.cons x .nil)))
        else none
      | _ => none
    let (matched, commuted) :=
      if matched.isEmpty then
        match commutedLhs? with
        | some lhsC =>
          (candidates.filter fun (r, _) =>
            ACL2.Replay.substTerm σvars σterms r.lhs == lhsC, true)
        | none => (matched, false)
      else (matched, false)
    let (spec, hypV) ← match matched with
      | [m] => pure m
      | m :: restM =>
        -- multi-include RE-STORAGE (sorting arc 2026-07-28): one rule stored
        -- once per include path — arithmetic-3's FOLD-CONSTS-IN-+ appears
        -- 13× in the qsort development's (:RULES …) stream, all IDENTICAL.
        -- Identical specs ARE one rule: take the first. Any DISTINCT
        -- matching specs remain a hard ambiguity.
        if restM.all (fun (r, _) => r == m.1) then pure m
        else throwError "rule {rname}: {matched.length} DISTINCT stored \
                    rules match substTerm(:SUBST, lhs) == {repr lhs} \
                    (direct or EQUAL-commuted; need exactly 1)"
      | [] => throwError "rule {rname}: 0 stored rules match \
                    substTerm(:SUBST, lhs) == {repr lhs} (direct or EQUAL-\
                    commuted; need exactly 1)"
    if prov.origin == "abbreviation-expansion" && !spec.hyps.isEmpty then
      throwError "rule {rname}: abbreviation-expansion step cites a rule \
                  with {spec.hyps.length} hypotheses — abbreviations are \
                  hyp-free (record/world mismatch)"
    -- block membership: a window-tagged sibling inside a classic block
    -- carries the block in `blockKind` (path-emission Phase 1)
    let blockOf : ProofNode → String := fun
      | .node _ _ _ _ p => if p.blockKind.isEmpty then p.innerKind else p.blockKind
    let hypKids := children.filter fun c => blockOf c == "hyp"
    let rhsKids := children.filter fun c => blockOf c == "rhs"
    let otherKids := children.filter fun c =>
      blockOf c != "hyp" && blockOf c != "rhs"
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
    let env' ← mkAppM ``bindArgsOver #[env, formalsE, valsE]
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
      let hWellScoped ← proveByDecide
        (← mkEq (← mkAppM ``ACL2.Replay.WellScoped #[reflectSExpr t]) (mkConst ``Bool.true))
        s!"WellScoped rule term ({rname})"
      mkAppM ``evalOpt_substTerm_substN
        #[w, env, formalsE, argsE, valsE, reflectSExpr t, hWellScoped, hlenPf, hargs]
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
          let vH ← ctxValExpr cfg ctx hσ
          -- TYPE-CHECKED lookup (G1 arc 2026-07-29): a term-keyed fact from
          -- another env context (pool-root/elim crossings) must not be
          -- consumed — mismatches fall through to the alternate sources.
          let checkedHit ← ctx.litFactByTermChecked? notH
            (← mkEq (mkApp (mkConst ``Logic.not) vH) (mkConst ``SExpr.nil))
          match checkedHit with
          | some hNotNil => do
            let hne ← mkAppM ``logic_not_nil_ne #[vH, hNotNil]
            mkAppM ``evtrue_of_conv_ne_nil #[← ctxValProof cfg ctx hσ, hne]
          | none =>
            -- a NOT-wrapped hyp whose ATOM's falsity is in scope: the hyp's
            -- truth is definitional (Logic.not nil = t) — the complement
            -- orientation of the direct case above (multi-elim guard-child
            -- walks surface this: DEFAULT-CAR's hyp (NOT (CONSP v2)) with
            -- the literal (CONSP v2) assumed false). S1.3 (2026-07-23): the
            -- falsity may also be an if-finish BRANCH assumption (ACL2's
            -- type-alist inside the else branch of a split on the atom —
            -- HOW-MANY-EVENS-AND-ODDS' DEFAULT-CDR relief) — consult
            -- branchFacts' false-branch entries too.
            let branchAtmNil? : SExpr → Option Expr := fun atm =>
              match ctx.branchFacts.find?
                  (fun (bf : SExpr × Expr × Bool × Expr) =>
                    bf.1 == atm && !bf.2.2.1) with
              | some (_, _, _, h) => some h
              | none => none
            if let some hAtmNil := (match hσ with
                | .cons (.atom (.symbol ns2)) (.cons atm2 .nil) =>
                  if ns2.name == "NOT" then
                    match ctx.litFactByTerm? atm2 with
                    | some h => some h
                    | none => branchAtmNil? atm2
                  else none
                | _ => none) then do
              let hT ← mkAppM ``logic_not_t_of_nil #[hAtmNil]
              let hne ← mkAppM ``ne_of_eq_of_ne #[hT, tNeNil]
              mkAppM ``evtrue_of_conv_ne_nil #[← ctxValProof cfg ctx hσ, hne]
            else do
            -- FC-DERIVED type-alist entry (emission arc 2026-07-21): the
            -- marker's :TA-RUNES name the forward-chaining rule that put the
            -- fact on the type-alist. Registered reliefs (rule-of-three:
            -- a third entry triggers registry-ization): LEXORDER-TOTAL —
            -- pinned against the EMITTED snapshot (audit-F2 style), the
            -- instantiated FC hyp discharged from the in-scope falsity
            -- fact, the conclusion via the kernel-proved
            -- `ACL2.lexorder_total`.
            let some marker := reliefMarkers.find? fun c => (nodeLhsRhs c).1 == hσ
              | throwError "rule {rname}: internal — marker vanished"
            let .node _ _ _ _ mprov := marker
            unless mprov.taRunes.any
                (fun r => r.ty == "forward-chaining" && r.name == "LEXORDER-TOTAL") do
              throwError "rule {rname}: marker-relieved hyp {repr hσ} has no \
                          (not …)-falsity fact in scope, and its :TA-RUNES \
                          {repr (mprov.taRunes.map (·.name))} name no \
                          registered FC relief (frontier; \
                          lit-facts {repr (ctx.litFacts.map (·.2.1))}; \
                          seg-facts {repr (ctx.segFacts.map (·.1))}; \
                          candidate types: {← (ctx.segFacts.filterMap
                            (fun (st, p) => if st == notH then some p else none)).mapM
                            (fun p => do pure (← Lean.Meta.inferType p))}; \
                          expected: {← mkEq (mkApp (mkConst ``Logic.not) vH)
                            (mkConst ``SExpr.nil)})"
            let some spec := cfg.fcRules.find? (·.name == "LEXORDER-TOTAL")
              | throwError "rule {rname}: :TA-RUNES cite LEXORDER-TOTAL but \
                            the (:GROUND-ZERO-FC-RULES) snapshot lacks it \
                            (stale log? recapture-all)"
            let varX : SExpr := .atom (.symbol { name := "X" })
            let varY : SExpr := .atom (.symbol { name := "Y" })
            let lexT (p q : SExpr) : SExpr :=
              .cons (.atom (.symbol { name := "LEXORDER" })) (.cons p (.cons q .nil))
            let notT (t : SExpr) : SExpr :=
              .cons (.atom (.symbol { name := "NOT" })) (.cons t .nil)
            unless spec.trigger == lexT varX varY &&
                   spec.hyps == [notT (lexT varX varY)] &&
                   spec.concls == [lexT varY varX] do
              throwError "rule {rname}: LEXORDER-TOTAL snapshot shape drifted \
                          from the pinned form: {repr spec.trigger} / \
                          {repr spec.hyps} / {repr spec.concls}"
            -- unify the concl (LEXORDER Y X) with hσ: Y ↦ u, X ↦ v
            let .cons (.atom (.symbol ls)) (.cons u (.cons v .nil)) := hσ
              | throwError "rule {rname}: FC relief target {repr hσ} is not \
                            a LEXORDER application (frontier)"
            unless ls.name == "LEXORDER" do
              throwError "rule {rname}: FC relief target {repr hσ} is not \
                          a LEXORDER application (frontier)"
            -- instantiated FC hyp (NOT (LEXORDER v u)): its truth is the
            -- in-scope FALSITY of the clause literal (LEXORDER v u)
            let source := lexT v u
            let some hNilSrc := ctx.litFactByTerm? source
              | throwError "rule {rname}: FC relief via LEXORDER-TOTAL needs \
                            the falsity of {repr source} in scope (frontier)"
            let vu ← ctxValExpr cfg ctx u
            let vv ← ctxValExpr cfg ctx v
            let hTotal ← mkAppM ``ACL2.lexorder_total #[vv, vu]
            -- left disjunct (lexorder vv vu = t) refuted by hNilSrc
            let vSrc ← ctxValExpr cfg ctx source
            let notLeft ← withLocalDeclD `h (← mkEq vSrc (mkConst ``SExpr.t))
              fun h => do
                let tEqNil ← mkAppM ``Eq.trans
                  #[← mkAppM ``Eq.symm #[h], hNilSrc]
                mkLambdaFVars #[h] (mkApp tNeNil tEqNil)
            let hT ← mkAppM ``Or.resolve_left #[hTotal, notLeft]
            let hne ← mkAppM ``ne_of_eq_of_ne #[hT, tNeNil]
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
          let chainOpt ← chainReqEq chainOpt
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
          let chainOpt ← chainReqEq chainOpt
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
    -- COMMUTED match: pCore proves the commuted equality's rewrite — prepend
    -- eval (EQUAL x y) ≡ eval (EQUAL y x) to root it at the node's lhs
    let pCore ← if commuted then do
        let .cons _ (.cons x (.cons y .nil)) := lhs
          | throwError "rule {rname}: internal — commuted non-equality lhs"
        let hNoEq ← proveNoShadow cfg { name := "EQUAL" }
        let comm ← mkAppM ``re_equal_comm
          #[w, env, reflectSExpr x, reflectSExpr y, hNoEq]
        mkAppM ``fuel_chain_eq #[comm, pCore]
      else pure pCore
    if rhsKids.isEmpty then
      unless rhsσ == rhs do
        throwError "rule {rname}: internal — rhs mismatch with no RHS chain"
      return pCore
    -- the RHS continuation: replay the recorded chain from rhsσ; it must land
    -- exactly on the node's recorded rhs (fail-closed)
    let ctx ← pinTermOpaques cfg cfg.envExpr ctx rhsσ
    let (chainOpt, finalT) ← rec.rewrites cfg ctx rhsσ rhsKids (depth + 1) []
    let chainOpt ← chainReqEq chainOpt
    unless finalT == rhs do
      throwError "rule {rname}: RHS chain reached {repr finalT}, node rhs is \
                  {repr rhs}"
    match chainOpt with
    | none => return pCore
    | some ch => mkAppM ``fuel_chain_eq #[pCore, ch]
  | "type-set-equality", _ =>
    -- `(equal x 'c) ⇒ 'nil` decided by ACL2's type-set on DISJOINT types
    -- (origin equal/type-set-nil). Registered cell: the clause context
    -- proves `(consp x)` and the quoted constant is a NON-CONS (a cons can
    -- never equal an atom — logic_equal_nil_of_consp_t_nil). Consumed, not
    -- inferred; anything else is a frontier.
    unless nodeOrigin n == "equal/type-set-nil" do
      throwError "type-set-equality: origin {nodeOrigin n} (frontier)"
    let .cons (.atom (.symbol eqS)) (.cons x (.cons qc .nil)) := lhs
      | throwError "type-set-equality: lhs {repr lhs} is not (equal x 'c) (frontier)"
    unless eqS.name == "EQUAL" do
      throwError "type-set-equality: lhs head {eqS.name} (frontier)"
    unless rhs == quoteNil do
      throwError "type-set-equality: rhs {repr rhs} ≠ 'nil (frontier)"
    let .cons (.atom (.symbol q)) (.cons cv .nil) := qc
      | throwError "type-set-equality: {repr qc} is not a quoted constant (frontier)"
    unless q.name == "QUOTE" do
      throwError "type-set-equality: {repr qc} is not a quoted constant (frontier)"
    if cv matches .cons _ _ then
      throwError "type-set-equality: constant {repr cv} is a cons — only the \
          cons-vs-atom cell is registered (frontier)"
    let ctx ← pinTermOpaques cfg cfg.envExpr ctx x
    let vx ← ctxValExpr cfg ctx x
    let some hConsp ← conspEvidence? ctx x vx
      | throwError "type-set-equality: no consp evidence for {repr x} in the \
          clause context (frontier)"
    let hC ← proveByDecide
      (← mkEq (mkApp (mkConst ``Logic.consp) (reflectSExpr cv)) (mkConst ``SExpr.nil))
      "consp of the quoted constant is nil"
    let hVal ← mkAppM ``logic_equal_nil_of_consp_t_nil #[hConsp, hC]
    let pL ← ctxValProof cfg ctx lhs
    let pR ← mkAppM ``re_val_quote #[cfg.worldExpr, cfg.envExpr, reflectSExpr SExpr.nil]
    mkAppM ``fuel_eq_of_conv #[pL, pR, hVal]
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
          let acc' ← chainAfter acc step
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
        let acc' ← chainAfter acc step
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
          acc := some (← chainAfter acc lifted)
          cur := .cons (.atom (.symbol fs)) ([c', a', b].foldr .cons .nil)
        let (chB, b') ← collapseEval cfg ctx facts b
        if let some ch := chB then
          let st : PathStep := { fn := fs, arity := 3, argIdx := 2, siblings := [c', a'] }
          let lifted ← applyStep w e st b b' ch
          acc := some (← chainAfter acc lifted)
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
      acc := some (← chainAfter acc lifted)
      curArgs := curArgs.set! i a'
  let cur : SExpr := .cons (.atom (.symbol fs)) (curArgs.toList.foldr .cons .nil)
  -- the POST-COLLAPSE term may be the form an in-scope assumption is about
  -- (argument collapse rebuilt it into another clause literal)
  if let some hNil := ctx.litFactByTerm? cur then
    let pl ← ctxValProof cfg ctx cur
    let pr ← mkAppM ``re_val_quote #[w, e, reflectSExpr SExpr.nil]
    let step ← mkAppM ``fuel_eq_of_conv #[pl, pr, hNil]
    let acc' ← chainAfter acc step
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
    let acc' ← chainAfter acc stepPf
    return (some acc', next)


/-- Lift one rewrite-if SWAPPED-P normalization step
    (`re_if_neg_test_swap`) from position `steps` (where `sub =
    (IF (IF c 'NIL 'T) a b)` sits inside `root`) to the root:
    `eval root ≡ eval root[steps ↦ swapped]`. Shared by
    `bridgeIfNegTestSwap` and the if-finish joint normalization
    (`normalizeSwapsToward`). -/
def liftNegTestSwap (cfg : ReplayConfig) (steps : List PathStep)
    (root sub c a b swapped : SExpr) : MetaM (Expr × SExpr) := do
  let mut inner ← mkAppM ``re_if_neg_test_swap
    #[cfg.worldExpr, cfg.envExpr, reflectSExpr c, reflectSExpr a, reflectSExpr b]
  let mut curL := sub
  let mut curR := swapped
  for st in steps.reverse do
    inner ← applyStep cfg.worldExpr cfg.envExpr st curL curR inner
    curL := rebuild st curL
    curR := rebuild st curR
  unless curL == root do
    throwError "liftNegTestSwap: reconstructed {repr curL} ≠ {repr root}"
  return (inner, curR)

/-- The EQUAL-NIL variant of `liftNegTestSwap` (sorting-completion-2
    Class A): `(IF (EQUAL 'NIL c) a b) ⇒ (IF c b a)` via
    `re_if_equal_nil_test_swap` (EQUAL unshadowed — kernel-decided). -/
def liftEqualNilTestSwap (cfg : ReplayConfig) (steps : List PathStep)
    (root sub c a b swapped : SExpr) : MetaM (Expr × SExpr) := do
  let hNoEq ← proveNoShadow cfg { name := "EQUAL" }
  let mut inner ← mkAppM ``re_if_equal_nil_test_swap
    #[cfg.worldExpr, cfg.envExpr, reflectSExpr c, reflectSExpr a,
      reflectSExpr b, hNoEq]
  let mut curL := sub
  let mut curR := swapped
  for st in steps.reverse do
    inner ← applyStep cfg.worldExpr cfg.envExpr st curL curR inner
    curL := rebuild st curL
    curR := rebuild st curR
  unless curL == root do
    throwError "liftEqualNilTestSwap: reconstructed {repr curL} ≠ {repr root}"
  return (inner, curR)

/-- The rewrite-if SWAPPED-P bridge (rewrite.lisp:17726-37): walk `rel` from
    `start`; when the rewritten test of an if has the negation shape
    `(IF c 'NIL 'T)`, ACL2 strips the negation and SWAPS the branches before
    descending — unconditionally and without recording a step (subsequent
    branch bkptrs refer to the swapped orientation). Two firing positions,
    both deterministic shape checks (never a search): a frame DESCENDS into
    such an if (the swap must precede the descent), or the node sits ON the
    if — its recorded `lhs` IS the swapped orientation (exact match
    required). Emits the normalization lifted to the chain root and returns
    the swapped running term; `none` when neither case applies (the caller's
    fail-closed navigation stands). -/
def bridgeIfNegTestSwap (cfg : ReplayConfig) (rel : List PathFrame)
    (start lhs : SExpr) : MetaM (Option (Expr × SExpr)) := do
  let mut cur := start
  let mut steps : List PathStep := []
  let emitSwap (steps : List PathStep) (cur c a b swapped : SExpr) :
      MetaM (Option (Expr × SExpr)) := do
    let (inner, root') ← liftNegTestSwap cfg steps start cur c a b swapped
    return some (inner, root')
  for fr in rel do
    match fr with
    | .boundary .. => return none      -- residual boundary: not this bridge's case
    | .argLam .. => return none        -- lambda descent: not this bridge's case
    | .arg idx _ =>
      if let .cons (.atom (.symbol ifS))
          (.cons (.cons (.atom (.symbol ifS2))
              (.cons c (.cons qn (.cons qt2 .nil))))
            (.cons a (.cons b .nil))) := cur then
        if ifS.name == "IF" && ifS2.name == "IF" && qn == quoteNil && qt2 == quoteT then
          let swapped : SExpr :=
            .cons (.atom (.symbol ifS)) (.cons c (.cons b (.cons a .nil)))
          return ← emitSwap steps cur c a b swapped
      match asApp cur with
      | none => return none
      | some (fn, args) =>
        if args.length > 3 || idx < 1 || idx > args.length then return none
        let siblings := (args.zipIdx).filterMap
          (fun (a, i) => if i + 1 == idx then none else some a)
        steps := steps ++ [{ fn, arity := args.length, argIdx := idx - 1, siblings }]
        cur := args[idx - 1]!
  -- TARGET case: the node is ON the swapped if — recorded lhs must BE the
  -- swapped orientation exactly
  if let .cons (.atom (.symbol ifS))
      (.cons (.cons (.atom (.symbol ifS2))
          (.cons c (.cons qn (.cons qt2 .nil))))
        (.cons a (.cons b .nil))) := cur then
    if ifS.name == "IF" && ifS2.name == "IF" && qn == quoteNil && qt2 == quoteT then
      let swapped : SExpr :=
        .cons (.atom (.symbol ifS)) (.cons c (.cons b (.cons a .nil)))
      if swapped == lhs then
        return ← emitSwap steps cur c a b swapped
  return none

/-- Find the first position where `cur` has a SWAPPED-P redex
    `(IF (IF c 'NIL 'T) a b)` while `target` has the stripped test `c` at the
    same position — descending only through structurally-parallel
    applications into the FIRST differing argument (a deterministic zip,
    never a search). Returns the path steps and the redex parts. -/
partial def findSwapPos (cur target : SExpr) (steps : List PathStep) :
    Option (List PathStep × SExpr × Bool × SExpr × SExpr × SExpr) :=
  if cur == target then none
  else
    -- the Bool tags the variant: false = the NOT-shape `(IF (IF c 'NIL 'T)
    -- a b)`; true = the EQUAL-NIL shape `(IF (EQUAL 'NIL c) a b)`
    -- (sorting-completion-2 Class A) — both swap to `(IF c b a)`
    let fire? : Option (Bool × SExpr × SExpr × SExpr) :=
      match cur, target with
      | .cons (.atom (.symbol ifS)) (.cons (.cons (.atom (.symbol ifS2))
            (.cons c (.cons qn (.cons qt2 .nil)))) (.cons a (.cons b .nil))),
        .cons (.atom (.symbol ifT')) (.cons c' _) =>
        if ifS.name == "IF" && ifS2.name == "IF" && qn == quoteNil &&
           qt2 == quoteT && ifT'.name == "IF" && c' == c then
          some (false, c, a, b)
        else none
      | _, _ => none
    let fire? := fire?.orElse fun _ =>
      match cur, target with
      | .cons (.atom (.symbol ifS)) (.cons (.cons (.atom (.symbol eqS))
            (.cons qn (.cons c .nil))) (.cons a (.cons b .nil))),
        .cons (.atom (.symbol ifT')) (.cons c' _) =>
        if ifS.name == "IF" && eqS.name == "EQUAL" && qn == quoteNil &&
           ifT'.name == "IF" && c' == c then
          some (true, c, a, b)
        else none
      | _, _ => none
    match fire? with
    | some (v, c, a, b) => some (steps, cur, v, c, a, b)
    | none =>
      match asApp cur, asApp target with
      | some (fn, args), some (fn', args') =>
        if fn == fn' && args.length == args'.length && args.length ≤ 3 then
          ((args.zip args').zipIdx).findSome? fun ((x, y), i) =>
            if x == y then none
            else
              let siblings := (args.zipIdx).filterMap
                (fun (s, j) => if j == i then none else some s)
              findSwapPos x y (steps ++
                [{ fn, arity := args.length, argIdx := i, siblings }])
        else none
      | _, _ => none

/-- Normalize `cur` toward `target` by iterated SWAPPED-P steps at mismatch
    positions (the if-finish JOINT case: a NOT unfold inside a test position
    makes ACL2 swap the enclosing if between the recorded children and the
    recorded rhs). Recompute-and-check: each step's position is dictated by
    the target, and the caller's final `== rhs` gate still stands. -/
def normalizeSwapsToward (cfg : ReplayConfig) (cur0 target : SExpr) :
    MetaM (Option Expr × SExpr) := do
  let mut cur := cur0
  let mut chain : Option Expr := none
  for _ in List.range 32 do
    if cur == target then break
    match findSwapPos cur target [] with
    | none => break
    | some (steps, sub, variant, c, a, b) =>
      let swapped : SExpr :=
        .cons (.atom (.symbol { name := "IF" }))
          (.cons c (.cons b (.cons a .nil)))
      let (inner, cur') ←
        if variant then liftEqualNilTestSwap cfg steps cur sub c a b swapped
        else liftNegTestSwap cfg steps cur sub c a b swapped
      chain ← some <$> chainAfter chain inner
      cur := cur'
  return (chain, cur)

/-- Lift an `EvRel SIff` node proof through ONE position step, per the
    congruence table (G1): if-THEN and if-ELSE positions preserve SIff (the
    untaken branch relates by reflexivity — needs the test's and the other
    branch's convergence); the if-TEST position COLLAPSES SIff to an
    eval-equality (the lazy `if` consults only `toBool`), and so do the
    IMPLIES argument positions (boolean-consumer rows, G1 rung 1 inc-2).
    Returns the lifted proof and whether it is still SIff (`true`) or
    collapsed to Eq (`false`). Any other position under an iff payload is a
    frontier. -/
def applyStepSIff (cfg : ReplayConfig) (ctx : ReplayCtx) (st : PathStep)
    (inner : Expr) : MetaM (Expr × Bool) := do
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
      this nesting at {st.fn.name}-position {st.argIdx} (conditional-congruence — \
      R1 wall d, deferred); underlying elaboration error: {e.toMessageData}"
  if st.fn.name == "IMPLIES" && st.arity == 2 then
    -- boolean-consumer COLLAPSE rows: `implies` consults only its
    -- arguments' truthiness — SIff in either argument makes the
    -- applications eval-EQUAL (needs the OTHER argument's convergence +
    -- the builtin's no-shadow fact).
    let hNo ← proveNoShadow cfg { name := "IMPLIES" }
    match st.argIdx, st.siblings with
    | 0, [c] =>
      let pc ← ctxValProof cfg ctx c
      let p ← (try mkAppM ``evrel_implies_arg1_siff_collapse #[hNo, pc, inner]
               catch e => wallD e)
      return (p, false)
    | 1, [h] =>
      let ph ← ctxValProof cfg ctx h
      let p ← (try mkAppM ``evrel_implies_arg2_siff_collapse #[hNo, ph, inner]
               catch e => wallD e)
      return (p, false)
    | _, _ => throwError "iff congruence: bad implies position {st.argIdx}"
  unless st.fn.name == "IF" && st.arity == 3 do
    throwError "iff congruence: position {st.fn.name}/{st.argIdx} does not \
                propagate IFF (frontier — only if-test/branch and implies \
                positions do)"
  match st.argIdx, st.siblings with
  | 0, [thn, els] =>
    -- TEST position: SIff collapses to eval-equality. `thn`/`els` occur only
    -- in the collapse lemma's RESULT type, so they cannot be inferred from
    -- `inner` — supply them explicitly from the path step's siblings (the
    -- former mkAppM metavariable failure here was misattributed to the
    -- wall-d nesting; the lemma is fully general in the tests).
    let p ← (try
      mkAppOptM ``evrel_if_test_siff_collapse
        #[none, none, none, none, some (reflectSExpr thn),
          some (reflectSExpr els), some inner]
      catch e => wallD e)
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

/-- The applied step's recorded equivalence relation. -/
def nodeEquiv : ProofNode → String | .node _ _ _ _ p => p.equiv

/-- Replay a chain of rewrite nodes, lifting each through the chain's start term by
    path-directed congruence (paths relativized to `depth`) and chaining. Returns
    the composed `∃N∀f≥N, eval start = eval finalTerm` (or `none` if the chain is
    empty) and the final term. -/
partial def replayRewritesWith (rec : NodeRec) (cfg : ReplayConfig) (ctx : ReplayCtx) (start : SExpr)
    (nodes : List ProofNode) (depth : Nat) (strip : List (Option String × Nat))
    -- the CURRENT literal chain's already-consumed nodes with their
    -- depth/strip (G1 rung 1, inc-2b): the or-collapse bridge re-composes
    -- the TEST-position prefix on the then-copy. Consume-and-continue
    -- recursions append; re-process sites pass unchanged; sub-chain
    -- recursions (branch children) start fresh (the default).
    (chainPrefix : List (ProofNode × Nat × List (Option String × Nat)) := []) :
    MetaM (Option (Expr × Bool) × SExpr) := do
  match nodes, depth, strip with
  | [], _, _ => return (none, start)
  | n :: rest, depth, strip => do
    let (lhs, rhs) := nodeLhsRhs n
    -- INLINE branch-window group (path-emission Phase 1): nodes tagged
    -- if-left/if-right reaching the walk directly are the surviving
    -- branch's sub-chain after a rewrite-if constant-test collapse (the
    -- tree builder attaches them inline exactly when the window term
    -- equals the collapse step's rhs). Replay the run as a chain over the
    -- window TERM and lift the composite at the window's :PATH plus the
    -- branch position its KIND names. Recipes that consume windows
    -- (if-finish's partition) strip the tag first — reaching here tagged
    -- means the inline case.
    if innerKindOf n == "if-left" || innerKindOf n == "if-right" then do
      let kind := innerKindOf n
      let some wterm := innerTermOf n
        | throwError "replayRewrites: {kind}-tagged node without a window \
            term (pre-Phase-1 log? recapture)"
      let wpath := innerPathOf n
      let mut group : List ProofNode := [n]
      let mut restG := rest
      let mut scanning := true
      while scanning do
        match restG with
        | m :: r' =>
          if innerKindOf m == kind && innerTermOf m == some wterm &&
              innerPathOf m == wpath then
            group := group ++ [m]
            restG := r'
          else scanning := false
        | [] => scanning := false
      let (chOpt, wfinal) ← replayRewritesWith rec cfg ctx wterm
        (group.map clearWindowTag) depth []
      let chOpt ← chainReqEq chOpt
      -- the collapse that precedes the window already REPLACED the if by
      -- its surviving branch in the running term, so the window term sits
      -- AT the if's own position: the lift path is the window's entry path
      -- alone (no branch frame)
      let relW ← ofExcept (relativizeFrames wpath depth)
      let frames := relW
      let steps ← match pathStepsFromFrames start frames wterm with
        | .ok st => pure st
        | .error e => throwError "replayRewrites: inline {kind} window's \
            entry path does not locate its term in the running chain: {e}"
      match chOpt with
      | none =>
        -- no effective rewrites in the window — a no-op group
        return ← replayRewritesWith rec cfg ctx start restG depth strip chainPrefix
      | some chain => do
        let mut inner := chain
        let mut curL := wterm
        let mut curR := wfinal
        for st in steps.reverse do
          inner ← applyStep cfg.worldExpr cfg.envExpr st curL curR inner
          curL := rebuild st curL
          curR := rebuild st curR
        unless curL == start do
          throwError "replayRewrites: inline {kind} window lift \
              reconstructed {repr curL} ≠ running {repr start}"
        let (restProof, finalTerm) ← replayRewritesWith rec cfg ctx curR
          restG depth strip (chainPrefix ++ [(n, depth, strip)])
        return (some (← chainWithR cfg ctx inner curR restProof), finalTerm)
    -- rewrite-if SWAPPED-P bridge: apply ACL2's silent branch swap when this
    -- node's path descends into a negation-test if in the RUNNING term, then
    -- re-process the node on the normalized term. (Skipped for the
    -- clause-context-resolution marker — it never navigates its path.)
    if (runeOf n).ty != "clause-context-resolution" then
      let rel ← relativizeAndStrip (nodePath n) depth strip
      match ← bridgeIfNegTestSwap cfg rel start lhs with
      | some (swapEq, start') =>
        let (restAll, finalT) ← replayRewritesWith rec cfg ctx start' (n :: rest) depth strip chainPrefix
        return (some (← chainWithR cfg ctx swapEq start' restAll), finalT)
      | none => pure ()
    -- OR-SHAPE IFF node (G1 rung 1, inc-2): rewrite-if-finish's
    -- `(if a a b) ⇒ (if a 't b)` collapse arrives `:EQUIV IFF` (the fork
    -- labels it truthfully now — p3-conj-mid-literal). Its SIff payload is
    -- lifted along the node's path by the R congruence table and MUST
    -- collapse to an eval-equality at a boolean-consumer frame before the
    -- literal root (if-test / implies positions); a root-iff literal chain
    -- is a frontier.
    if nodeEquiv n == "iff" && (runeOf n).ty == "if-simplification" then
      if let .node _ _ _ [] _ := n then
        let .cons (.atom (.symbol ifS)) (.cons a (.cons a2 (.cons bT .nil))) := lhs
          | throwError "replayRewrites: iff if-simplification lhs {repr lhs} is \
              not an if application (frontier)"
        unless ifS.name == "IF" && a == a2 do
          throwError "replayRewrites: iff if-simplification {repr lhs} is not \
              the or-shape (if a a b) (frontier)"
        let expectedRhs : SExpr := .cons (.atom (.symbol ifS))
          (.cons a (.cons quoteT (.cons bT .nil)))
        unless rhs == expectedRhs do
          throwError "replayRewrites: iff or-shape rhs {repr rhs} is not \
              (if a 't b) (frontier)"
        let rel ← relativizeAndStrip (nodePath n) depth strip
        let steps ← match pathStepsFromFrames start rel lhs with
          | .ok s => pure s
          | .error e => throwError "replayRewrites: iff or-shape :PATH does \
              not navigate to the redex: {e}"
        let ctx ← pinTermOpaques cfg cfg.envExpr ctx lhs
        let payload ← mkAppM ``evrel_siff_if_or_shape
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr a, reflectSExpr bT,
            ← ctxValExpr cfg ctx a, ← ctxValExpr cfg ctx bT,
            ← ctxValProof cfg ctx a, ← ctxValProof cfg ctx bT]
        let mut inner := payload
        let mut innerIff := true
        let mut curL := lhs
        let mut curR := rhs
        for st in steps.reverse do
          if innerIff then
            let (p, still) ← applyStepSIff cfg ctx st inner
            inner := p
            innerIff := still
          else
            inner ← applyStep cfg.worldExpr cfg.envExpr st curL curR inner
          curL := rebuild st curL
          curR := rebuild st curR
        unless curL == start do
          throwError "replayRewrites: iff or-shape lift reconstructed \
              {repr curL} ≠ running {repr start}"
        if innerIff then
          throwError "replayRewrites: or-shape iff chain still IFF at the \
              literal root (frontier — R-parameterized literal chains)"
        let (restProof, finalTerm) ← replayRewritesWith rec cfg ctx curR rest depth strip
          (chainPrefix ++ [(n, depth, strip)])
        return (some (← chainWithR cfg ctx inner curR restProof), finalTerm)
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
            (chainPrefix ++ [(n, depth, strip)])
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
                    (chainPrefix ++ [(n, depth, strip)])
                return (some (← chainWithR cfg ctx lifted newTerm restProof), finalTerm)
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
        let strip' := if rel.isEmpty then
                        strip ++ [(innermostConsumedKind (nodePath n) depth,
                                   if cv == SExpr.nil then 3 else 2)]
                      else strip
        let (restProof, finalTerm) ← replayRewritesWith rec cfg ctx newTerm rest depth strip'
          (chainPrefix ++ [(n, depth, strip)])
        return (some (← chainWithR cfg ctx lifted newTerm restProof), finalTerm)
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
              let strip' := if rel.isEmpty then
                              strip ++ [(innermostConsumedKind (nodePath n) depth,
                                         if cv == SExpr.nil then 3 else 2)]
                            else strip
              let (restProof, finalTerm) ← replayRewritesWith rec cfg ctx newTerm rest depth strip'
                (chainPrefix ++ [(n, depth, strip)])
              return (some (← chainWithR cfg ctx lifted newTerm restProof), finalTerm)
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
        let myKind := innermostConsumedKind (nodePath n) depth
        let strip' := strip ++ steps.map (fun st => (myKind, st.argIdx + 1))
        let .cons (.atom (.symbol ifS)) (.cons c (.cons thn (.cons els .nil))) := S
          | throwError "if-finish/combined: running subterm {repr S} is not a \
                        3-arg if"
        unless ifS.name == "IF" do
          throwError "if-finish/combined: running subterm head {ifS.name} ≠ if"
        -- partition the children by their WINDOW (path-emission Phase 1):
        -- branch rewrites arrive inside if-left/if-right windows
        -- (record-directed — the fork brackets rewrite-if-finish's branch
        -- descents); whole-if FINISHING steps (if1/boolean, same-branches)
        -- fire after the branch windows close, so they carry the ENCLOSING
        -- window's coordinates — their window-local path must equal the
        -- if-finish node's own (`rel`), validated fail-closed, and the walk
        -- below re-roots them at the if by PATH TRIMMING (kept ONLY here;
        -- an `if-post` window at the fork would retire it — noted for the
        -- fold-back audit).
        -- group by WINDOW IDENTITY + recorded order: a child whose window
        -- term IS the then/else branch OPENS that branch's group; following
        -- children (nested windows, post-collapse continuations) stay in
        -- the open group until the other branch's window opens. Children at
        -- the if itself (whole-if finishing steps) close the branch groups.
        -- Only the OWN branch window's tag is cleared for the sub-walk —
        -- nested window tags survive for the recursive inline handler.
        let mut thenCh : List ProofNode := []
        let mut elseCh : List ProofNode := []
        let mut postCh : List ProofNode := []
        let mut cur : Nat := 0  -- 0 = none, 1 = then, 2 = else
        for chN in children do
          if innerKindOf chN == "if-left" && innerTermOf chN == some thn then
            unless postCh.isEmpty do
              throwError "if-finish/combined: branch child after a whole-if \
                          child (frontier)"
            cur := 1
            thenCh := thenCh ++ [clearWindowTag chN]
          else if innerKindOf chN == "if-right" && innerTermOf chN == some els then
            unless postCh.isEmpty do
              throwError "if-finish/combined: branch child after a whole-if \
                          child (frontier)"
            cur := 2
            elseCh := elseCh ++ [clearWindowTag chN]
          else
            let chRel? ←
              try pure (some (← relativizeAndStrip (nodePath chN) depth strip'))
              catch _ => pure none
            if chRel? == some rel && innerKindOf chN == "" then
              cur := 0
              postCh := postCh ++ [retargetAtIf chN rel.length]
            else if cur == 1 then
              thenCh := thenCh ++ [chN]
            else if cur == 2 then
              elseCh := elseCh ++ [chN]
            else
              throwError "if-finish/combined: child {repr (nodeLhsRhs chN).1} \
                  (kind {innerKindOf chN}) precedes both branch windows and \
                  is not at the if (frontier)"
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
          let (chT, thn') ← replayRewritesWith rec cfg ctx' thn
            thenCh depth (strip' ++ [(myKind, 2)])
          let chT ← chainReqEq chT
          let prf ← match chT with
            | some p => pure p
            | none => mkIdEq thn
          pure (← mkLambdaFVars #[hNe] prf, thn')
        let (lamE, els') ← withLocalDeclD `hnil (← mkEq vC nilC) fun hNil => do
          let ctx' := { ctx with branchFacts := ctx.branchFacts ++ [(c, vC, false, hNil)] }
          let (chE, els') ← replayRewritesWith rec cfg ctx' els
            elseCh depth (strip' ++ [(myKind, 3)])
          let chE ← chainReqEq chE
          let prf ← match chE with
            | some p => pure p
            | none => mkIdEq els
          pure (← mkLambdaFVars #[hNil] prf, els')
        let target : SExpr := .cons (.atom (.symbol ifS))
          (.cons c (.cons thn' (.cons els' .nil)))
        -- OR-COLLAPSE BRIDGE (G1 rung 1, inc-2b): an IFF combined node
        -- whose then-branch is the UNREWRITTEN test's copy `A` — ACL2's
        -- rewrite-if replaced it by 'T with no recorded step (the collapse
        -- is guarded by `unrewritten-test == left`). Replay: re-compose the
        -- TEST-position prefix nodes on the then-copy (the branch-children
        -- strip pattern, `(myKind, 1)`), require the result to be the
        -- rewritten test `c`, and bridge with `evrel_siff_if_or_bridge` —
        -- the node's composite becomes IFF (p3-conj-mid-literal's flip).
        let mut bridge? : Option Expr := none
        let mut postStart := target
        if prov.equiv == "iff" && thn' != quoteT then
          if let some pc0 := postCh.head? then
            let (pcLhs, _) := nodeLhsRhs pc0
            if pcLhs == .cons (.atom (.symbol ifS))
                (.cons c (.cons quoteT (.cons els' .nil))) then
              unless thenCh.isEmpty && thn' == thn do
                throwError "if-finish/combined: or-collapse bridge with a \
                    rewritten then-branch (frontier)"
              unless rel.isEmpty do
                throwError "if-finish/combined: or-collapse bridge below the \
                    literal root (frontier — needs the mixed lift)"
              let mut testNodes : List ProofNode := []
              for (pn, pd, ps) in chainPrefix do
                -- a prefix node whose path does not relativize under THIS
                -- node's frame is at another position — a NON-MATCH, not an
                -- error (audit Q1: deliberate; a wrong selection still
                -- fails closed on the xA == c check below)
                let relPn? ← try pure (some (← relativizeAndStrip (nodePath pn) pd ps))
                  catch _ => pure none
                if let some (.arg 1 _ :: _) := relPn? then
                  testNodes := testNodes ++ [pn]
              let (chA, xA) ← replayRewritesWith rec cfg ctx thn testNodes depth
                (strip' ++ [(myKind, 1)])
              unless xA == c do
                throwError "if-finish/combined: or-collapse bridge — the \
                    re-composed test chain reached {repr xA}, the rewritten \
                    test is {repr c} (frontier)"
              let chA ← chainReqEq chA
              let hAX ← match chA with
                | some hp => pure hp
                | none => throwError "if-finish/combined: or-collapse bridge — \
                    empty test chain but then-copy {repr thn} ≠ test {repr c}"
              bridge? := some (← mkAppM ``evrel_siff_if_or_bridge
                #[cfg.worldExpr, cfg.envExpr, reflectSExpr c, reflectSExpr thn,
                  reflectSExpr els', vC, ← ctxValExpr cfg ctx els',
                  hAX, pC, ← ctxValProof cfg ctx els'])
              postStart := .cons (.atom (.symbol ifS))
                (.cons c (.cons quoteT (.cons els' .nil)))
        -- whole-if finishing steps apply AFTER the branch congruence, on the
        -- rebuilt if
        let (postOpt, final) ← replayRewritesWith rec cfg ctx postStart postCh depth strip'
        let postOpt ← chainReqEq postOpt
        -- the JOINT may need SWAPPED-P normalizations the children created
        -- (a NOT unfold inside a test position swaps the enclosing if,
        -- unrecorded — ORDEREDP-MEMB)
        let (swapOpt, final) ← normalizeSwapsToward cfg final rhs
        -- rewrite-equal's UNRECORDED nil-normalization inside a branch
        -- (`bridgeEqualNilNormDeep`) — same joint treatment as the swaps
        let (nilNormOpt, final) ← do
          if final != rhs then
            match ← bridgeEqualNilNormDeep cfg ctx final rhs with
            | some h => pure ((some h : Option Expr), rhs)
            | none => pure ((none : Option Expr), final)
          else pure ((none : Option Expr), final)
        unless final == rhs do
          throwError "if-finish/combined: children chains reached {repr final}, \
                      node rhs is {repr rhs}"
        if let some br := bridge? then
          -- the bridged composite S →eq target →SIFF postStart →eq final
          -- (rel = []): inject the eq parts into the SIff lane and transit;
          -- the node's chain contribution is IFF (consumed at the literal
          -- boundary by the spine's test-position collapse)
          let mut comp := br
          if target != S then
            let eqB ← mkAppM ``evalOpt_congr_if_branches_cond
              #[w, e, reflectSExpr c, reflectSExpr thn, reflectSExpr els,
                reflectSExpr thn', reflectSExpr els', vC, pC, lamT, lamE]
            let eqBS ← mkAppM ``evrel_of_fuel_eq
              #[mkConst ``siff_refl, eqB, ← ctxValProof cfg ctx target]
            comp ← mkAppM ``evrel_trans #[mkConst ``siff_trans, eqBS, comp]
          let mut postParts : List Expr := []
          if let some p := postOpt then postParts := postParts ++ [p]
          if let some p := swapOpt then postParts := postParts ++ [p]
          if let some p := nilNormOpt then postParts := postParts ++ [p]
          unless postParts.isEmpty do
            let postEq ← chainEqs postParts
            let postS ← mkAppM ``evrel_of_fuel_eq
              #[mkConst ``siff_refl, postEq, ← ctxValProof cfg ctx final]
            comp ← mkAppM ``evrel_trans #[mkConst ``siff_trans, comp, postS]
          let (restProof, finalTerm) ← replayRewritesWith rec cfg ctx final rest depth strip
            (chainPrefix ++ [(n, depth, strip)])
          return (some (← chainIffWithR cfg ctx comp finalTerm restProof), finalTerm)
        let mut proofs : List Expr := []
        if target != S then
          proofs := proofs ++ [← mkAppM ``evalOpt_congr_if_branches_cond
            #[w, e, reflectSExpr c, reflectSExpr thn, reflectSExpr els,
              reflectSExpr thn', reflectSExpr els', vC, pC, lamT, lamE]]
        if let some p := postOpt then
          proofs := proofs ++ [p]
        if let some p := swapOpt then
          proofs := proofs ++ [p]
        if let some p := nilNormOpt then
          proofs := proofs ++ [p]
        if proofs.isEmpty then
          -- no effective rewrites: a no-op summary node
          unless S == rhs do
            throwError "if-finish/combined: no effective children but running \
                        subterm {repr S} ≠ rhs {repr rhs}"
          return ← replayRewritesWith rec cfg ctx start rest depth strip
            (chainPrefix ++ [(n, depth, strip)])
        let nodeProof ← chainEqs proofs
        let (lifted, newTerm) ←
          emitCongruence w e start (nodePath n) S final nodeProof depth strip
        let (restProof, finalTerm) ← replayRewritesWith rec cfg ctx newTerm rest depth strip
          (chainPrefix ++ [(n, depth, strip)])
        return (some (← chainWithR cfg ctx lifted newTerm restProof), finalTerm)
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
                -- (litFactByTerm? itself already falls through to segFacts —
                -- the *1.5/2.1 segment fact resolves through it; audit F1
                -- removed a dead third arm that re-searched segFacts)
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
                      -- equality sources: clausify-branch segment facts AND
                      -- clause-literal falsity facts of the same
                      -- `(not (equal p q))` shape (G2 rung 2: the hoisted
                      -- (NOT (EQUAL X1 (CAR X-EQUIV))) literal's falsity
                      -- pins vX1 = v(CAR X-EQUIV) at *1.5/2.1)
                      let eqSources : List (SExpr × Expr) :=
                        ctx.segFacts ++ ctx.litFacts.map (fun (_, l, h) => (l, h))
                      for (st, hSeg) in eqSources do
                        if found.isSome then break
                        let .cons (.atom (.symbol ns))
                            (.cons pq@(.cons (.atom (.symbol eqS'))
                              (.cons p (.cons q .nil))) .nil) := st
                          | continue
                        unless ns.name == "NOT" && eqS'.name == "EQUAL" do
                          continue
                        -- heq : vp = vq from the false segment literal
                        let vPQ ← ctxValExpr cfg ctx pq
                        -- TYPE-CHECKED (audit F8, the litFactByTermChecked?
                        -- discipline): a fact whose proof lives in ANOTHER
                        -- env context (pool-root/elim crossings) or whose
                        -- opaque pins drifted is SKIPPED, not crashed on
                        let expectedTy ← mkEq
                          (mkApp (mkConst ``Logic.not) vPQ)
                          (mkConst ``SExpr.nil)
                        unless ← isDefEq (← inferType hSeg) expectedTy do
                          continue
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
                                (rewriting {repr start}; \
                                lit-facts {repr (ctx.litFacts.map (·.2.1))}; \
                                seg-facts {repr (ctx.segFacts.map (·.1))}) \
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
                  curL := rebuild st curL
                  curR := rebuild st curR
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
      let (restAll, finalT) ← replayRewritesWith rec cfg ctx start' (n :: rest) depth strip chainPrefix
      return (some (← chainWithR cfg ctx testChain start' restAll), finalT)
    -- REWRITE-EQUAL cons-decomposition (sorting-completion-2, ORDERED-PERMS
    -- Subgoal *1/7'5' literal 10, both polarities): ACL2's rewrite-equal on
    -- (EQUAL s1 s2) rewrites the SYNTHESIZED components
    -- (rewrite-args '((car lhs) (car rhs)) — gstack bkptr 1/2, so the path
    -- frames name redexes that are NOT literal subterms), decides each
    -- component equality (a recorded node at the EQUAL's own path, or a
    -- SILENT type-alist refutation), then — cars equal — repeats for the
    -- cdrs. Verdicts: any component refuted ⇒ 'NIL
    -- (`logic_equal_nil_of_{car,cdr}_components`); both phases equal ⇒ 'T by
    -- cons-extensionality with consp evidence for BOTH sides
    -- (`logic_equal_t_of_components`). Detected at the FIRST scratch step;
    -- the whole remaining chain is the protocol — anything off-shape
    -- hard-fails.
    if (runeOf n).ty != "clause-context-resolution" then
      if let .cons (.atom (.symbol eqS)) (.cons s1 (.cons s2 .nil)) := start then
        if eqS.name == "EQUAL" then
          -- window-tagged detection (path-emission Phase 1): the fork
          -- brackets the component descents in equal-cars/equal-cdrs
          -- windows carrying BOTH synthesized redexes — no shape guessing.
          -- (cdrs-first arises when the cars phase decided with no scratch
          -- rewrite — its window is empty and unseen here.)
          if innerKindOf n == "equal-cars" || innerKindOf n == "equal-cdrs" then do
            if true then
              let mut ctx ← pinTermOpaques cfg cfg.envExpr ctx start
              let vs1 ← ctxValExpr cfg ctx s1
              let vs2 ← ctxValExpr cfg ctx s2
              let mut nodesLeft : List ProofNode := n :: rest
              -- verdict accumulator: none = still deciding; some hEq = the
              -- final `Logic.equal vs1 vs2 = <const>` fact + the constant
              let mut verdict : Option (Expr × SExpr) := none
              let mut phaseComps : List Expr := []  -- car-, then cdr-phase
              for pfn in ["CAR", "CDR"] do
                if verdict.isSome then continue
                let mut c1 : SExpr := .cons (.atom (.symbol { name := pfn }))
                  (.cons s1 .nil)
                let mut c2 : SExpr := .cons (.atom (.symbol { name := pfn }))
                  (.cons s2 .nil)
                ctx ← pinTermOpaques cfg cfg.envExpr ctx c1
                ctx ← pinTermOpaques cfg cfg.envExpr ctx c2
                let mut h1 ← mkEqRefl (← ctxValExpr cfg ctx c1)
                let mut h2 ← mkEqRefl (← ctxValExpr cfg ctx c2)
                -- consume this phase's scratch rewrites (either side, any
                -- interleaving; each is a full node replayed by its own
                -- recipe)
                let mut scanning := true
                while scanning do
                  match nodesLeft with
                  | [] => scanning := false
                  | n' :: r' =>
                    let (l', r'') := nodeLhsRhs n'
                    let phaseKind := if pfn == "CAR" then "equal-cars"
                                     else "equal-cdrs"
                    let side? : Option Nat :=
                      if innerKindOf n' == phaseKind then
                        match nodePath n' with
                        | .arg k _ :: _ => some k
                        | _ => none
                      else none
                    match side? with
                    | some 1 =>
                      if l' == c1 then
                        let e ← rec.node cfg ctx n' depth
                        ctx ← pinTermOpaques cfg cfg.envExpr ctx r''
                        let ve ← mkAppM ``val_eq_of_eval_eq
                          #[e, ← ctxValProof cfg ctx c1,
                            ← ctxValProof cfg ctx r'']
                        h1 ← mkAppM ``Eq.trans #[h1, ve]
                        c1 := r''; nodesLeft := r'
                      else scanning := false
                    | some 2 =>
                      if l' == c2 then
                        let e ← rec.node cfg ctx n' depth
                        ctx ← pinTermOpaques cfg cfg.envExpr ctx r''
                        let ve ← mkAppM ``val_eq_of_eval_eq
                          #[e, ← ctxValProof cfg ctx c2,
                            ← ctxValProof cfg ctx r'']
                        h2 ← mkAppM ``Eq.trans #[h2, ve]
                        c2 := r''; nodesLeft := r'
                      else scanning := false
                    | _ => scanning := false
                -- the phase decision: a recorded (EQUAL c1 c2) node at the
                -- EQUAL's own path, or a silent type-alist refutation
                let decT : SExpr := .cons (.atom (.symbol { name := "EQUAL" }))
                  (.cons c1 (.cons c2 .nil))
                let dec? ← match nodesLeft with
                  | n' :: r' => do
                    let (l', rr') := nodeLhsRhs n'
                    if l' == decT && (← relativizeAndStrip (nodePath n') depth strip) == [] then
                      pure (some (n', rr', r'))
                    else pure none
                  | [] => pure none
                match dec? with
                | some (n', rr', r') =>
                  nodesLeft := r'
                  let e ← rec.node cfg ctx n' depth
                  ctx ← pinTermOpaques cfg cfg.envExpr ctx decT
                  let vDec ← ctxValExpr cfg ctx decT
                  if rr' == quoteT then
                    let vq ← mkAppM ``re_val_quote
                      #[cfg.worldExpr, cfg.envExpr, reflectSExpr SExpr.t]
                    let ve ← mkAppM ``val_eq_of_eval_eq
                      #[e, ← ctxValProof cfg ctx decT, vq]
                    -- vDec = t → vc1 = vc2 → component equality
                    let _ := vDec
                    let hc ← mkAppM ``logic_eq_of_equal_t #[ve]
                    let hcomp ← mkAppM ``Eq.trans
                      #[h1, ← mkAppM ``Eq.trans #[hc, ← mkAppM ``Eq.symm #[h2]]]
                    phaseComps := phaseComps ++ [hcomp]
                  else if rr' == quoteNil then
                    let vq ← mkAppM ``re_val_quote
                      #[cfg.worldExpr, cfg.envExpr, reflectSExpr SExpr.nil]
                    let ve ← mkAppM ``val_eq_of_eval_eq
                      #[e, ← ctxValProof cfg ctx decT, vq]
                    let lem := if pfn == "CAR" then
                      ``logic_equal_nil_of_car_components
                      else ``logic_equal_nil_of_cdr_components
                    verdict := some (← mkAppM lem #[h1, h2, ve], SExpr.nil)
                  else
                    throwError "replayRewrites: rewrite-equal {pfn} decision \
                        node {repr decT} ⇒ {repr rr'} is not a constant \
                        verdict (frontier)"
                | none =>
                  -- silent refutation from the in-scope context (the same
                  -- facts ACL2's type-set consulted)
                  let decFlip : SExpr := .cons (.atom (.symbol { name := "EQUAL" }))
                    (.cons c2 (.cons c1 .nil))
                  ctx ← pinTermOpaques cfg cfg.envExpr ctx decT
                  let hRef ← do
                    match ← deriveNilFact cfg ctx decT with
                    | some h => pure h
                    | none =>
                      match ← deriveNilFact cfg ctx decFlip with
                      | some h => mkAppM ``logic_equal_nil_comm #[h]
                      | none =>
                        throwError "replayRewrites: rewrite-equal {pfn} \
                            phase — no recorded decision and no in-scope \
                            refutation of {repr decT} (frontier)"
                  let lem := if pfn == "CAR" then
                    ``logic_equal_nil_of_car_components
                    else ``logic_equal_nil_of_cdr_components
                  verdict := some (← mkAppM lem #[h1, h2, hRef], SExpr.nil)
              let (hEq, cst) ← do
                match verdict with
                | some (h, c) => pure (h, c)
                | none => do
                  -- both phases component-equal: 'T by cons-extensionality;
                  -- consp evidence for BOTH sides from value shape/context
                  let [hcompCar, hcompCdr] := phaseComps
                    | throwError "replayRewrites: rewrite-equal decomposition \
                        finished with {phaseComps.length} component proofs \
                        (internal)"
                  let some hca ← conspEvidence? ctx s1 vs1
                    | throwError "replayRewrites: rewrite-equal — no consp \
                        evidence for {repr s1} (frontier)"
                  let some hcb ← conspEvidence? ctx s2 vs2
                    | throwError "replayRewrites: rewrite-equal — no consp \
                        evidence for {repr s2} (frontier)"
                  pure (← mkAppM ``logic_equal_t_of_components
                    #[hca, hcb, hcompCar, hcompCdr], SExpr.t)
              unless nodesLeft.isEmpty do
                throwError "replayRewrites: rewrite-equal decomposition left \
                    unconsumed nodes \
                    {repr (nodesLeft.map (fun m => (nodeLhsRhs m).1))} \
                    (frontier)"
              let pl ← ctxValProof cfg ctx start
              let pr ← mkAppM ``re_val_quote
                #[cfg.worldExpr, cfg.envExpr, reflectSExpr cst]
              let step ← mkAppM ``fuel_eq_of_conv #[pl, pr, hEq]
              let resT : SExpr := .cons (.atom (.symbol { name := "QUOTE" }))
                (.cons cst .nil)
              return (some (step, false), resT)
    let nodeEq ← rec.node cfg ctx n depth
    let (lifted, newTerm) ←
      try
        emitCongruence cfg.worldExpr cfg.envExpr start (nodePath n) lhs rhs nodeEq depth strip
      catch ex =>
        let nch : String := toString (match n with | .node _ _ _ ch _ => ch.length)
        throwError "generic-tail lift for {(runeOf n).ty}/{nodeOrigin n} \
          (kind {innerKindOf n}, {nch} children): {ex.toMessageData}"
    -- an if-simplification AT THE CHAIN ROOT selects a branch; ACL2's rewrite-if
    -- keeps the if on the gstack while rewriting inside that branch, so the
    -- remaining nodes' paths carry the branch frame — record it for stripping.
    let strip' ←
      -- BRANCH-SELECTING root if-simplifications only: an `if1/boolean`
      -- collapse replaces the if by its (boolean) test — no branch frame
      -- remains on the gstack, so nothing to strip.
      if (runeOf n).ty == "if-simplification" && lhs == start &&
         (nodeOrigin n) != "if1/boolean" then
        let myKind := innermostConsumedKind (nodePath n) depth
        match lhs with
        | .cons _ (.cons _ (.cons thn (.cons els .nil))) =>
          if rhs == thn then pure (strip ++ [(myKind, 2)])
          else if rhs == els then pure (strip ++ [(myKind, 3)])
          else throwError "replayRewrites: root if-simplification rhs is neither branch"
        | _ => throwError "replayRewrites: root if-simplification lhs not a 3-arg if"
      else pure strip
    let (restProof, finalTerm) ← replayRewritesWith rec cfg ctx newTerm rest depth strip'
      (chainPrefix ++ [(n, depth, strip)])
    return (some (← chainWithR cfg ctx lifted newTerm restProof), finalTerm)

/- The tied node-level knot — the ONLY remaining mutual at this layer.
   Public names/signatures identical to the pre-WP2 mutual members. -/
mutual

partial def replayNode (cfg : ReplayConfig) (ctx : ReplayCtx) (n : ProofNode)
    (depth : Nat := 0) : MetaM Expr :=
  replayNodeWith ⟨fun c x n' d => replayNode c x n' d,
                  fun c x s ns d st => replayRewrites c x s ns d st⟩ cfg ctx n depth

partial def replayRewrites (cfg : ReplayConfig) (ctx : ReplayCtx) (start : SExpr) :
    List ProofNode → (depth : Nat := 0) → (strip : List (Option String × Nat) := []) →
    MetaM (Option (Expr × Bool) × SExpr) :=
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
    : MetaM (Option (Expr × Bool) × SExpr) := do
  if lp.notFlg then
    let .cons (.atom (.symbol notS)) (.cons atm .nil) := lp.literal
      | throwError "replayLiteralChain: notFlg literal is not (not atm): {repr lp.literal}"
    unless notS.name == "NOT" do
      throwError "replayLiteralChain: notFlg literal head {notS.name} ≠ not"
    let (chainOpt, finalAtom) ← replayRewrites cfg ctx atm lp.nodes 0
    let chainOpt ← chainReqEq chainOpt
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
        return (some (chain, false), foldedT)
      else
        return (lifted.map ((·, false)), finalLit)
    | _ => return (lifted.map ((·, false)), finalLit)
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
    let chainOpt ← chainReqEq chainOpt
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
  let chainOpt ← chainReqEq chainOpt
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

/-- A clause-context falsity demand: either an exact clause-literal TERM, or
    a clause-literal INDEX (solidify nodes name their source literal by index,
    not by term). -/
inductive ContextDemand where
  | term (t : SExpr)
  | litIdx (k : Nat)
  /-- The clause's equality literals CONNECTED to `{a, b}` (the solidify
      node's `:EQUIV-TERM` sides) are all demanded — the transitive
      type-alist equivalence needs the whole component in scope. -/
  | equivClass (a b : SExpr)
  /-- A later literal of shape `(NOT (TRUE-LISTP (CONS a w)))` for the
      recognizer's inner term `w` (any car `a`): ACL2's type-set closure
      justifies `(TRUE-LISTP w) ⇒ 'T` from that literal's falsity —
      `trueListp (cons a w)` reduces to `trueListp w` (sorting-completion-2
      Class A, ORDERED-PERMS Subgoal *1/7'5' literal 1 after the
      branch-substitutions). Pattern demand — the car is not knowable at
      demand-collection time. -/
  | tlpCons (w : SExpr)
  deriving BEq

/-- Every IF-test subterm of `t`, recursively (never descending QUOTE):
    candidates for clause-context demands — an if-test the rewriter resolved
    against the type-alist with NO emitted node (the reconciled constant-test
    class in `replayRewritesWith`) consumes a clause literal's falsity, and
    the test appears as an if-test inside the chain's own lhs/rhs terms
    (G2 rung 2: qsort's PERM-IMPLIES-EQUAL-ALL-REL-2 opens REL's FN-dispatch
    body whose tests are the clause's own `(EQUAL FN 'LT/'LTE)` literals). -/
partial def ifTestsOf : SExpr → List SExpr
  | .cons (.atom (.symbol f)) args =>
    if f.name == "QUOTE" then []
    else
      let rec argsOf : SExpr → List SExpr
        | .cons a rest => ifTestsOf a ++ argsOf rest
        | _ => []
      (if f.name == "IF" then
         match args with
         | .cons t _ =>
           match t with
           | .cons (.atom (.symbol q)) _ =>
             if q.name == "QUOTE" then [] else [t]
           | .atom _ => [t]
           | _ => [t]
         | _ => []
       else []) ++ argsOf args
  | _ => []

/-- A `.term` falsity demand plus its EQUAL-flip (the hoist site matches
    clause-literal terms exactly; type-alist lookups go through `equal`'s
    commutativity, so both orientations are demanded). -/
def ifTestDemandsOf (t : SExpr) : List ContextDemand :=
  [ContextDemand.term t] ++
  (match t with
   | .cons (.atom (.symbol es)) (.cons u (.cons v .nil)) =>
     if es.name == "EQUAL" then
       [ContextDemand.term
         (.cons (.atom (.symbol es)) (.cons v (.cons u .nil)))]
     else []
   | _ => [])

/-- Every `(CDR u)` subterm of `t` (never descending QUOTE) — the CONSP
    closure's ingredient scan. -/
partial def cdrSubterms : SExpr → List SExpr
  | t@(.cons (.atom (.symbol f)) args) =>
    if f.name == "QUOTE" then []
    else
      let rec argsOf : SExpr → List SExpr
        | .cons a rest => cdrSubterms a ++ argsOf rest
        | _ => []
      (if f.name == "CDR" then [t] else []) ++ argsOf args
  | _ => []

/-- The CLAUSE-CONTEXT falsity demands of a literal's chain, as the exact
    clause-literal terms/indices whose falsity the chain's nodes consume
    (ACL2 rewrites literal i under the falsity of ALL other clause literals):
    - a silent hyp-relief marker for hyp `h` demands `(not h)`;
    - a `type-alist` nil-verdict node `l ⇒ 'nil` demands `l` itself;
    - a `type-alist` truthy node `l ⇒ 't` demands `(not l)`;
    - a solidify node with a `.literal k` equiv source demands literal `k`
      (S1 2026-07-23 — the IH equation consumed from a LATER literal);
    - every IF-test subterm of a node's lhs/rhs (and its EQUAL-flip) — the
      reconciled constant-test class resolves such a test from the clause
      context with no emitted node (G2 rung 2). A demand that is no later
      clause literal is skipped harmlessly at the hoist site. -/
partial def collectContextDemands : ProofNode → List ContextDemand
  | .node ⟨rty, _, _⟩ l rh children prov =>
    let notOf : SExpr → SExpr := fun t =>
      .cons (.atom (.symbol { name := "NOT" })) (.cons t .nil)
    let ifTestDemands : List ContextDemand :=
      (ifTestsOf l ++ ifTestsOf rh).flatMap ifTestDemandsOf
    (if rty == "hyp-relief" then
       [ContextDemand.term (notOf l)] ++
       -- a (NOT atom) hyp's clause-context source is the ATOM literal — its
       -- falsity IS the hyp's truth (the complement orientation the marker
       -- consumer's route already reads; DEFAULT-CDR's (NOT (CONSP (CDR X)))
       -- hyp at HOW-MANY-EVENS-AND-ODDS, S1 2026-07-23). Demand the atom too
       -- so the walk hoists it when it sits later in the clause; a demand
       -- that is no clause literal is skipped harmlessly at the hoist site.
       (match l with
        | .cons (.atom (.symbol ns)) (.cons atm .nil) =>
          if ns.name == "NOT" then [ContextDemand.term atm] else []
        | _ => []) ++
       -- an FC-DERIVED relief (the LEXORDER-TOTAL registry, marker :TA-RUNES)
       -- consumes the COMMUTED lexorder application's falsity — demand that
       -- literal too so the walk hoists it when it sits later in the clause
       -- (HOW-MANY-FILTER-1)
       (match l with
        | .cons (.atom (.symbol ls)) (.cons u (.cons v .nil)) =>
          if ls.name == "LEXORDER" && prov.taRunes.any
              (fun r => r.ty == "forward-chaining" && r.name == "LEXORDER-TOTAL")
          then [ContextDemand.term (.cons (.atom (.symbol ls)) (.cons v (.cons u .nil)))]
          else []
        | _ => [])
     else if rty == "type-alist" then
       if rh == quoteNil then
         [ContextDemand.term l] ++
         -- the nil-verdict closure's TRUE-LISTP∧¬CONSP ingredient: the
         -- truthy true-listp fact may sit in a LATER literal
         -- (ORDERED-PERMS *1/7'5' literal 5: `B ⇒ 'NIL` from segment
         -- (CONSP B)-false + later literal 9 (NOT (TRUE-LISTP B)))
         [ContextDemand.term (notOf
           (.cons (.atom (.symbol { name := "TRUE-LISTP" })) (.cons l .nil)))]
       else if rh == quoteT then [ContextDemand.term (notOf l)]
       else []
     else if rty == "rewriting-equivalence" then
       -- a solidify node consumes its source literal's falsity BY INDEX; a
       -- transitive equivalence (S1 2026-07-23) additionally needs the whole
       -- connected component of its :EQUIV-TERM sides in scope
       (match prov.equivSource with
        | some (.literal k) => [ContextDemand.litIdx k]
        | _ => []) ++
       (match prov.equivTerm with
        | some (.cons (.atom (.symbol es)) (.cons a (.cons b .nil))) =>
          if es.name == "EQUAL" then [ContextDemand.equivClass a b] else []
        | _ => [])
     else if prov.origin == "recognizer/true" then
       -- a recognizer resolved TRUE from the clause context (a later
       -- literal is its negation — EQUAL-CONS Subgoal 4); hoisting is a
       -- no-op when the fact is derivable another way
       [ContextDemand.term (notOf l)] ++
       -- the TRUE-LISTP type-set-closure justifications: a later
       -- `(NOT (TRUE-LISTP (CONS a w)))` literal (see `tlpCons`), and — for
       -- the (TRUE-LISTP (CDR u)) shape — the closure arm's DIRECT
       -- ingredient `(NOT (TRUE-LISTP u))` (ORDERED-PERMS: literal 9's
       -- (NOT (TRUE-LISTP B)) justifies (TRUE-LISTP (CDR B)) ⇒ 'T)
       (match l with
        | .cons (.atom (.symbol rs)) (.cons w .nil) =>
          if rs.name == "TRUE-LISTP" then
            [ContextDemand.tlpCons w] ++
            (match w with
             | .cons (.atom (.symbol fs)) (.cons u .nil) =>
               if fs.name == "CDR" then
                 [ContextDemand.term (notOf
                   (.cons (.atom (.symbol { name := "TRUE-LISTP" }))
                     (.cons u .nil)))]
               else []
             | _ => [])
          else if rs.name == "CONSP" then
            -- the CONSP-closure ingredients (ORDERED-PERMS *1/2.2 and the
            -- IF-split shapes): for EVERY (CDR u) subterm of w, the truthy
            -- (CDR u) / (TRUE-LISTP u) / (TRUE-LISTP (CDR u)) literals
            ((cdrSubterms w).flatMap fun cu =>
              match cu with
              | .cons _ (.cons u .nil) =>
                [ContextDemand.term (notOf cu),
                 ContextDemand.term (notOf
                   (.cons (.atom (.symbol { name := "TRUE-LISTP" }))
                     (.cons u .nil))),
                 ContextDemand.term (notOf
                   (.cons (.atom (.symbol { name := "TRUE-LISTP" }))
                     (.cons cu .nil)))]
              | _ => []) ++
            -- the conspEvidence? truthy-(CDR w) route on the inner term
            -- itself ((CONSP B) with a later (NOT (CDR B)) literal), and the
            -- general truthy+proper-list route's TRUE-LISTP ingredient
            [ContextDemand.term (notOf
              (.cons (.atom (.symbol { name := "CDR" })) (.cons w .nil))),
             ContextDemand.term (notOf
              (.cons (.atom (.symbol { name := "TRUE-LISTP" }))
                (.cons w .nil)))]
          else []
        | _ => [])
     else if prov.origin == "recognizer/false" then [ContextDemand.term l]
     else []) ++ ifTestDemands ++ children.flatMap collectContextDemands

/-- WORLD-AWARE demand augmentation: a DEFINITION node's unfolded body (read
    from the world's defun, formals substituted by the recorded call args)
    contributes its if-tests as falsity demands. The recorded rhs shows
    ACL2's POST-resolution view (a context-resolved test appears there as
    the quoted verdict), so a test the reconciled constant-test class must
    resolve appears ONLY in the world-side body — invisible to
    `collectContextDemands` (G2 rung 2: REL's FN-dispatch body whose tests
    are the clause's own `(EQUAL FN 'LT/'LTE)` literals). -/
partial def collectDefBodyDemands (cfg : ReplayConfig) : ProofNode → List ContextDemand
  | .node ⟨rty, _, _⟩ l _ children _ =>
    (if rty == "definition" then
       match l with
       | .cons (.atom (.symbol fn)) args =>
         match cfg.worldVal.defs.get? fn, args.toList? with
         | some (formals, body), some argL =>
           if formals.length == argL.length then
             (ifTestsOf (ACL2.Replay.substTerm formals argL body)).flatMap
               ifTestDemandsOf
           else []
         | _, _ => []
       | _ => []
     else []) ++ children.flatMap (collectDefBodyDemands cfg)

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

/-- Close `EvTrue (disjoin lits)` for a TAUTOLOGOUS clause — one containing a
    complementary pair `L` / `(NOT L)`, or the COMMUTED-EQUAL pair
    `(EQUAL a b)` / `(NOT (EQUAL b a))` (ACL2's type-set treats the commuted
    equality as the same type-alist entry — p7's SAME-LN sym conjunct) — by
    cases on the negated literal's atom value. ACL2 recognizes such a clause
    as *t* with no recorded steps (add-literal and
    remove-trivial-equivalences drop it as proved silently), so the mirror is
    the pair's excluded middle. Fails loudly when no pair exists. `who` names
    the calling site in the error. -/
def tautClauseClose (cfg : ReplayConfig) (ctx : ReplayCtx) (lits : List SExpr)
    (who : String) : MetaM Expr := do
  let notOf (t : SExpr) : SExpr :=
    .cons (.atom (.symbol { name := "NOT" })) (.cons t .nil)
  let commuteEq? : SExpr → Option SExpr := fun t =>
    match t with
    | .cons (.atom (.symbol eqS)) (.cons a (.cons b .nil)) =>
      if eqS.name == "EQUAL" then
        some (.cons (.atom (.symbol eqS)) (.cons b (.cons a .nil)))
      else none
    | _ => none
  -- (positive index, negated index, positive atom, negated atom): the
  -- negated literal is (NOT negAtom) with negAtom == atom (direct) or the
  -- commuted equality
  let pair? : Option (Nat × Nat × SExpr × SExpr) :=
    lits.zipIdx.findSome? fun (l, i) =>
      lits.zipIdx.findSome? fun (l2, j) =>
        if l2 == notOf l then some (i, j, l, l)
        else match commuteEq? l with
          | some lC => if l2 == notOf lC then some (i, j, l, lC) else none
          | none => none
  let some (iPos, iNeg, atom, negAtom) := pair?
    | throwError "{who}: tautology close — no complementary literal pair in \
        {repr lits} (frontier)"
  let ctxT ← pinTermOpaques cfg cfg.envExpr ctx (disjoinTerm lits)
  let vN ← ctxValExpr cfg ctxT negAtom
  let nilC := mkConst ``SExpr.nil
  let tNeNil ← proveByDecide
    (← mkAppM ``Ne #[mkConst ``SExpr.t, nilC]) "t ≠ nil"
  let posL ← withLocalDeclD `hne (← mkAppM ``Ne #[vN, nilC]) fun hNe => do
    let p ←
      if negAtom == atom then
        evtrueOfLitTrue cfg ctxT lits iPos atom hNe
      else do
        -- commuted pair: v(EQUAL b a) ≠ nil gives vb = va, so
        -- v(EQUAL a b) = Logic.equal va vb = Logic.equal va va = t
        unless vN.isAppOfArity ``Logic.equal 2 do
          throwError "{who}: commuted-equal value of {repr negAtom} is not \
              (Logic.equal _ _) (internal)"
        let vb := vN.appFn!.appArg!
        let va := vN.appArg!
        let hEq ← mkAppM ``Logic.eq_of_equal_ne_nil #[hNe]  -- vb = va
        let vA ← ctxValExpr cfg ctxT atom  -- Logic.equal va vb
        unless vA.isAppOfArity ``Logic.equal 2 do
          throwError "{who}: value of {repr atom} is not (Logic.equal _ _) \
              (internal)"
        let fL ← withLocalDeclD `z (mkConst ``SExpr) fun zV => do
          mkLambdaFVars #[zV] (← mkAppM ``Logic.equal #[va, zV])
        -- vA = Logic.equal va vb = Logic.equal va va (by vb = va) = t
        let hStep ← mkAppM ``congrArg #[fL, hEq]  -- equal va vb = equal va va
        let hSelf ← mkAppM ``Logic.equal_self #[va]
        let hT ← mkAppM ``Eq.trans #[hStep, hSelf]  -- vA = t
        let hATrue ← mkAppM ``ne_of_eq_of_ne #[hT, tNeNil]
        let _ := vb
        evtrueOfLitTrue cfg ctxT lits iPos atom hATrue
    mkLambdaFVars #[hNe] p
  let negL ← withLocalDeclD `hnil (← mkEq vN nilC) fun hNil => do
    let hT ← mkAppM ``logic_not_t_of_nil #[hNil]
    let hTrue ← mkAppM ``ne_of_eq_of_ne #[hT, tNeNil]
    mkLambdaFVars #[hNil]
      (← evtrueOfLitTrue cfg ctxT lits iNeg (notOf negAtom) hTrue)
  mkAppM ``Classical.byCases #[negL, posL]

end ACL2.Replay.Driver
