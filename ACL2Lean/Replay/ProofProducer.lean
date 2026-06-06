/-
  Proof-producing checker for ACL2 proof trees.

  Walks the parsed proof tree and constructs Lean proof terms (Expr)
  for each node. Mirrors the Bool checker (ProofChecker.lean) but
  returns proofs instead of booleans.

  Architecture:
  - Reflection layer: SExpr → Lean Expr
  - Side condition provers: decide (symbol checks), simp (HashMap lookups)
  - Node provers: one per rune type, applies the corresponding EvalLemma
  - Composition: T1 (congruence) + T16 (chain) compose node proofs
-/
import ACL2Lean.Replay.EvalLemmas
import ACL2Lean.ProofTree
import Lean

namespace ACL2.Replay.ProofProducer

open ACL2 ACL2.Replay Lean Elab Meta

/-! ## Totality / type-prescription synthesis (1-arg structural recursion)

  ACL2 proves termination and type-prescription before admitting a recursive
  function; the proof replay needs that fact (recursive calls converge to an
  integer) to discharge a recursive branch. For the restricted-but-real shape

      (defun fn (formal)
        (if (consp formal)
            (binary-+ 'step (fn (cdr formal)))
            'base))

  — 1-arg structural recursion on the single formal, recursing only as
  `(fn (cdr formal))`, integer-valued — totality is a fixed induction proof
  (induction on `acl2Count` via `acl2_induction_consp`), parameterized by the
  function-specific data. `totality1_generic` IS that proof; `synthTotality1`
  detects the shape from a function's body and instantiates it. No hardcoded
  function/formal names; hard-fail (throwError) at the frontier. -/

/-- Generic totality + type-prescription for a 1-arg structurally-recursive
    function `fn` whose body is `(IF (CONSP formal) (BINARY-+ 'step (fn (CDR
    formal))) 'base)`. Applied to any value, the body converges to an integer.

    This is the generalization of `SimpleWorld.my_len_total`: the SAME proof
    skeleton works for an arbitrary such function once `fn`, `formal`, `step`,
    `base`, and `body` are supplied. `synthTotality1` instantiates it. -/
theorem totality1_generic (w : World) (fnSym formal : Symbol) (base step : Int)
    (body : SExpr)
    (hbody : body =
      .cons (.atom (.symbol { name := "if" }))
        (.cons (.cons (.atom (.symbol { name := "consp" }))
                 (.cons (.atom (.symbol formal)) .nil))
          (.cons (.cons (.atom (.symbol { name := "binary-+" }))
                   (.cons (.cons (.atom (.symbol { name := "quote" }))
                            (.cons (.atom (.number (.int step))) .nil))
                     (.cons (.cons (.atom (.symbol fnSym))
                              (.cons (.cons (.atom (.symbol { name := "cdr" }))
                                       (.cons (.atom (.symbol formal)) .nil)) .nil)) .nil)))
            (.cons (.cons (.atom (.symbol { name := "quote" }))
                     (.cons (.atom (.number (.int base))) .nil)) .nil))))
    (h_fn : w.defs[fnSym]? = some ([formal], body))
    (h_no_consp : w.defs[({ name := "consp" } : Symbol)]? = none)
    (h_no_cdr : w.defs[({ name := "cdr" } : Symbol)]? = none)
    (h_no_plus : w.defs[({ name := "binary-+" } : Symbol)]? = none)
    (h_fn_ns : fnSym.isNamed "quote" = false ∧ fnSym.isNamed "if" = false ∧
               fnSym.isNamed "let" = false ∧ fnSym.isNamed "let*" = false) :
    ∀ val : SExpr, ∃ k : Int, ∃ N, ∀ f ≥ N,
      evalOpt f w (bindArgs [formal] [val]) body
        = some (.atom (.number (.int k))) := by
  apply acl2_induction_consp
  · -- BASE: consp val = nil → body takes else-branch → base
    intro val hconsp
    have hxlook : (bindArgs [formal] [val]).get? formal = some val := by
      show (bindArgs [formal] [val])[formal]? = some val
      simp [bindArgs]
    refine ⟨base, 4, fun f hf => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 4 := ⟨f - 4, by omega⟩
    have hc : evalOpt (g + 3) w (bindArgs [formal] [val])
        (.cons (.atom (.symbol { name := "consp" })) (.cons (.atom (.symbol formal)) .nil))
        = some .nil := by
      rw [evalOpt_builtin_1 (g + 2) w (bindArgs [formal] [val]) { name := "consp" }
            (.atom (.symbol formal)) val (by decide) h_no_consp
            (evalOpt_var (g + 1) w (bindArgs [formal] [val]) formal val hxlook)]
      rw [callBuiltin_consp, hconsp]
    rw [hbody]
    rw [evalOpt_if_false (g + 3) w (bindArgs [formal] [val]) _ _ _ hc]
    exact evalOpt_quote (g + 2) w _ (.atom (.number (.int base)))
  · -- STEP: consp val ≠ nil → then-branch, recursive call via IH on (cdr val)
    intro val hconsp ih
    obtain ⟨k', N', hrec⟩ := ih
    have hxlook : (bindArgs [formal] [val]).get? formal = some val := by
      show (bindArgs [formal] [val])[formal]? = some val
      simp [bindArgs]
    have htrue : Logic.toBool (Logic.consp val) = true := by
      cases val with
      | cons a d => rfl
      | nil => exact absurd rfl hconsp
      | atom a => exact absurd rfl hconsp
    refine ⟨step + k', N' + 5, fun f hf => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 5 := ⟨f - 5, by omega⟩
    have hc : evalOpt (g + 4) w (bindArgs [formal] [val])
        (.cons (.atom (.symbol { name := "consp" })) (.cons (.atom (.symbol formal)) .nil))
        = some (Logic.consp val) := by
      rw [evalOpt_builtin_1 (g + 3) w (bindArgs [formal] [val]) { name := "consp" }
            (.atom (.symbol formal)) val (by decide) h_no_consp
            (evalOpt_var (g + 2) w (bindArgs [formal] [val]) formal val hxlook)]
      rw [callBuiltin_consp]
    have hcdr : evalOpt (g + 2) w (bindArgs [formal] [val])
        (.cons (.atom (.symbol { name := "cdr" })) (.cons (.atom (.symbol formal)) .nil))
        = some (Logic.cdr val) := by
      rw [evalOpt_builtin_1 (g + 1) w (bindArgs [formal] [val]) { name := "cdr" }
            (.atom (.symbol formal)) val (by decide) h_no_cdr
            (evalOpt_var g w (bindArgs [formal] [val]) formal val hxlook)]
      rw [callBuiltin_cdr]
    have hrecCall : evalOpt (g + 3) w (bindArgs [formal] [val])
        (.cons (.atom (.symbol fnSym))
          (.cons (.cons (.atom (.symbol { name := "cdr" }))
                   (.cons (.atom (.symbol formal)) .nil)) .nil))
        = some (.atom (.number (.int k'))) := by
      rw [evalOpt_defn_1 (g + 2) w (bindArgs [formal] [val]) fnSym
            (.cons (.atom (.symbol { name := "cdr" }))
              (.cons (.atom (.symbol formal)) .nil))
            (Logic.cdr val) formal body h_fn_ns h_fn hcdr]
      exact hrec (g + 2) (by omega)
    have hstep : evalOpt (g + 3) w (bindArgs [formal] [val])
        (.cons (.atom (.symbol { name := "quote" })) (.cons (.atom (.number (.int step))) .nil))
        = some (.atom (.number (.int step))) :=
      evalOpt_quote (g + 2) w _ (.atom (.number (.int step)))
    rw [hbody]
    rw [evalOpt_if_true (g + 4) w (bindArgs [formal] [val]) _ _ _ (Logic.consp val) hc htrue]
    rw [evalOpt_builtin_2 (g + 3) w (bindArgs [formal] [val]) { name := "binary-+" }
          _ _ (.atom (.number (.int step))) (.atom (.number (.int k'))) (by decide) h_no_plus
          hstep hrecCall]
    rw [callBuiltin_plus, logic_plus_int]

/-- A CALL `(fnSym arg)` to a 1-arg user-defined function converges to some
    value, given (a) the argument converges (existential-fuel form), and (b) the
    function body is total at that argument value (the `synthTotality1` fact,
    here in its `∃ k, ∃ N, …` shape). Composes `evalOpt_defn_1`: unfold the call
    one fuel step, then apply the totality fact to the unfolded body. The
    resulting value is `(int k)` but we expose it existentially (`∃ v`) since the
    concrete integer is not known at proof-construction time. -/
theorem callConverges1 (w : World) (env : Env) (fnSym formal : Symbol)
    (arg argVal body : SExpr)
    (h_ns : fnSym.isNamed "quote" = false ∧ fnSym.isNamed "if" = false ∧
            fnSym.isNamed "let" = false ∧ fnSym.isNamed "let*" = false)
    (h_def : w.defs.get? fnSym = some ([formal], body))
    (h_arg : ∃ N, ∀ f ≥ N, evalOpt f w env arg = some argVal)
    (h_tot : ∃ k : Int, ∃ N, ∀ f ≥ N,
      evalOpt f w (bindArgs [formal] [argVal]) body = some (.atom (.number (.int k)))) :
    ∃ v : SExpr, ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol fnSym)) (.cons arg .nil)) = some v := by
  obtain ⟨Na, ha⟩ := h_arg
  obtain ⟨k, Nb, hb⟩ := h_tot
  refine ⟨.atom (.number (.int k)), max Na Nb + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [evalOpt_defn_1 g w env fnSym arg argVal formal body h_ns h_def (ha g (by omega))]
  exact hb g (by omega)

/-- A `(cons a1 a2)` call converges to `.cons v1 v2` (the cons of the two
    argument values), given both arguments converge (existential-fuel form).
    Composes `evalOpt_builtin_2`; `callBuiltin "cons" [v1, v2]` is defeq to
    `.cons v1 v2`. The head symbol must be the `cons` builtin (not special, not
    shadowed). -/
theorem consConverges (w : World) (env : Env) (consSym : Symbol)
    (a1 a2 v1 v2 : SExpr)
    (h_ns : consSym.isNamed "quote" = false ∧ consSym.isNamed "if" = false ∧
            consSym.isNamed "let" = false ∧ consSym.isNamed "let*" = false)
    (h_no_def : w.defs.get? consSym = none)
    (h_cons : consSym.name = "cons")
    (h1 : ∃ N, ∀ f ≥ N, evalOpt f w env a1 = some v1)
    (h2 : ∃ N, ∀ f ≥ N, evalOpt f w env a2 = some v2) :
    ∃ N, ∀ f ≥ N,
      evalOpt f w env (.cons (.atom (.symbol consSym)) (.cons a1 (.cons a2 .nil)))
        = some (.cons v1 v2) := by
  obtain ⟨N1, h1⟩ := h1
  obtain ⟨N2, h2⟩ := h2
  refine ⟨max N1 N2 + 1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [evalOpt_builtin_2 g w env consSym a1 a2 v1 v2 h_ns h_no_def
        (h1 g (by omega)) (h2 g (by omega))]
  rw [h_cons]; rfl

/-- One `f ≥ N+1` step of an `equal-self` proof, given the argument `x`
    converges to `v` for all fuel `≥ N`. Used by the existential-fuel
    `proveEqualSelfNode`: for any `f ≥ N+1`, write `f = g+1` with `g ≥ N`, then
    `evalOpt_equal_self` at `g` gives `eval (g+1) (EQUAL x x) = some T`, and
    `evalOpt_quote` gives `eval (g+1) (QUOTE T) = some T`; so the two sides
    agree. Hides the `Nat` predecessor surgery from the Expr-level producer. -/
theorem equalSelfStep (w : World) (env : Env) (x : SExpr) (N : Nat) (v : SExpr)
    (h_no_def : w.defs.get? ({ name := "equal" } : Symbol) = none)
    (hconv : ∀ f ≥ N, evalOpt f w env x = some v)
    (f : Nat) (hf : f ≥ N + 1) :
    evalOpt f w env
        (.cons (.atom (.symbol { name := "equal" })) (.cons x (.cons x .nil)))
      = evalOpt f w env
        (.cons (.atom (.symbol { name := "quote" })) (.cons SExpr.t .nil)) := by
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [evalOpt_equal_self g w env x v (hconv g (by omega)) h_no_def]
  rw [evalOpt_quote g w env SExpr.t]

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
  /-- Per-case variable context: each clause variable's SHARED abstract value
      and a convergence proof `∀ f, evalOpt (f+1) w env (.atom (.symbol s)) =
      some value`. Populated by the case/induction setup so every node in a
      case sees the same value for a given variable. Empty ⇒ a variable falls
      back to `evalOpt_symbol_converges` (a fresh abstract value per call,
      fine for context-free nodes like equal-self). No hardcoded names. -/
  vars : List (Symbol × Expr × Expr) := []
  /-- Per-case fact PROOFS available to discharge frontier obligations. Each
      entry is a proof term whose type is some equation the node needs (e.g. a
      proof of `Logic.consp xv = SExpr.nil` established by the clause context).
      Searched by `findFact` (defeq up to the target type). Empty ⇒ only
      context-free justifications (structural facts) are available. -/
  facts : List Expr := []

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
    (extraLemmas : Array Name := #[]) (useDecide : Bool := false) : MetaM Expr := do
  let defaultCtx ← Simp.Context.mkDefault
  let mut simpThms := defaultCtx.simpTheorems[0]!
  for n in unfoldNames do
    simpThms ← simpThms.addDeclToUnfold n
  for n in extraLemmas do
    simpThms ← simpThms.addConst n
  let cfg : Simp.Config := { decide := useDecide }
  let ctx ← Simp.mkContext cfg (simpTheorems := #[simpThms])
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
    (unfoldNames := ctx.worldUnfoldNames) (useDecide := true)

/-- Search `ctx.facts` for a proof whose inferred type is defeq to
    `targetType`. Returns the proof term if found, else `none`. Used by the
    recognizer handler to discharge a `callBuiltin RECOG [argVal] = c`
    obligation from a clause-context fact. -/
def findFact (ctx : ProofCtx) (targetType : Expr) : MetaM (Option Expr) := do
  for fact in ctx.facts do
    let factType ← inferType fact
    if ← isDefEq factType targetType then
      return some fact
  return none


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


/-- Does `t` (syntactically) contain a call to one of `definedNames`?
    A call is a cons whose head is a symbol in `definedNames`. Used to detect a
    recursive branch (which needs totality, not handled by `proveDefinitionNode`). -/
partial def callsDefinedFn (definedNames : List Symbol) (t : SExpr) : Bool :=
  match t with
  | .cons (.atom (.symbol s)) rest =>
    definedNames.any (fun d => d == s) || callsDefinedFn definedNames rest
  | .cons a d => callsDefinedFn definedNames a || callsDefinedFn definedNames d
  | _ => false

/-! ## Totality synthesis routine

  `synthTotality1` detects the 1-arg structural-recursion shape of `fnSym`'s
  body in `w` and produces a kernel-checked proof of its totality / integer
  type-prescription by instantiating `totality1_generic`. Detection-driven:
  hard-fails (throwError) for any function not of the supported shape. -/

/-- Parse an integer-quote `(QUOTE (int n))`; fail otherwise. -/
private def parseIntQuote (e : SExpr) (what : String) : MetaM Int := do
  match e with
  | .cons (.atom (.symbol q)) (.cons (.atom (.number (.int n))) .nil) =>
    if q.isNamed "quote" then pure n
    else throwError "synthTotality1: {what} is not a quoted integer: {repr e}"
  | _ => throwError "synthTotality1: {what} is not a quoted integer: {repr e}"

/-- Synthesize a totality/type-prescription proof for a 1-arg structurally
    recursive function `fnSym` defined in `w`. The body must have the shape

        (IF (CONSP formal) (BINARY-+ 'step (fnSym (CDR formal))) 'base)

    (1-arg, structural recursion on the single formal, recursing only as
    `(fnSym (CDR formal))`, integer-valued). Returns a kernel-checkable `Expr`
    of type

        ∀ val, ∃ k : Int, ∃ N, ∀ f ≥ N,
          evalOpt f w (bindArgs [formal] [val]) body
            = some (.atom (.number (.int k)))

    `worldExpr` is the reflected World; `worldUnfoldNames` are the definition
    names to unfold when discharging the HashMap-lookup side conditions.
    Hard-fails at the frontier (wrong arity, non-structural recursion, multiple
    recursive calls, non-integer base/step, etc.). No hardcoded names. -/
def synthTotality1 (w : World) (worldExpr : Expr) (worldUnfoldNames : Array Name)
    (fnSym : Symbol) : MetaM Expr := do
  -- Look up the definition; require exactly one formal.
  let some (formals, body) := w.defs.get? fnSym
    | throwError "synthTotality1: {repr fnSym} not in world.defs (frontier)"
  let formal ← match formals with
    | [f] => pure f
    | _ => throwError "synthTotality1: {repr fnSym} is not 1-arg \
        (formals = {repr formals}); only 1-arg structural recursion supported (frontier)"
  -- Body must be (IF test thenB elseB).
  let (test, thenB, elseB) ← match body with
    | .cons (.atom (.symbol ifSym))
        (.cons test (.cons thenB (.cons elseB .nil))) =>
      if ifSym.isNamed "if" then pure (test, thenB, elseB)
      else throwError "synthTotality1: body head is not IF: {repr body}"
    | _ => throwError "synthTotality1: body is not a 4-element IF: {repr body} (frontier)"
  -- Test must be (CONSP formal): structural recursion on the single formal.
  match test with
  | .cons (.atom (.symbol cs)) (.cons (.atom (.symbol tv)) .nil) =>
    unless cs.isNamed "consp" && tv == formal do
      throwError "synthTotality1: test is not (CONSP formal): {repr test} (frontier)"
  | _ => throwError "synthTotality1: test is not a 1-arg recognizer on the formal: \
      {repr test} (frontier)"
  -- Else-branch must be a quoted integer `base` (the type-prescription base).
  let base ← parseIntQuote elseB "else-branch (base case)"
  -- Then-branch must be (BINARY-+ 'step (fnSym (CDR formal))): the single
  -- structural recursive call combined with a constant integer.
  let recCallExpected : SExpr :=
    .cons (.atom (.symbol fnSym))
      (.cons (.cons (.atom (.symbol { name := "cdr" }))
               (.cons (.atom (.symbol formal)) .nil)) .nil)
  let step ← match thenB with
    | .cons (.atom (.symbol plusSym)) (.cons stepQ (.cons recCall .nil)) =>
      unless plusSym.isNamed "binary-+" do
        throwError "synthTotality1: then-branch head is not BINARY-+: {repr thenB} (frontier)"
      unless recCall == recCallExpected do
        throwError "synthTotality1: recursive call is not (fnSym (CDR formal)): \
          {repr recCall}; only structural recursion on the formal supported (frontier)"
      parseIntQuote stepQ "then-branch step constant"
    | _ => throwError "synthTotality1: then-branch is not (BINARY-+ 'step (rec)): \
        {repr thenB} (frontier)"
  -- Reject any *other* recursive calls (multiple recursion is the frontier):
  -- the only legal call to fnSym is the one we matched in `recCall`.
  let elseHasRec := callsDefinedFn [fnSym] elseB
  if elseHasRec then
    throwError "synthTotality1: recursive call in else-branch unsupported (frontier)"
  -- All checks passed. Instantiate `totality1_generic`.
  -- Side conditions:
  --   hbody : body = <reflected generic shape>  — `rfl` (same reflected term).
  --   h_fn  : w.defs[fnSym]? = some ([formal], body)
  --   h_no_* : builtins not shadowed
  --   h_fn_ns : fnSym not special
  let ctx : ProofCtx := {
    worldExpr := worldExpr, world := w, envExpr := worldExpr /- unused here -/,
    worldUnfoldNames := worldUnfoldNames }
  let hBody ← do
    let bodyE := reflectSExpr body
    mkAppM ``Eq.refl #[bodyE]
  let hFn ← proveWorldDefnLookup ctx fnSym [formal] body
  let hNoConsp ← proveWorldLookupNone ctx { name := "consp" }
  let hNoCdr ← proveWorldLookupNone ctx { name := "cdr" }
  let hNoPlus ← proveWorldLookupNone ctx { name := "binary-+" }
  let hFnNs ← proveNotSpecial fnSym
  return mkAppN (Lean.mkConst ``totality1_generic)
    #[worldExpr, reflectSymbol fnSym, reflectSymbol formal,
      reflectInt base, reflectInt step, reflectSExpr body,
      hBody, hFn, hNoConsp, hNoCdr, hNoPlus, hFnNs]
where
  /-- Local copies of the world-lookup provers (the proof-tree handlers are in
      the `proveNode` where-block and not in scope here). -/
  proveWorldDefnLookup (ctx : ProofCtx) (fnSym : Symbol)
      (formals : List Symbol) (body : SExpr) : MetaM Expr := do
    let worldDefs := mkApp (Lean.mkConst ``World.defs) ctx.worldExpr
    let lookupExpr ← mkAppM ``Std.HashMap.get? #[worldDefs, reflectSymbol fnSym]
    let formalsListExpr := formals.foldr
      (fun s acc => mkApp3 (Lean.mkConst ``List.cons [0]) (Lean.mkConst ``Symbol)
        (reflectSymbol s) acc)
      (mkApp (Lean.mkConst ``List.nil [0]) (Lean.mkConst ``Symbol))
    let pairExpr := mkApp4 (Lean.mkConst ``Prod.mk [0, 0])
      (← mkAppM ``List #[Lean.mkConst ``Symbol]) (Lean.mkConst ``SExpr)
      formalsListExpr (reflectSExpr body)
    let pairTy ← inferType pairExpr
    let someE := mkApp2 (Lean.mkConst ``Option.some [0]) pairTy pairExpr
    proveBySimp (← mkAppM ``Eq #[lookupExpr, someE])
      (unfoldNames := ctx.worldUnfoldNames) (useDecide := true)

/-- Prove a single proof node. Returns an existential fuel proof:
    `∃ N, ∀ f ≥ N, evalOpt f w env node.lhs = evalOpt f w env node.rhs`

    Every step is a symbolic rewrite directed by the proof tree.
    The proof producer constructs the corresponding EvalLemma application.
    No ground evaluation — all proofs work with arbitrary env. -/
partial def proveNode (ctx : ProofCtx) (node : ProofNode) : MetaM Expr := do
  match node with
  | .node (runeType, runeName) lhs rhs children _prov =>
    match runeType with
    | "equal-self" => proveEqualSelfNode ctx lhs rhs
    | "fake-rune-for-anonymous-enabled-rule" => proveRecognizerNode ctx lhs rhs
    | "definition" => proveDefinitionNode ctx runeName lhs rhs children
    | other => throwError "proveNode: rune type '{other}' not yet implemented"
where
  /-- Prove symbolic convergence of a term: ∃ v, evalOpt (f+1) w env term = some v.
      Returns (xv, hxv) where xv is the abstract value Expr and
      hxv proves evalOpt (f+1) w env term = some xv. -/
  proveConverges (ctx : ProofCtx) (f : Nat) (term : SExpr) :
      MetaM (Expr × Expr) := do
    match term with
    | .atom (.symbol s) =>
      match ctx.vars.find? (fun (s', _, _) => s' == s) with
      | some (_, val, conv) =>
        -- shared case value: `conv f : eval (f+1) w env s = some val`
        return (val, mkApp conv (mkNatLit f))
      | none =>
        -- no case binding: a fresh abstract value via evalOpt_symbol_converges
        let hConv := mkAppN (Lean.mkConst ``evalOpt_symbol_converges)
          #[mkNatLit f, ctx.worldExpr, ctx.envExpr, reflectSymbol s]
        let xv ← mkAppM ``Exists.choose #[hConv]
        let hxv ← mkAppM ``Exists.choose_spec #[hConv]
        return (xv, hxv)
    | .atom (.number n) =>
      -- Number literal: converges to itself
      let proof ← proveNumberEval ctx f n
      return (reflectSExpr (.atom (.number n)), proof)
    | .nil =>
      let proof ← proveNilEval ctx f
      return (reflectSExpr .nil, proof)
    | .cons (.atom (.symbol q)) (.cons v .nil) =>
      if q.isNamed "quote" then
        let proof ← proveQuoteEval ctx f v
        return (reflectSExpr v, proof)
      else
        throwError "proveConverges: unsupported term {repr term}"
    | .cons (.atom (.symbol c)) (.cons a1 (.cons a2 .nil)) =>
      -- General 2-arg builtin call. The only structural value we can name
      -- without a context fact is CONS: `(cons a1 a2)` evaluates to the cons
      -- of the argument values. `callBuiltin "cons" [v1,v2]` is defeq to
      -- `.cons v1 v2`, so we expose the literal cons as the value Expr.
      if c.isNamed "cons" then
        -- Args evaluate at fuel `g = f-1`; the call lands at fuel `g+1 = f+1`.
        -- Requires `f ≥ 1` (the argument values must converge first).
        let g ← match f with
          | 0 => throwError "proveConverges: (cons ..) needs fuel ≥ 1"
          | g + 1 => pure g
        let (v1, h1) ← proveConverges ctx g a1
        let (v2, h2) ← proveConverges ctx g a2
        -- evalOpt_builtin_2: eval (f+1) (cons a1 a2)
        --   = some (callBuiltin "cons" [v1, v2])
        let hNotSpecial ← proveNotSpecial c
        let hNoDef ← proveWorldLookupNone ctx c
        let hRaw := mkAppN (Lean.mkConst ``evalOpt_builtin_2)
          #[mkNatLit f, ctx.worldExpr, ctx.envExpr,
            reflectSymbol c, reflectSExpr a1, reflectSExpr a2, v1, v2,
            hNotSpecial, hNoDef, h1, h2]
        -- `some (callBuiltin "cons" [v1,v2])` is defeq to `some (.cons v1 v2)`;
        -- retype the proof so the named value is the literal cons.
        let consVal := mkApp2 (Lean.mkConst ``SExpr.cons) v1 v2
        let someConsVal := mkApp2 (Lean.mkConst ``Option.some [0])
          (Lean.mkConst ``SExpr) consVal
        let lhsEval := mkAppN (Lean.mkConst ``evalOpt)
          #[mkNatLit (f + 1), ctx.worldExpr, ctx.envExpr, reflectSExpr term]
        let targetTy ← mkAppM ``Eq #[lhsEval, someConsVal]
        let hEval ← mkExpectedTypeHint hRaw targetTy
        return (consVal, hEval)
      else
        throwError "proveConverges: unsupported term {repr term}"
    | _ =>
      throwError "proveConverges: unsupported term {repr term}"

  /-- Existential-fuel convergence: returns `(value, proof)` where
      `proof : ∃ N, ∀ f ≥ N, evalOpt f w env term = some value`.

      Strictly more capable than the fixed-fuel `proveConverges`: it additionally
      handles a CALL `(fnSym arg)` to a 1-arg structurally-recursive,
      integer-valued function (detected and proven total by `synthTotality1`),
      whose convergence holds only for fuel `≥ N` with `N` existential — which a
      fixed-fuel proof cannot express. Leaf/structural cases mirror
      `proveConverges`, lifted to the existential form via `mkFuelConvergeExist`
      / `consConverges`. Hard-fails at the frontier (anything `synthTotality1`
      rejects, or any unsupported shape). -/
  proveConvergesExist (ctx : ProofCtx) (term : SExpr) :
      MetaM (Expr × Expr) := do
    match term with
    | .atom (.symbol s) =>
      match ctx.vars.find? (fun (s', _, _) => s' == s) with
      | some (_, val, conv) =>
        -- `conv 0 : eval (0+1) w env s = some val`; lift fuel-1 proof to ∃-form.
        -- `val` is an Expr (possibly opaque), so use the Expr-valued wrapper.
        let h0 := mkApp conv (mkNatLit 0)
        let hExist ← mkFuelConvergeExistTermE ctx 1 term val h0
        return (val, hExist)
      | none =>
        -- No case binding: a fresh abstract value via evalOpt_symbol_converges.
        let hConv := mkAppN (Lean.mkConst ``evalOpt_symbol_converges)
          #[mkNatLit 0, ctx.worldExpr, ctx.envExpr, reflectSymbol s]
        let xv ← mkAppM ``Exists.choose #[hConv]
        let h0 ← mkAppM ``Exists.choose_spec #[hConv]
        let hExist ← mkFuelConvergeExistTermE ctx 1 term xv h0
        return (xv, hExist)
    | .atom (.number n) =>
      let h0 ← proveNumberEval ctx 0 n
      let hExist ← mkFuelConvergeExistTerm ctx 1 term (.atom (.number n)) h0
      return (reflectSExpr (.atom (.number n)), hExist)
    | .nil =>
      let h0 ← proveNilEval ctx 0
      let hExist ← mkFuelConvergeExistTerm ctx 1 term .nil h0
      return (reflectSExpr .nil, hExist)
    | .cons (.atom (.symbol q)) (.cons v .nil) =>
      if q.isNamed "quote" then
        let h0 ← proveQuoteEval ctx 0 v
        let hExist ← mkFuelConvergeExistTerm ctx 1 term v h0
        return (reflectSExpr v, hExist)
      else
        -- 1-arg call. If the head is a defined function that `synthTotality1`
        -- accepts, the call converges to an integer (totality fact). Otherwise
        -- the frontier: let synthTotality1's own throwError propagate.
        proveCallConvergesExist ctx q v
    | .cons (.atom (.symbol c)) (.cons a1 (.cons a2 .nil)) =>
      if c.isNamed "cons" then
        let (v1, h1) ← proveConvergesExist ctx a1
        let (v2, h2) ← proveConvergesExist ctx a2
        let hNotSpecial ← proveNotSpecial c
        let hNoDef ← proveWorldLookupNone ctx c
        let hName ← proveByDecide (mkApp3 (Lean.mkConst ``Eq [1])
          (Lean.mkConst ``String)
          (mkApp (Lean.mkConst ``Symbol.name) (reflectSymbol c)) (mkStrLit "cons"))
        let consVal := mkApp2 (Lean.mkConst ``SExpr.cons) v1 v2
        let hExist := mkAppN (Lean.mkConst ``consConverges)
          #[ctx.worldExpr, ctx.envExpr, reflectSymbol c,
            reflectSExpr a1, reflectSExpr a2, v1, v2,
            hNotSpecial, hNoDef, hName, h1, h2]
        return (consVal, hExist)
      else
        throwError "proveConvergesExist: unsupported term {repr term}"
    | _ =>
      throwError "proveConvergesExist: unsupported term {repr term}"

  /-- CALL `(fnSym arg)` (1-arg) convergence in existential-fuel form. Drives off
      `synthTotality1` to obtain the body-totality fact for `fnSym`; if the
      function is off-shape, `synthTotality1` hard-fails (frontier). The argument
      converges (recursively), and `callConverges1` composes the unfold step with
      the totality fact. The integer value is existential, so it is exposed via
      `Exists.choose`. -/
  proveCallConvergesExist (ctx : ProofCtx) (fnSym : Symbol)
      (arg : SExpr) : MetaM (Expr × Expr) := do
    let some (formals, body) := ctx.world.defs.get? fnSym
      | throwError "proveConvergesExist: {repr fnSym} not in world.defs (frontier)"
    let formal ← match formals with
      | [f] => pure f
      | _ => throwError "proveConvergesExist: {repr fnSym} is not 1-arg (frontier)"
    -- Totality fact: ∀ val, ∃ k, ∃ N, ∀ f ≥ N, eval f (bindArgs [formal] [val]) body
    --   = some (int k). Off-shape ⇒ synthTotality1 hard-fails (frontier).
    let totGeneric ← synthTotality1 ctx.world ctx.worldExpr ctx.worldUnfoldNames fnSym
    -- Argument convergence (existential).
    let (argVal, hArg) ← proveConvergesExist ctx arg
    -- Specialize the totality fact at argVal: ∃ k, ∃ N, ∀ f ≥ N, … = some (int k).
    let hTot := mkApp totGeneric argVal
    let hNs ← proveNotSpecial fnSym
    let hDef ← proveWorldDefnLookupExist ctx fnSym formal body
    -- callConverges1: ∃ v, ∃ N, ∀ f ≥ N, eval f w env (fnSym arg) = some v.
    let hCall := mkAppN (Lean.mkConst ``callConverges1)
      #[ctx.worldExpr, ctx.envExpr, reflectSymbol fnSym, reflectSymbol formal,
        reflectSExpr arg, argVal, reflectSExpr body, hNs, hDef, hArg, hTot]
    -- Expose the value existentially.
    let v ← mkAppM ``Exists.choose #[hCall]
    let hExist ← mkAppM ``Exists.choose_spec #[hCall]
    return (v, hExist)

  /-- `proveWorldDefnLookup` for the totality/call path (the where-bound one
      below has the same body; this keeps it usable inside the converger). -/
  proveWorldDefnLookupExist (ctx : ProofCtx) (fnSym : Symbol)
      (formal : Symbol) (body : SExpr) : MetaM Expr := do
    let worldDefs := mkApp (Lean.mkConst ``World.defs) ctx.worldExpr
    let lookupExpr ← mkAppM ``Std.HashMap.get? #[worldDefs, reflectSymbol fnSym]
    let formalsListExpr := mkApp3 (Lean.mkConst ``List.cons [0]) (Lean.mkConst ``Symbol)
      (reflectSymbol formal) (mkApp (Lean.mkConst ``List.nil [0]) (Lean.mkConst ``Symbol))
    let pairExpr := mkApp4 (Lean.mkConst ``Prod.mk [0, 0])
      (← mkAppM ``List #[Lean.mkConst ``Symbol]) (Lean.mkConst ``SExpr)
      formalsListExpr (reflectSExpr body)
    let pairTy ← inferType pairExpr
    let someE := mkApp2 (Lean.mkConst ``Option.some [0]) pairTy pairExpr
    proveBySimp (← mkAppM ``Eq #[lookupExpr, someE])
      (unfoldNames := ctx.worldUnfoldNames) (useDecide := true)

  /-- Wrap a fixed-fuel proof `eval N w env term = some v` (SExpr value `v`) into
      `∃ M, ∀ f ≥ M, eval f w env term = some v`, via `mkFuelConvergeExist`. -/
  mkFuelConvergeExistTerm (ctx : ProofCtx) (N : Nat) (term v : SExpr)
      (h : Expr) : MetaM Expr :=
    mkFuelConvergeExist ctx N term v h

  /-- As `mkFuelConvergeExistTerm` but the value is an Expr (possibly opaque),
      not a reflectable SExpr. -/
  mkFuelConvergeExistTermE (ctx : ProofCtx) (N : Nat) (term : SExpr) (vE : Expr)
      (h : Expr) : MetaM Expr := do
    let NE := mkNatLit N
    let aE := reflectSExpr term
    let someV := mkApp2 (Lean.mkConst ``Option.some [0]) (Lean.mkConst ``SExpr) vE
    let pred ← mkFuelPredLocal ctx aE fun _ => someV
    withLocalDeclD `f (Lean.mkConst ``Nat) fun fVar => do
      let geType ← mkAppM ``GE.ge #[fVar, NE]
      withLocalDeclD `hf geType fun hfVar => do
        let geA := mkAppN (Lean.mkConst ``evalOpt_ge_fuel)
          #[NE, fVar, ctx.worldExpr, ctx.envExpr, aE, vE, h, hfVar]
        let body ← mkLambdaFVars #[fVar, hfVar] geA
        return mkApp4 (Lean.mkConst ``Exists.intro [1])
          (Lean.mkConst ``Nat) pred NE body

  /-- `mkFuelPred` inlined (the private top-level one is not in scope here). -/
  mkFuelPredLocal (ctx : ProofCtx) (aExpr : Expr) (mkRhs : Expr → Expr) :
      MetaM Expr := do
    withLocalDeclD `N (Lean.mkConst ``Nat) fun nVar => do
      withLocalDeclD `f (Lean.mkConst ``Nat) fun fVar => do
        let geType ← mkAppM ``GE.ge #[fVar, nVar]
        withLocalDeclD `hf geType fun hfVar => do
          let lhsEval := mkAppN (Lean.mkConst ``evalOpt)
            #[fVar, ctx.worldExpr, ctx.envExpr, aExpr]
          let eqType ← mkAppM ``Eq #[lhsEval, mkRhs fVar]
          let forall_ ← mkForallFVars #[fVar, hfVar] eqType
          mkLambdaFVars #[nVar] forall_

  /-- equal-self: (EQUAL X X) → (QUOTE T)
      Symbolic proof: X converges to some abstract value xv,
      then evalOpt_equal_self gives eval(EQUAL X X) = some T.

      Uses the existential-fuel converger so that `X` may itself be a CALL to a
      recursive function (e.g. `(MY-LEN X)`): `proveConvergesExist` gives
      `∃ N, ∀ f ≥ N, eval f w env X = some xv`; we obtain a concrete-fuel witness
      from it via `Exists.choose`/`choose_spec` rebased through `evalOpt_ge_fuel`
      is unnecessary — instead compose at the existential level throughout. -/
  proveEqualSelfNode (ctx : ProofCtx) (lhs rhs : SExpr) : MetaM Expr := do
    let x := match lhs with
      | .cons _ (.cons x (.cons _ .nil)) => x
      | _ => panic! "equal-self: LHS is not (EQUAL X X)"
    -- Existential convergence of X: ∃ N, ∀ f ≥ N, eval f w env X = some xv.
    let (xv, hxvExist) ← proveConvergesExist ctx x
    -- Obtain a concrete-fuel witness from the existential: choose N, get the
    -- ∀ f ≥ N fact, then instantiate at N to feed evalOpt_equal_self at N.
    let hNoDef ← proveWorldLookupNone ctx { name := "equal" }
    -- We build the equal-self proof at the existential level: for each f ≥ N,
    -- eval (f) X = some xv, and eval (f+1) (EQUAL X X) = some T (equal_self),
    -- eval (f+1) (QUOTE T) = some T (quote). Compose into ∃ M, ∀ f≥M, lhs = rhs.
    let xExpr := reflectSExpr x
    -- N from the existential.
    let hN ← mkAppM ``Exists.choose #[hxvExist]
    let hSpec ← mkAppM ``Exists.choose_spec #[hxvExist]
    -- predicate: fun N => ∀ f ≥ N, eval f w env lhs = eval f w env rhs
    let lhsE := reflectSExpr lhs
    let rhsE := reflectSExpr rhs
    let pred ← mkFuelPredLocal ctx lhsE fun fVar =>
      mkAppN (Lean.mkConst ``evalOpt) #[fVar, ctx.worldExpr, ctx.envExpr, rhsE]
    -- witness M = N + 1.
    let mExpr ← mkAppM ``HAdd.hAdd #[hN, mkNatLit 1]
    let proofBody ← withLocalDeclD `f (Lean.mkConst ``Nat) fun fVar => do
      let geType ← mkAppM ``GE.ge #[fVar, mExpr]
      withLocalDeclD `hf geType fun hfVar => do
        -- f = g + 1 with g ≥ N.
        -- We get g via f - 1; supply (f-1 ≥ N) and rewrite eval f = eval ((f-1)+1).
        -- Simpler: use a helper lemma to avoid manual Nat surgery in Expr-land.
        let body ← mkAppM ``equalSelfStep
          #[ctx.worldExpr, ctx.envExpr, xExpr, hN, xv, hNoDef, hSpec, fVar, hfVar]
        mkLambdaFVars #[fVar, hfVar] body
    let exbuilt := mkApp4 (Lean.mkConst ``Exists.intro [1])
      (Lean.mkConst ``Nat) pred mExpr proofBody
    return exbuilt

  /-- Minimum fuel `f` such that `proveConverges ctx f term` succeeds: the
      nesting depth of evaluated calls (leaves need fuel 0 ⇒ `eval (f+1)`;
      each `(cons ..)` layer needs one more). General over term shape. -/
  convergeFuel (term : SExpr) : Nat :=
    match term with
    | .cons (.atom (.symbol _)) (.cons a1 (.cons a2 .nil)) =>
      1 + max (convergeFuel a1) (convergeFuel a2)
    | _ => 0

  /-- Parse a quoted constant `(QUOTE c)` into `c`; fail otherwise. -/
  parseQuotedConst (e : SExpr) : MetaM SExpr := do
    match e with
    | .cons (.atom (.symbol q)) (.cons c .nil) =>
      if q.isNamed "quote" then pure c
      else throwError "recognizer: RHS is not a quoted constant: {repr e}"
    | _ => throwError "recognizer: RHS is not a quoted constant: {repr e}"

  /-- recognizer node: `(RECOG arg) → 'c` (c = NIL or T).
      Meaning: `eval(RECOG arg) = eval('c)`. General over the recognizer
      builtin and the argument. Justification of `callBuiltin RECOG [argVal] = c`
      comes from (a) a structural fact (consp of a CONS form) or (b) a clause
      context fact in `ctx.facts`; otherwise hard-fail at the frontier. -/
  proveRecognizerNode (ctx : ProofCtx) (lhs rhs : SExpr) : MetaM Expr := do
    -- Parse `(RECOG arg)`.
    let (recogSym, arg) ← match lhs with
      | .cons (.atom (.symbol s)) (.cons arg .nil) => pure (s, arg)
      | _ => throwError "recognizer: LHS is not a 1-arg call: {repr lhs}"
    -- Parse the quoted result constant.
    let c ← parseQuotedConst rhs
    let cExpr := reflectSExpr c
    -- Evaluate the argument symbolically (fuel sized to its call nesting).
    let fa := convergeFuel arg
    let (argVal, hArgEval) ← proveConverges ctx fa arg
    -- eval (fa+2) (RECOG arg) = some (callBuiltin recogSym.name [argVal]).
    -- `proveBuiltin1` reflects its `av : SExpr`, but `argVal` is already a value
    -- Expr (possibly opaque), so build the `evalOpt_builtin_1` application
    -- directly to pass the Expr value.
    let hNotSpecial ← proveNotSpecial recogSym
    let hNoDef ← proveWorldLookupNone ctx recogSym
    let hRecog := mkAppN (Lean.mkConst ``evalOpt_builtin_1)
      #[mkNatLit (fa + 1), ctx.worldExpr, ctx.envExpr,
        reflectSymbol recogSym, reflectSExpr arg, argVal,
        hNotSpecial, hNoDef, hArgEval]
    -- Build the obligation `callBuiltin recogSym.name [argVal] = c`.
    let callExpr ← mkAppM ``callBuiltin
      #[mkStrLit recogSym.name, ← mkListLitSExpr [argVal]]
    let hCall ← proveCallEqConst ctx recogSym arg callExpr cExpr c
    -- some (callBuiltin ..) = some c, then eval (RECOG arg) = some c.
    let hSomeEq ← mkAppM ``congrArg
      #[mkApp (Lean.mkConst ``Option.some [0]) (Lean.mkConst ``SExpr), hCall]
    let hA ← mkAppM ``Eq.trans #[hRecog, hSomeEq]
    -- eval ('c) = some c.
    let hB ← proveQuoteEval ctx (fa + 1) c
    -- Wrap: ∃ N, ∀ f ≥ N, eval(RECOG arg) = eval('c).
    mkFuelEqExist ctx (fa + 2) lhs rhs c hA hB

  /-- Build a `List SExpr` Lean Expr literal from value Exprs. -/
  mkListLitSExpr (vs : List Expr) : MetaM Expr := do
    let mut acc := mkApp (Lean.mkConst ``List.nil [0]) (Lean.mkConst ``SExpr)
    for v in vs.reverse do
      acc := mkApp3 (Lean.mkConst ``List.cons [0]) (Lean.mkConst ``SExpr) v acc
    return acc

  /-- Prove `callBuiltin recogSym.name [argVal] = c`.
      (a) Structural: `arg` is a CONS form and the call is `consp` of a cons
          value ⇒ reduces by defeq (`callBuiltin_consp`/`consp_cons`) to `T`
          (a general fact, no context needed).
      (b) Context fact: a proof in `ctx.facts` whose type is defeq to the
          equation. A fact stated at the `Logic.*` level (e.g.
          `Logic.consp argVal = nil`) is defeq to the `callBuiltin` form and is
          accepted by `findFact` directly.
      Otherwise hard-fail at the frontier. -/
  proveCallEqConst (ctx : ProofCtx) (recogSym : Symbol) (arg : SExpr)
      (callExpr cExpr : Expr) (c : SExpr) : MetaM Expr := do
    let targetTy ← mkAppM ``Eq #[callExpr, cExpr]
    -- (a) Structural: consp of a syntactic CONS form, result T. `callExpr`
    -- (`callBuiltin "consp" [.cons v1 v2]`) is defeq to `SExpr.t`, so a defeq
    -- retype of `rfl` discharges the equation.
    let isConsForm := match arg with
      | .cons (.atom (.symbol cs)) (.cons _ (.cons _ .nil)) => cs.isNamed "cons"
      | _ => false
    if recogSym.isNamed "consp" && isConsForm && c == SExpr.t then
      let pf ← mkAppM ``Eq.refl #[cExpr]
      return ← mkExpectedTypeHint pf targetTy
    -- (b) Context fact (callBuiltin- or Logic-level, matched up to defeq).
    match ← findFact ctx targetTy with
    | some pf => return pf
    | none => throwError "recognizer: no justification for {repr arg} → {repr c}"

  /-- Reflect a `List Symbol` as a Lean `Expr` of type `List Symbol`. -/
  reflectSymbolList (ss : List Symbol) : Expr :=
    match ss with
    | [] => mkApp (Lean.mkConst ``List.nil [0]) (Lean.mkConst ``Symbol)
    | s :: rest => mkApp3 (Lean.mkConst ``List.cons [0]) (Lean.mkConst ``Symbol)
        (reflectSymbol s) (reflectSymbolList rest)

  /-- Prove `(bindArgs formals argVals).get? p = some pv` for a concrete formal
      `p` bound (with distinct concrete formals) to value Expr `pv` at its
      position. `formalsExpr`/`argValsExpr` are the reflected `List Symbol` /
      `List SExpr` Exprs. Discharged by `simp [bindArgs, getElem?_insert]` +
      `decide` on the symbol-equality conditions — the same mechanism as the
      hand proof's `hxlook`/`hylook`. -/
  proveBindLookup (formalsExpr argValsExpr : Expr) (p : Symbol) (pv : Expr) :
      MetaM Expr := do
    let bindEnv ← mkAppM ``bindArgs #[formalsExpr, argValsExpr]
    let lookup ← mkAppM ``Std.HashMap.get? #[bindEnv, reflectSymbol p]
    let someV := mkApp2 (Lean.mkConst ``Option.some [0]) (Lean.mkConst ``SExpr) pv
    let goalTy ← mkAppM ``Eq #[lookup, someV]
    proveBySimp goalTy (unfoldNames := #[``bindArgs])
      (extraLemmas := #[``Std.HashMap.getElem?_insert]) (useDecide := true)

  /-- definition node: `(fn a1 … an) → rhs` (n = 1 or 2), where `rhs` is the
      simplified body after its IF was resolved. Produces
      `∃N∀f≥N, eval (fn args) = eval rhs`.

      General mechanism (no hardcoded names), scoped to the non-recursive
      (base-case) shape: unfold the call (`evalOpt_defn_*`), resolve the body's
      IF using the `if-simplification` child to learn the branch and the
      recognizer mechanism to evaluate the test, then evaluate the chosen
      branch. Both the call and `rhs` converge to the same value `V`. -/
  proveDefinitionNode (ctx : ProofCtx) (fnName : String) (lhs rhs : SExpr)
      (children : List ProofNode) : MetaM Expr := do
    -- Parse the call `(fn a1 … an)`.
    let (fnSym, args) ← match lhs with
      | .cons (.atom (.symbol s)) rest =>
        match rest.toList? with
        | some as => pure (s, as)
        | none => throwError "definition: malformed call argument list: {repr lhs}"
      | _ => throwError "definition: LHS is not a call: {repr lhs}"
    unless fnSym.isNamed fnName do
      throwError "definition: rune name {fnName} ≠ call head {repr fnSym}"
    -- Look up the definition in the world (hard-fail if absent).
    let some (formals, body) := ctx.world.defs.get? fnSym
      | throwError "definition: function {repr fnSym} not in world.defs (frontier)"
    unless formals.length == args.length do
      throwError "definition: arity mismatch for {repr fnSym}"
    -- Support arity 1 and 2 only (evalOpt_defn_1/2); hard-fail otherwise.
    unless formals.length == 1 || formals.length == 2 do
      throwError "definition: arity {formals.length} unsupported (frontier)"
    -- The body must be (IF test thenB elseB).
    let (test, thenB, elseB) ← match body with
      | .cons (.atom (.symbol ifSym))
          (.cons test (.cons thenB (.cons elseB .nil))) =>
        if ifSym.isNamed "if" then pure (test, thenB, elseB)
        else throwError "definition: body head is not IF: {repr body}"
      | _ => throwError "definition: body is not a 4-element IF: {repr body}"
    -- Find the if-simplification child to learn which branch was taken.
    let chosenB ← do
      let mut found : Option SExpr := none
      for c in children do
        match c with
        | .node (rt, _) _ crhs _ _ => if rt == "if-simplification" then found := some crhs
      match found with
      | some r => pure r
      | none => throwError "definition: no if-simplification child (frontier)"
    let isThen ← if chosenB == thenB then pure true
      else if chosenB == elseB then pure false
      else throwError "definition: if-simplification rhs {repr chosenB} \
        matches neither branch"
    -- Hard-fail if the chosen branch calls a user-defined (recursive) function:
    -- that needs totality, which is the next step, not this one.
    let definedNames := ctx.world.defs.toList.map (fun (s, _) => s)
    if callsDefinedFn definedNames chosenB then
      throwError "definition: recursive branch needs totality (frontier)"
    -- Reflect formals and build the argument-value list + arg-eval proofs.
    let formalsExpr := reflectSymbolList formals
    -- The body env evaluates the chosen branch at fuel `bcf+1`; the test must
    -- evaluate at fuel `bcf` ≥ 1 (it contains the formal variable lookup).
    let bcf := Nat.max (convergeFuel chosenB) 1
    -- We will prove `eval (M+1) w env (fn args) = some V` where M = bcf+2 is the
    -- fuel the body's IF needs. Arg-eval proofs feed `evalOpt_defn_*` at fuel M.
    let bodyFuel := bcf + 2
    -- Argument values + proofs `eval bodyFuel w env aᵢ = some avᵢ`.
    let mut argVals : List Expr := []
    let mut argProofs : List Expr := []
    for a in args do
      let af := convergeFuel a
      unless af + 1 ≤ bodyFuel do
        throwError "definition: argument {repr a} needs more fuel than allotted (frontier)"
      -- proveConverges gives `eval (af+1) ... a = some av`; bump to `eval bodyFuel`
      -- via evalOpt_ge_fuel (bodyFuel ≥ af+1) so it feeds `evalOpt_defn_*`.
      let (av, hRaw) ← proveConverges ctx af a
      let hBumped := mkAppN (Lean.mkConst ``evalOpt_ge_fuel)
        #[mkNatLit (af + 1), mkNatLit bodyFuel, ctx.worldExpr, ctx.envExpr,
          reflectSExpr a, av, hRaw, ← mkGeProof bodyFuel (af + 1)]
      argVals := argVals ++ [av]
      argProofs := argProofs ++ [hBumped]
    -- Build the body env Expr: bindArgs formals argVals.
    let argValsListExpr ← mkListLitSExpr argVals
    let bodyEnvExpr ← mkAppM ``bindArgs #[formalsExpr, argValsListExpr]
    -- Build the body-env context: each formal looks up to its arg value, with a
    -- convergence proof `fun f => eval (f+1) w bodyEnv pᵢ = some avᵢ`.
    let mut bodyVars : List (Symbol × Expr × Expr) := []
    for (p, pv) in formals.zip argVals do
      let hLookup ← proveBindLookup formalsExpr argValsListExpr p pv
      -- conv : fun (f : Nat) => evalOpt_var f w bodyEnv p pv hLookup
      let conv ← withLocalDeclD `f (Lean.mkConst ``Nat) fun fVar => do
        let body := mkAppN (Lean.mkConst ``evalOpt_var)
          #[fVar, ctx.worldExpr, bodyEnvExpr, reflectSymbol p, pv, hLookup]
        mkLambdaFVars #[fVar] body
      bodyVars := bodyVars ++ [(p, pv, conv)]
    let ctx' : ProofCtx := { ctx with envExpr := bodyEnvExpr, vars := bodyVars }
    -- Parse the test as a recognizer call `(RECOG p)`.
    let (recogSym, recogArg) ← match test with
      | .cons (.atom (.symbol s)) (.cons a .nil) => pure (s, a)
      | _ => throwError "definition: test is not a 1-arg recognizer: {repr test}"
    -- Evaluate the test argument at fuel `bcf` (needs the formal lookup).
    let targFuel := bcf - 1   -- proveConverges gives eval (targFuel+1) = eval bcf
    let (recogArgVal, hRecogArg) ← proveConverges ctx' targFuel recogArg
    -- eval (bcf+1) bodyEnv (RECOG p) = some (callBuiltin RECOG [recogArgVal]).
    let hNotSpecial ← proveNotSpecial recogSym
    let hNoDef ← proveWorldLookupNone ctx' recogSym
    let hTestRaw := mkAppN (Lean.mkConst ``evalOpt_builtin_1)
      #[mkNatLit bcf, ctx.worldExpr, bodyEnvExpr,
        reflectSymbol recogSym, reflectSExpr recogArg, recogArgVal,
        hNotSpecial, hNoDef, hRecogArg]
    -- Resolve the IF branch.
    -- Chosen branch convergence: eval (bcf+1) bodyEnv chosenB = some V.
    let (vVal, hChosen) ← proveConverges ctx' bcf chosenB
    let ifResult ←
      if isThen then
        -- Truthy: need `callBuiltin RECOG [recogArgVal] = cv` and `toBool cv = true`.
        -- The recognizer value for the then-branch must be a concrete truthy
        -- constant or come from a fact; here we resolve it structurally for
        -- `consp` of a cons form (value T) — the only truthy recognizer the
        -- base/step shapes produce without extra instrumentation.
        let callExpr ← mkAppM ``callBuiltin
          #[mkStrLit recogSym.name, ← mkListLitSExpr [recogArgVal]]
        -- The truthy constant value: try the structural consp-of-cons fact (T).
        let cExpr := reflectSExpr SExpr.t
        let hCall ← proveCallEqConst ctx' recogSym recogArg callExpr cExpr SExpr.t
        let hSomeEq ← mkAppM ``congrArg
          #[mkApp (Lean.mkConst ``Option.some [0]) (Lean.mkConst ``SExpr), hCall]
        let hTest ← mkAppM ``Eq.trans #[hTestRaw, hSomeEq]
        -- toBool T = true by decide.
        let hTruthy ← proveByDecide (← mkAppM ``Eq
          #[← mkAppM ``Logic.toBool #[cExpr], Lean.mkConst ``Bool.true])
        -- evalOpt_if_true (bcf+1) ... gives eval (bcf+2) (IF) = eval (bcf+1) thenB.
        pure <| mkAppN (Lean.mkConst ``evalOpt_if_true)
          #[mkNatLit (bcf + 1), ctx.worldExpr, bodyEnvExpr,
            reflectSExpr test, reflectSExpr thenB, reflectSExpr elseB,
            cExpr, hTest, hTruthy]
      else
        -- Nil: need `callBuiltin RECOG [recogArgVal] = nil`.
        let callExpr ← mkAppM ``callBuiltin
          #[mkStrLit recogSym.name, ← mkListLitSExpr [recogArgVal]]
        let cExpr := reflectSExpr SExpr.nil
        let hCall ← proveCallEqConst ctx' recogSym recogArg callExpr cExpr SExpr.nil
        let hSomeEq ← mkAppM ``congrArg
          #[mkApp (Lean.mkConst ``Option.some [0]) (Lean.mkConst ``SExpr), hCall]
        let hTest ← mkAppM ``Eq.trans #[hTestRaw, hSomeEq]
        -- evalOpt_if_false (bcf+1) ... gives eval (bcf+2) (IF) = eval (bcf+1) elseB.
        pure <| mkAppN (Lean.mkConst ``evalOpt_if_false)
          #[mkNatLit (bcf + 1), ctx.worldExpr, bodyEnvExpr,
            reflectSExpr test, reflectSExpr thenB, reflectSExpr elseB, hTest]
    -- Chain: eval (bcf+2) bodyEnv (IF ...) = eval (bcf+1) bodyEnv chosenB = some V.
    let hBody ← mkAppM ``Eq.trans #[ifResult, hChosen]
    -- Unfold the call: eval (bodyFuel+1) w env (fn args)
    --   = eval bodyFuel w bodyEnv body  (bodyFuel = bcf+2).
    let hDef ← proveWorldDefnLookup ctx fnSym formals body
    let hUnfold ←
      if formals.length == 1 then
        let formal := formals[0]!
        let arg := args[0]!
        let av := argVals[0]!
        let hArg := argProofs[0]!
        let hns ← proveNotSpecial fnSym
        pure <| mkAppN (Lean.mkConst ``evalOpt_defn_1)
          #[mkNatLit bodyFuel, ctx.worldExpr, ctx.envExpr,
            reflectSymbol fnSym, reflectSExpr arg, av,
            reflectSymbol formal, reflectSExpr body,
            hns, hDef, hArg]
      else
        let f1 := formals[0]!
        let f2 := formals[1]!
        let a1 := args[0]!
        let a2 := args[1]!
        let av1 := argVals[0]!
        let av2 := argVals[1]!
        let hA1 := argProofs[0]!
        let hA2 := argProofs[1]!
        let hns ← proveNotSpecial fnSym
        pure <| mkAppN (Lean.mkConst ``evalOpt_defn_2)
          #[mkNatLit bodyFuel, ctx.worldExpr, ctx.envExpr,
            reflectSymbol fnSym, reflectSExpr a1, reflectSExpr a2, av1, av2,
            reflectSymbol f1, reflectSymbol f2, reflectSExpr body,
            hns, hDef, hA1, hA2]
    -- LHS: eval (bodyFuel+1) w env (fn args) = some V.
    let hLHS ← mkAppM ``Eq.trans #[hUnfold, hBody]
    -- RHS: eval (bodyFuel+1) w env rhs = some V (both sides converge to V).
    let lhsFuel := bodyFuel + 1
    let (vRhs, hRhsRaw) ← proveConverges ctx (convergeFuel rhs) rhs
    -- Bump the RHS proof to fuel lhsFuel.
    let hRHS := mkAppN (Lean.mkConst ``evalOpt_ge_fuel)
      #[mkNatLit (convergeFuel rhs + 1), mkNatLit lhsFuel, ctx.worldExpr, ctx.envExpr,
        reflectSExpr rhs, vRhs, hRhsRaw, ← mkGeProof lhsFuel (convergeFuel rhs + 1)]
    -- The two value Exprs (vVal from the LHS branch, vRhs from RHS) must be the
    -- same value. We retype both `= some <vVal>` so mkFuelEqExist sees one V.
    let someVVal := mkApp2 (Lean.mkConst ``Option.some [0]) (Lean.mkConst ``SExpr) vVal
    let lhsEvalTy ← mkAppM ``Eq
      #[mkAppN (Lean.mkConst ``evalOpt)
          #[mkNatLit lhsFuel, ctx.worldExpr, ctx.envExpr, reflectSExpr lhs], someVVal]
    let rhsEvalTy ← mkAppM ``Eq
      #[mkAppN (Lean.mkConst ``evalOpt)
          #[mkNatLit lhsFuel, ctx.worldExpr, ctx.envExpr, reflectSExpr rhs], someVVal]
    let hLHS' ← mkExpectedTypeHint hLHS lhsEvalTy
    let hRHS' ← mkExpectedTypeHint hRHS rhsEvalTy
    -- Wrap into ∃ N, ∀ f ≥ N, eval (fn args) = eval rhs.
    mkFuelEqExistE ctx lhsFuel lhs rhs vVal hLHS' hRHS'

  /-- Prove `w.defs.get? fnSym = some (formals, body)` by simp + world unfold. -/
  proveWorldDefnLookup (ctx : ProofCtx) (fnSym : Symbol)
      (formals : List Symbol) (body : SExpr) : MetaM Expr := do
    let worldDefs := mkApp (Lean.mkConst ``World.defs) ctx.worldExpr
    let lookupExpr ← mkAppM ``Std.HashMap.get? #[worldDefs, reflectSymbol fnSym]
    let pairExpr := mkApp4 (Lean.mkConst ``Prod.mk [0, 0])
      (← mkAppM ``List #[Lean.mkConst ``Symbol]) (Lean.mkConst ``SExpr)
      (reflectSymbolList formals) (reflectSExpr body)
    let pairTy ← inferType pairExpr
    let someE := mkApp2 (Lean.mkConst ``Option.some [0]) pairTy pairExpr
    proveBySimp (← mkAppM ``Eq #[lookupExpr, someE])
      (unfoldNames := ctx.worldUnfoldNames) (useDecide := true)

  /-- `mkFuelEqExist` accepting value Exprs directly (rather than reflecting a
      `SExpr v`). Same construction as `mkFuelEqExist` but `v` is an Expr. -/
  mkFuelEqExistE (ctx : ProofCtx) (N : Nat) (a b : SExpr) (vE : Expr)
      (hA hB : Expr) : MetaM Expr := do
    let NE := mkNatLit N
    let aE := reflectSExpr a
    let bE := reflectSExpr b
    let pred ← mkFuelPredE ctx aE fun fVar =>
      mkAppN (Lean.mkConst ``evalOpt) #[fVar, ctx.worldExpr, ctx.envExpr, bE]
    withLocalDeclD `f (Lean.mkConst ``Nat) fun fVar => do
      let geType ← mkAppM ``GE.ge #[fVar, NE]
      withLocalDeclD `hf geType fun hfVar => do
        let geA := mkAppN (Lean.mkConst ``evalOpt_ge_fuel)
          #[NE, fVar, ctx.worldExpr, ctx.envExpr, aE, vE, hA, hfVar]
        let geB := mkAppN (Lean.mkConst ``evalOpt_ge_fuel)
          #[NE, fVar, ctx.worldExpr, ctx.envExpr, bE, vE, hB, hfVar]
        let eqProof ← mkAppM ``Eq.trans #[geA, ← mkAppM ``Eq.symm #[geB]]
        let body ← mkLambdaFVars #[fVar, hfVar] eqProof
        return mkApp4 (Lean.mkConst ``Exists.intro [1])
          (Lean.mkConst ``Nat) pred NE body

  /-- `mkFuelPred` inlined into the where-block (private top-level `mkFuelPred`
      is not in scope here). -/
  mkFuelPredE (ctx : ProofCtx) (aExpr : Expr) (mkRhs : Expr → Expr) :
      MetaM Expr := do
    withLocalDeclD `N (Lean.mkConst ``Nat) fun nVar => do
      withLocalDeclD `f (Lean.mkConst ``Nat) fun fVar => do
        let geType ← mkAppM ``GE.ge #[fVar, nVar]
        withLocalDeclD `hf geType fun hfVar => do
          let lhsEval := mkAppN (Lean.mkConst ``evalOpt)
            #[fVar, ctx.worldExpr, ctx.envExpr, aExpr]
          let eqType ← mkAppM ``Eq #[lhsEval, mkRhs fVar]
          let forall_ ← mkForallFVars #[fVar, hfVar] eqType
          mkLambdaFVars #[nVar] forall_

  /-- Prove `m ≥ n` for concrete Nat literals (m ≥ n) by decide. -/
  mkGeProof (m n : Nat) : MetaM Expr := do
    proveByDecide (← mkAppM ``GE.ge #[mkNatLit m, mkNatLit n])

/-- Does `a` occur as a subterm of `term`? -/
partial def occursIn (a term : SExpr) : Bool :=
  term == a || match term with
    | .cons x y => occursIn a x || occursIn a y
    | _ => false

/-- Reflect a `List SExpr` as a Lean `Expr` of type `List SExpr`. -/
def reflectSExprList : List SExpr → Expr
  | [] => mkApp (Lean.mkConst ``List.nil [0]) (Lean.mkConst ``SExpr)
  | x :: xs => mkApp3 (Lean.mkConst ``List.cons [0]) (Lean.mkConst ``SExpr)
      (reflectSExpr x) (reflectSExprList xs)

/-- Prove `s.isNamed name = false` by decision. -/
def proveIsNamedFalse (s : Symbol) (name : String) : MetaM Expr :=
  proveByDecide (mkApp3 (Lean.mkConst ``Eq [1]) (Lean.mkConst ``Bool)
    (mkApp2 (Lean.mkConst ``Symbol.isNamed) (reflectSymbol s) (mkStrLit name))
    (Lean.mkConst ``Bool.false))

/-- Lift a node proof `∃ N, ∀ f ≥ N, eval a = eval b` to the enclosing term:
    given `term` containing `a` at an evaluation (function-argument) position,
    produce the rewritten term and a proof
    `∃ N, ∀ f ≥ N, eval term = eval (term with first occurrence of a → b)`.
    Composes `evalOpt_arg_congr` from the outside in. Hard-fails if the target
    sits in a non-evaluation position (QUOTE/IF/LET) — those are resolved by
    a child node, not a literal-chain rewrite. -/
partial def liftCongr (ctx : ProofCtx) (term a b : SExpr) (innerProof : Expr) :
    MetaM (SExpr × Expr) := do
  if term == a then
    return (b, innerProof)
  else match term with
  | .cons (.atom (.symbol s)) argsExpr =>
    if s.isNamed "quote" then
      throwError "liftCongr: rewrite target inside QUOTE: {repr term}"
    else if s.isNamed "if" || s.isNamed "let" || s.isNamed "let*" then
      throwError "liftCongr: rewrite target inside IF/LET (should be a child): {repr term}"
    else
      let some args := argsExpr.toList?
        | throwError "liftCongr: malformed argument list in {repr term}"
      let some i := args.findIdx? (occursIn a)
        | throwError "liftCongr: target {repr a} not found in {repr term}"
      let before := args.take i
      let after := args.drop (i + 1)
      let argTerm := args[i]!
      let (newArg, argProof) ← liftCongr ctx argTerm a b innerProof
      let proof := mkAppN (Lean.mkConst ``evalOpt_arg_congr)
        #[ctx.worldExpr, ctx.envExpr, reflectSymbol s,
          reflectSExprList before, reflectSExprList after,
          reflectSExpr argTerm, reflectSExpr newArg,
          ← proveIsNamedFalse s "quote", ← proveIsNamedFalse s "if",
          ← proveIsNamedFalse s "let", ← proveIsNamedFalse s "let*", argProof]
      return (.cons (.atom (.symbol s)) (SExpr.ofList (before ++ newArg :: after)), proof)
  | _ => throwError "liftCongr: target not at an evaluation position: {repr term}"

/-- Compose a chain of node proofs for a literal.
    Given nodes `[n1, n2, ..., nk]` and the literal term,
    produces `∃ N, ∀ f ≥ N, evalOpt f w env literal = some T`.

    Each node proves `eval lhs_i = eval rhs_i`; `liftCongr` lifts it to the
    enclosing term (finding the rewrite position automatically), and
    `fuel_chain_eq` composes successive steps. -/
def proveLiteralChain (ctx : ProofCtx) (literal : SExpr)
    (nodes : List ProofNode) : MetaM Expr := do
  let mut currentTerm := literal
  let mut chainProof : Option Expr := none

  for node in nodes do
    match node with
    | .node _ nodeLhs nodeRhs _ _ =>
      -- The node proves: ∃ N, ∀ f ≥ N, eval nodeLhs = eval nodeRhs
      let nodeProof ← proveNode ctx node
      -- Lift to the enclosing term at the rewrite position, then chain.
      let (newTerm, stepProof) ← liftCongr ctx currentTerm nodeLhs nodeRhs nodeProof
      match chainProof with
      | none => chainProof := some stepProof
      | some prev =>
        chainProof := some (← mkAppM ``fuel_chain_eq #[prev, stepProof])
      currentTerm := newTerm

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

/-! ## Theorem declaration -/

/-- Produce a Lean theorem from a proof tree.
    Given a world, formula, and list of proof nodes (one literal's chain),
    adds `theorem <name> (env : Env) : ∃ N, ∀ f ≥ N, evalOpt f w env formula = some T`
    to the Lean environment. The proof is kernel-checked. -/
def addTheoremFromChain (worldExpr : Expr) (world : World)
    (worldUnfoldNames : Array Name)
    (formula : SExpr) (nodes : List ProofNode)
    (declName : Name) : TermElabM Unit := do
  let envType ← Term.elabTerm (← `(Env)) none
  withLocalDeclD `env envType fun envVar => do
    let ctx : ProofCtx := {
      worldExpr := worldExpr
      world := world
      envExpr := envVar
      worldUnfoldNames := worldUnfoldNames
    }
    let proofBody ← proveLiteralChain ctx formula nodes
    let proof ← mkLambdaFVars #[envVar] proofBody
    let thmType ← mkForallFVars #[envVar] (← inferType proofBody)
    addDecl (.thmDecl {
      name := declName
      levelParams := []
      type := thmType
      value := proof
    })

end ACL2.Replay.ProofProducer
