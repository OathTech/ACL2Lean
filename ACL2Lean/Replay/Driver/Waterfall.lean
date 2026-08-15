/-
  Driver/Waterfall — split from Driver/Core (WP2 Stage 3a, 2026-07-17;
  see docs/plans/2026-07-18_driver-modular-refactor.md).

  The c3 induction scaffold (CaseTree, measures, covering clauses) and the
  ClauseRec recursion interface shared by all waterfall processor modules.
-/
import ACL2Lean.Replay.Driver.Preprocess

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-! ## The c3 induction scaffold + the conditional-replayed-statement harness

The WF-induction scaffold consumes the EMITTED justification (measure / rel /
controllers / per-case tests + IH substitutions — the measure-emission track's
output) and instantiates `acl2_induction_consp` (strong induction on
`SExpr.consCount` — the well-foundedness construction Lean owns; everything else
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

/-- The ARGS-VALUED TP-corollary hypothesis TYPE (G1 arc 2026-07-29):
    `∀ env' args… (u₀…uₙ v : SExpr),
       (∃N∀f≥N, eval env' aᵢ = some uᵢ) → … →
       (∃N∀f≥N, eval env' (fn args) = some v) →
       <corollary lifted, (fn formals) ↦ v, formalᵢ ↦ uᵢ> = t`.
    The value-only shape (`mkTpHypType`) cannot state a corollary whose
    residue mentions a formal BARE (the BINARY-APPEND/my-app
    `(EQUAL (fn X Y) Y)` disjunct class); binding the argument VALUES lifts
    exactly those occurrences. Offered only when the value-only lift fails
    (existing hypothesis shapes unchanged). -/
def mkTpHypTypeAv (cfg : ReplayConfig) (fn : Symbol) (formals : List Symbol)
    (cor : SExpr) : MetaM Expr := do
  withLocalDeclD `env' (mkConst ``ACL2.Env) fun envV => do
    let decls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
      (Array.range formals.length).map fun i =>
        (Name.mkSimple s!"a{i}", .default, fun _ => pure (mkConst ``SExpr))
    withLocalDecls decls fun argVs => do
      let udecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
        (Array.range formals.length).map fun i =>
          (Name.mkSimple s!"u{i}", .default, fun _ => pure (mkConst ``SExpr))
      withLocalDecls udecls fun uVs => do
        withLocalDeclD `v (mkConst ``SExpr) fun vV => do
          let appT := mkAppListExpr fn argVs
          let argPrems ← (argVs.zip uVs).toList.mapM fun (aV, uV) =>
            mkValConvPropEx cfg.worldExpr envV aV uV
          let prem ← mkValConvPropEx cfg.worldExpr envV appT vV
          let appPat : SExpr :=
            .cons (.atom (.symbol fn))
              ((formals.map (SExpr.atom ∘ Atom.symbol)).foldr SExpr.cons .nil)
          let lifted ← dpValExpr [(appPat, vV)]
            (fun s => match formals.findIdx? (· == s) with
              | some i => pure uVs[i]!
              | none => throwError "mkTpHypTypeAv: corollary of {fn.name} has a \
                  free variable {s.name} outside the application/formals (frontier)")
            cor
          let concl ← mkEq lifted (mkConst ``SExpr.t)
          let body ← (argPrems ++ [prem]).foldrM (fun h acc => mkArrow h acc) concl
          mkForallFVars (#[envV] ++ argVs ++ uVs ++ #[vV]) body

/-- The theorem-dependency hypothesis TYPE for a STORED rewrite rule
    (`rule:<thm>`, the `equal` instance — the rule's own `:EQUIV`; a
    non-`equal` rule is a frontier at the USE site, `replayNode`):
    `∀ env', EvTrue w env' h₁ → … → ∃N ∀f≥N, eval env' lhs = eval env' rhs`.
    The premises are TRUTHINESS (ACL2 relieves hyps under iff), the conclusion
    the rule's stored equality — exactly the emitted rule, nothing else
    (docs/plans/2026-07-05_theorem-dependency-hypotheses.md §v1). -/
def mkRuleHypType (cfg : ReplayConfig) (spec : RuleSpec) : MetaM Expr := do
  -- defense-in-depth (audit 2026-07-06 finding E): stating an iff rule as an
  -- eval-EQUALITY would be too strong — refuse rather than mis-state. A USER
  -- equivalence rule (G2 rung 2) gets the INTERPRETED-relation conclusion
  -- instead: `EvTrue env' (R lhs rhs)` over the world's own R defun (design
  -- 2026-07-29 §1 — never re-model what the interpreter defines); the offer
  -- site admits it only when R names a world-defined binary fn.
  withLocalDeclD `env' (mkConst ``ACL2.Env) fun envV => do
    let concl ←
      if spec.equiv == "equal" then
        mkEvalEqPropEx cfg.worldExpr envV
          (reflectSExpr spec.lhs) (reflectSExpr spec.rhs)
      else do
        let rSym : Symbol := { name := spec.equiv.map Char.toUpper }
        let some (formals, _) := cfg.worldVal.defs.get? rSym
          | throwError "mkRuleHypType: rule {spec.name} is stored under \
              equivalence {spec.equiv}, which names no world-defined fn — \
              the interpreted-relation shape needs the defun (offer-site \
              filter breach)"
        unless formals.length == 2 do
          throwError "mkRuleHypType: equivalence {spec.equiv} has arity \
              {formals.length}, not 2"
        let relApp : SExpr := .cons (.atom (.symbol rSym))
          (.cons spec.lhs (.cons spec.rhs .nil))
        pure (mkAppN (mkConst ``EvTrue)
          #[cfg.worldExpr, envV, reflectSExpr relApp])
    let body ← spec.hyps.foldrM (fun h acc => do
      mkArrow (mkAppN (mkConst ``EvTrue) #[cfg.worldExpr, envV, reflectSExpr h]) acc)
      concl
    mkForallFVars #[envV] body

/-- The `linear:<rune>` hypothesis TYPE for a cited ground-zero :LINEAR
    rule (sorting-absolute 2b): schematic over the ambient env exactly
    like `mkRuleHypType`'s premise chain, concluding the rule's stored
    conclusion as `EvTrue` — `∀ env', EvTrue w env' h₁ → … →
    EvTrue w env' concl`. The stored fields are EMITTED verbatim
    (`(:GROUND-ZERO-LINEAR-RULES …)`); nothing is normalized. Consumed by
    `replayDischargeNode` as a DP-obligation premise; discharged
    Imported-side (the acl2CountExec-class kits) or kept as an honest
    D6 condition. -/
def mkLinearHypType (cfg : ReplayConfig) (spec : LinearRuleSpec) :
    MetaM Expr := do
  withLocalDeclD `env' (mkConst ``ACL2.Env) fun envV => do
    let concl := mkAppN (mkConst ``EvTrue)
      #[cfg.worldExpr, envV, reflectSExpr spec.concl]
    let body ← spec.hyps.foldrM (fun h acc => do
      mkArrow (mkAppN (mkConst ``EvTrue)
        #[cfg.worldExpr, envV, reflectSExpr h]) acc) concl
    mkForallFVars #[envV] body

/-- The `cong:<thm>` hypothesis TYPE for a congruence-shaped defthm (G2
    rung 2): the WHOLE formula's replayed statement, `∀ env', EvTrue w env' formula` —
    exactly the theorem, no normalization. Consumed by the R-collapse at a
    user-equivalence step's congruence frame; discharged from the
    dependency's replayed statement like `rule:` hypotheses. -/
def mkCongHypType (cfg : ReplayConfig) (spec : CongSpec) : MetaM Expr := do
  withLocalDeclD `env' (mkConst ``ACL2.Env) fun envV => do
    mkForallFVars #[envV]
      (mkAppN (mkConst ``EvTrue) #[cfg.worldExpr, envV, reflectSExpr spec.formula])

/-- The `use:<thm>` hypothesis TYPE (R7a): the cited theorem's
    whole-formula replayed statement, `∀ env', EvTrue w env' formula` —
    exactly the theorem, no normalization (the `cong:` shape without the
    congruence parse). -/
def mkUseHypType (cfg : ReplayConfig) (spec : UseSpec) : MetaM Expr := do
  withLocalDeclD `env' (mkConst ``ACL2.Env) fun envV => do
    mkForallFVars #[envV]
      (mkAppN (mkConst ``EvTrue) #[cfg.worldExpr, envV, reflectSExpr spec.formula])

/-- The `tpthm:<thm>` hypothesis TYPE (the first :CLASSES consumer): a
    THEOREM-classed :TYPE-PRESCRIPTION rule's whole-formula replayed
    statement, `∀ env', EvTrue w env' formula`. -/
def mkTpThmHypType (cfg : ReplayConfig) (spec : TpThmSpec) : MetaM Expr := do
  withLocalDeclD `env' (mkConst ``ACL2.Env) fun envV => do
    mkForallFVars #[envV]
      (mkAppN (mkConst ``EvTrue) #[cfg.worldExpr, envV, reflectSExpr spec.formula])

/-- The `equivfull:<thm>` hypothesis TYPE (the R-solidify lane): the
    equivalence theorem's whole TRANSLATED Goal statement,
    `∀ env', EvTrue w env' formula` — all four defequiv conjuncts, consumed
    by the equivalence-rune own-position congruence. -/
def mkEquivFullHypType (cfg : ReplayConfig) (spec : EquivFullSpec) :
    MetaM Expr := do
  withLocalDeclD `env' (mkConst ``ACL2.Env) fun envV => do
    mkForallFVars #[envV]
      (mkAppN (mkConst ``EvTrue) #[cfg.worldExpr, envV, reflectSExpr spec.formula])

/-- The `equivrefl:<thm>` hypothesis TYPE: the equivalence rule's
    reflexivity component, `∀ env', EvTrue w env' (R x x)`. -/
def mkEquivReflHypType (cfg : ReplayConfig) (spec : EquivReflSpec) : MetaM Expr := do
  let rxx : SExpr := .cons (.atom (.symbol spec.rel))
    (.cons (.atom (.symbol spec.vx)) (.cons (.atom (.symbol spec.vx)) .nil))
  withLocalDeclD `env' (mkConst ``ACL2.Env) fun envV => do
    mkForallFVars #[envV]
      (mkAppN (mkConst ``EvTrue) #[cfg.worldExpr, envV, reflectSExpr rxx])

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
      | .useHint hyps ccl appC _lmis => hyps ++ ccl ++ appC.flatMap id
      | .fcDerivations _ => []
      | .complementClose lit => [lit]
      | .dedupDrop lit => [lit]
      | .taSubst n f _ sn so => [n, f, sn, so]
      | .branch _ items => items.flatMap goI
    goI it
  cn.inputClause ++ cn.steps.flatMap (·.items.flatMap itemTerms)
    ++ cn.children.flatMap clauseSubtreeTerms

/-- The decision tree recovered from the cases' ruling-test lists (ACL2's
    induction machine derives the cases from the scheme function's
    if-structure, so the test lists always form a binary split tree). Leaves
    carry the case INDEX into `ind.cases`. -/
inductive CaseTree where
  | leaf (caseIdx : Nat)
  | split (test : SExpr) (pos neg : CaseTree)
  deriving Repr

/-- Recover the decision tree. Each input is `(caseIdx, remaining tests)`;
    at each level all nonempty heads must be the same test up to negation.
    Hard-fails on anything else (no inference — the structure is validated,
    never guessed). -/
partial def buildCaseTree (cases : List (Nat × List SExpr)) :
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
        if ns.name == "NOT" then u else t0
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
structure TestFact where
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
      if q.isNamed "QUOTE" then t
      else .cons (.atom (.symbol q)) (elimSpine rest)
    | _ => t
where
  elimSpine : SExpr → SExpr
    | .cons a rest => .cons (elimReplace carT cdrT vT uT v1 v2 a) (elimSpine rest)
    | t => t

/-- I1 μ-REGISTRY (induction-generality design, J2): build the TOTAL
    meta-level `Env → Nat` interpretation of an emitted measure term.

    R3 (T1+2 sprint phase 2, 2026-08-14): the row set is the UNIFIED
    measure table (`Replay/MeasureTable.lean` + `MeasureShape.muHeads`),
    shared with `proveTotality`/`proveTp`'s admission gates,
    `dischargeDecrease`'s walk dispatch and `derive_exec%`'s
    `MeasurePos` — the four fragments the overspecialization audit's
    F6/F7/F8 found classifying measures independently. An UNREGISTERED
    shape hard-fails: a loud frontier, never a default. The measure
    appears in NO statement (design I1's trust observation): μ is proof
    bookkeeping, so a registry gap can only fail a proof. -/
def buildMeasureFn (measure : SExpr) : MetaM Expr := do
  let some sh := measureShape? measure
    | throwError "μ-registry: measure shape {repr measure} not registered \
                  (frontier)"
  let some heads := sh.muHeads
    | throwError "μ-registry: measure head {sh.headName} has no \
                  trusted-core Nat interpretation — only the \
                  recorded-termination route interprets a user measure fn \
                  (frontier)"
  unless heads.length == sh.vars.length do
    throwError "μ-registry: row {sh.headName} has {heads.length} μ head(s) \
                for {sh.vars.length} measured variable(s) (internal)"
  withLocalDeclD `env (mkConst ``ACL2.Env) fun envV => do
    let comps ← (sh.vars.zip heads).mapM fun (v, fn) => do
      mkAppM fn #[← dpConcVar envV v]
    match comps with
    | [] => throwError "μ-registry: row {sh.headName} has no measured \
                        variables (internal)"
    | c0 :: rest => do
      let body ← rest.foldlM (fun acc c => mkAppM ``HAdd.hAdd #[acc, c]) c0
      mkLambdaFVars #[envV] body

/-- I4 COVERING JOIN (J2): the IH's measured-subset substitution must be
    covered by an EMITTED termination clause of the scheme fn, instantiated
    by ACL2's own flesh-out — `sublis-var (pairlis$ formals (fargs term))`
    (theory-audit OUT-3; the measured actuals are DISTINCT VARIABLES by
    ACL2's sound-induction condition, enforced here, never assumed). The
    expected decrease literal is `(O< measureσ measure)` with σ the alist
    restricted to the measured variables; a clause containing it must exist.
    Never an obligation ACL2 did not emit — no cover, hard-fail. -/
def checkCoveringClause (cfg : ReplayConfig) (ind : InductionStep)
    (alist : List (Symbol × SExpr)) (measuredVars : List Symbol) :
    MetaM Unit := do
  let .cons (.atom (.symbol fn)) argSpine := ind.term
    | throwError "replayInduction: induction term {repr ind.term} is not an \
                  application (frontier)"
  let some actuals := argSpine.toList?
    | throwError "replayInduction: induction term args not a list (frontier)"
  -- scheme fn formals: the world, or — for a builtin-named scheme fn,
  -- world-EXCLUDED by no-shadow (e.g. LEN) — its ground-zero snapshot
  let some formals :=
      ((cfg.worldVal.defs.get? fn).map (·.1)).orElse
        (fun _ => (cfg.gzDefs.find? (·.1 == fn)).map (·.2.1))
    | throwError "replayInduction: scheme fn {fn.name} neither in the world \
                  nor a ground-zero snapshot (frontier)"
  unless formals.length == actuals.length do
    throwError "replayInduction: induction term arity mismatch (frontier)"
  -- the flesh-out renaming; measured ACTUALS must be distinct variables
  let mAlist := alist.filter (fun (v, _) => measuredVars.contains v)
  let mVarsOfActuals := (formals.zip actuals).filterMap fun (f, a) =>
    match a with
    | .atom (.symbol s) => if measuredVars.contains s then some (f, s) else none
    | _ => none
  let measuredActuals := mVarsOfActuals.map (·.2)
  unless measuredVars.all (measuredActuals.contains ·) do
    throwError "replayInduction: a measured variable is not a distinct-\
                variable actual of the induction term (sound-induction \
                condition — frontier)"
  let some j := cfg.justs.lookup fn.name
    | throwError "replayInduction: no emitted justification for scheme fn \
                  {fn.name} (emission gap — frontier)"
  let expected : SExpr :=
    .cons (.atom (.symbol { name := "O<" }))
      (.cons (ACL2.Replay.substTerm (mAlist.map (·.1)) (mAlist.map (·.2))
        ind.measure)
      (.cons ind.measure .nil))
  -- rename PER LITERAL: a clause sexpr's head is a literal (a cons), which
  -- `substTerm`'s application arm does not enter — map over the literal list
  let renamed ← j.terminationClauses.mapM fun cl =>
    match cl.toList? with
    | some lits => pure (lits.map (ACL2.Replay.substTerm formals actuals))
    | none => throwError "checkCoveringClause: malformed emitted termination \
                clause (not a list): {repr cl}"
  unless renamed.any (fun lits => lits.contains expected) do
    throwError "replayInduction: IH substitution {repr mAlist} has no \
                covering emitted termination clause (expected decrease \
                {repr expected}) — never an obligation ACL2 did not emit \
                (frontier)"


/-- The clause-level recursion interface (WP2 Stage 2): the waterfall
    knot's entry points as a record. Every processor and the spine/clause
    walkers are top-level defs taking `rec` — the knot is tied ONCE below
    (`replayClause`/`replayClauseSpine`, public names and signatures
    unchanged from the pre-WP2 mutual). -/
structure ClauseRec where
  /-- `replayClause` — the per-clause waterfall dispatcher. -/
  clause : ReplayConfig → ReplayCtx → ClauseNode → MetaM Expr
  /-- `replayClauseSpine` — the literal-spine walker. -/
  clauseSpine : ReplayConfig → ReplayCtx → String → List (Nat × SExpr) →
    List ClauseItem → List SExpr → List ClauseNode → MetaM Expr

end ACL2.Replay.Driver
