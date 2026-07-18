/-
  Driver/Core — split from the monolithic Driver.lean (WP2 Stage 1,
  2026-07-17; see docs/plans/2026-07-18_driver-modular-refactor.md).

  The c3 induction scaffold, the clause-level waterfall knot
  (replayClauseSpine/composeSplit/replayClause + processors), and the
  conditional-mirror harness.
-/
import ACL2Lean.Replay.Driver.Preprocess

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

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
      if q.isNamed "QUOTE" then t
      else .cons (.atom (.symbol q)) (elimSpine rest)
    | _ => t
where
  elimSpine : SExpr → SExpr
    | .cons a rest => .cons (elimReplace carT cdrT vT uT v1 v2 a) (elimSpine rest)
    | t => t

/-- I1 μ-REGISTRY (induction-generality design, J2): build the TOTAL
    meta-level `Env → Nat` interpretation of an emitted measure term.
    Registered heads: `ACL2-COUNT` (of a variable) ↦ `SExpr.acl2Count` of
    the env value; `BINARY-+` ↦ `Nat.add`. An UNKNOWN head hard-fails — a
    loud frontier, never a default (extension is additive registration).
    The measure appears in NO statement (design I1's trust observation):
    μ is proof bookkeeping, so a registry gap can only fail a proof. -/
partial def buildMeasureFn (measure : SExpr) : MetaM Expr := do
  withLocalDeclD `env (mkConst ``ACL2.Env) fun envV => do
    mkLambdaFVars #[envV] (← go envV measure)
where
  go (envV : Expr) : SExpr → MetaM Expr
    | .cons (.atom (.symbol h)) (.cons arg .nil) => do
      unless h.name == "ACL2-COUNT" do
        throwError "μ-registry: unary measure head {h.name} not registered \
                    (frontier)"
      let .atom (.symbol v) := arg
        | throwError "μ-registry: (ACL2-COUNT {repr arg}) — non-variable \
                      measured argument (frontier)"
      mkAppM ``SExpr.acl2Count #[← dpConcVar envV v]
    | .cons (.atom (.symbol h)) (.cons m1 (.cons m2 .nil)) => do
      unless h.name == "BINARY-+" do
        throwError "μ-registry: binary measure head {h.name} not registered \
                    (frontier)"
      mkAppM ``HAdd.hAdd #[← go envV m1, ← go envV m2]
    | m => throwError "μ-registry: measure shape {repr m} not registered \
                       (frontier)"

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
partial def composeSplit (rec : ClauseRec) (cfg : ReplayConfig) (ctx : ReplayCtx) (idStr : String)
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
      let p ← composeSplit rec cfg ctx idStr lp chainOpt clauseLit restLits branches
        accClause children (facts ++ [(T, vT, false, hNil)]) fSide
      mkLambdaFVars #[hNil] p
    let posL ← withLocalDeclD `hne (← mkAppM ``Ne #[vT, nilC]) fun hNe => do
      let p ← composeSplit rec cfg ctx idStr lp chainOpt clauseLit restLits branches
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
          unless eqS.name == "EQUAL" do
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
    composeSplit rec cfg ctx idStr lp chainOpt clauseLit restLits branches
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
          if ns.name == "NOT" then
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
          | .step n => (runeOf n).ty == "context-subst"
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
      let pChild ← rec.clause cfg ctx child
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
            if ns.name == "NOT" then
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
          | .step n => (runeOf n).ty == "context-subst"
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
            let pChild ← rec.clause cfg ctx child
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
              | .step n => (runeOf n).ty == "context-subst"
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
            rec.clauseSpine cfg ctx' idStr restLits cont' accClause' children
        mkLambdaFVars #[h] p
      mkAppM ``evtrue_dp_if_split
        #[w, e, reflectSExpr clauseLit, reflectSExpr quoteT, reflectSExpr restTerm,
          vLit, pLit, hthen, helse]

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
partial def replayElim (rec : ClauseRec) (cfg : ReplayConfig) (ctx : ReplayCtx) (cn : ClauseNode)
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
  let some [.atom (.keyword "ELIM"), .atom (.symbol runeName)] := runeS.toList?
    | throwError "replayElim: elim record rune {repr runeS} at {cn.idStr}"
  unless runeName.name == "CAR-CDR-ELIM" do
    throwError "replayElim: elim rule {runeName.name} ≠ car-cdr-elim at \
                {cn.idStr} (frontier)"
  let .atom (.symbol v) := varS
    | throwError "replayElim: eliminated var {repr varS} at {cn.idStr}"
  let .cons (.atom (.symbol consS))
      (.cons (.atom (.symbol v1)) (.cons (.atom (.symbol v2)) .nil)) := targetS
    | throwError "replayElim: elim target {repr targetS} is not (cons v1 v2) \
                  at {cn.idStr}"
  unless consS.name == "CONS" && v1 != v2 && v1 != v && v2 != v do
    throwError "replayElim: elim target vars ({consS.name} {v1.name} {v2.name}) \
                at {cn.idStr}"
  let vT : SExpr := .atom (.symbol v)
  let carT : SExpr := .cons (.atom (.symbol { name := "CAR" })) (.cons vT .nil)
  let cdrT : SExpr := .cons (.atom (.symbol { name := "CDR" })) (.cons vT .nil)
  let uT : SExpr := .cons (.atom (.symbol { name := "CONS" }))
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
  let lit1 : SExpr := .cons (.atom (.symbol { name := "NOT" }))
    (.cons (.cons (.atom (.symbol { name := "CONSP" })) (.cons vT .nil)) .nil)
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
    let pChild ← rec.clause cfg' ctx' child
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
    let uSig : SExpr := .cons (.atom (.symbol { name := "CONS" }))
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
partial def replayGeneralize (rec : ClauseRec) (cfg : ReplayConfig) (ctx : ReplayCtx) (cn : ClauseNode)
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
  let some termsS := plistLookup "TERMS" genS
    | throwError "replayGeneralize: :GENERALIZE without :TERMS at {cn.idStr}"
  let some varsS := plistLookup "VARS" genS
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
  let pChild ← rec.clause cfg' ctx' child
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
partial def replaySubsumed (rec : ClauseRec) (cfg : ReplayConfig) (ctx : ReplayCtx)
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
  let pChild ← rec.clause cfg' ctx' child
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
partial def replayEliminateIrrelevance (rec : ClauseRec) (cfg : ReplayConfig) (ctx : ReplayCtx)
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
  let pChild ← rec.clause cfg ctx child
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

/-- Replay an INDUCTION pool-root from its EMITTED justification
    (REWIRED at J2 — induction-generality design §I1–I5, spike-validated by
    `Imported/FlattenSpike.lean` and `Imported/InterleaveSpike.lean`):
    the motive is ENV-LEVEL (`P env := EvTrue w env ⟪pushed⟫`) under strong
    induction on the μ-registry interpretation of the EMITTED measure term
    (`measure_strong_induction`); cases follow the emitted decision tree;
    each emitted IH alist instantiates the ONE strong hypothesis at the
    updated env (swaps and ride-along substitutions are plain env updates),
    justified by a decrease covered by the scheme fn's emitted termination
    clauses (`checkCoveringClause`) and discharged from the case's ruling
    facts by the Count library. J2's DISCHARGE FRAGMENT: single measured
    variable with `(CDR v)`/`(CAR v)` substitution under a direct
    `(consp v)`/`(not (endp v))` ruling fact; compound-test inversion is J3,
    sum-measure discharge is J4 — both hard-fail here until then. -/
partial def replayInduction (rec : ClauseRec) (cfg : ReplayConfig) (ctx : ReplayCtx) (cn : ClauseNode) :
    MetaM Expr := do
  let some ind := cn.induction | throwError "replayInduction: no induction"
  -- 1. validate the justification shape (J2: μ-registry + T3 + I4 covering)
  let μE ← buildMeasureFn ind.measure
  let relOk := match ind.rel with
    | .atom (.symbol r) => r.name == "O<"
    | _ => false
  unless relOk do throwError "replayInduction: rel {repr ind.rel} ≠ o< (frontier)"
  -- T3 (theory audit): measured subset := free vars of the FLESHED-OUT
  -- measure term; must be ⊆ the emitted :CONTROLLERS
  let measuredVars := ACL2.Replay.freeVars ind.measure
  if measuredVars.isEmpty then
    throwError "replayInduction: measure {repr ind.measure} has no measured \
                variables (frontier)"
  unless measuredVars.all (ind.controllers.contains ·) do
    throwError "replayInduction: measured vars {repr measuredVars} ⊄ \
                :CONTROLLERS {repr ind.controllers} (T3 — frontier)"
  -- 2. per-case validation: distinct alist vars; every IH's measured
  -- substitution covered by an EMITTED termination clause (I4)
  for c in ind.cases do
    if c.tests.isEmpty then
      throwError "replayInduction: a case has no ruling tests (frontier)"
    for alist in c.alists do
      let vars := alist.map (·.1)
      unless vars.eraseDups.length == vars.length do
        throwError "replayInduction: IH alist vars {repr vars} not distinct"
      checkCoveringClause cfg ind alist measuredVars
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
  -- 4. P : Env → Prop — the pushed pool entry's truth at the ambient env
  -- (J2, design I2: the ENV-LEVEL motive — spike-validated)
  let P ← withLocalDeclD `e (mkConst ``ACL2.Env) fun eV => do
    mkLambdaFVars #[eV] (← mkAppM ``EvTrue #[w, eV, pushedE])
  let conspOf := fun (v : Expr) => mkApp (mkConst ``Logic.consp) v
  let hNoLet ← proveByDecide
    (← mkEq (← mkAppM ``ACL2.Replay.NoLet #[pushedE]) (mkConst ``Bool.true))
    "NoLet pushed"
  -- 5. the strong-induction STEP: ∀ e, (∀ e', μ e' < μ e → P e') → P e,
  -- dispatching the emitted decision tree.
  let step ← withLocalDeclD `e (mkConst ``ACL2.Env) fun eV => do
    let sihTy ← withLocalDeclD `e2 (mkConst ``ACL2.Env) fun e2V => do
      let lt ← mkAppM ``LT.lt #[(mkApp μE e2V).headBeta, (mkApp μE eV).headBeta]
      mkForallFVars #[e2V] (← mkArrow lt (mkApp P e2V).headBeta)
    let inner ← withLocalDeclD `sih sihTy fun sihV => do
          let cfg' := { cfg with envExpr := eV }
          let ctx0 : ReplayCtx :=
            { ctx with varVals := [], vals := [], litFacts := [] }
          -- ONE IH's truth: instantiate the strong IH at the UPDATED env —
          -- every alist pair is a plain env update (swaps and arbitrary
          -- ride-along terms included, design I3) — and bridge to this env
          -- by substN: EvTrue of the σ-instance of the pushed DISJUNCTION
          let ihDisjTruth (ctxD : ReplayCtx) (facts : List TestFact)
              (alist : List (Symbol × SExpr)) :
              MetaM (ReplayCtx × Expr) := do
            -- pin every substituted term's value IN THIS ENV (simultaneous-
            -- substitution semantics, J1(b)-validated)
            let formals := alist.map (·.1)
            let args := alist.map (·.2)
            let mut ctxD := ctxD
            let mut vals : List (Expr × Expr) := []
            for (_, atm) in alist do
              ctxD ← pinTermOpaques cfg' eV ctxD atm
              let aE ← ctxValExpr cfg' ctxD atm
              let aP ← ctxValProof cfg' ctxD atm
              vals := vals ++ [(aE, aP)]
            -- DECREASE derivation (design I4/I5): consp-ness of a measured
            -- variable from the case's ruling facts — direct (consp v),
            -- falsy (endp v), falsy (atom v), or a NIL or-form compound
            -- test inverted along the EMITTED term (J3); else hard-fail.
            let conspToBoolOf (mv : Symbol) : MetaM Expr := do
              let mvT : SExpr := .atom (.symbol mv)
              let consT : SExpr :=
                .cons (.atom (.symbol { name := "CONSP" })) (.cons mvT .nil)
              let endpT : SExpr :=
                .cons (.atom (.symbol { name := "ENDP" })) (.cons mvT .nil)
              let atomT : SExpr :=
                .cons (.atom (.symbol { name := "ATOM" })) (.cons mvT .nil)
              let xvE ← dpConcVar eV mv
              match facts.find? (fun f => f.test == consT && f.sign) with
              | some cf => do
                let neTy ← mkAppM ``Ne #[conspOf xvE, nilC]
                unless ← isDefEq (← inferType cf.signE) neTy do
                  throwError "replayInduction: the (consp {mv.name}) \
                              fact's value is not Logic.consp of the \
                              measured var's env value"
                let hNeCast ← mkExpectedTypeHint cf.signE neTy
                mkAppM ``toBool_true_of_ne_nil #[hNeCast]
              | none =>
              -- the case tree strips the leading `not`: the step case's
              -- fact is the POSITIVE recognizer with sign FALSE
              match facts.find? (fun f => f.test == endpT && !f.sign) with
              | some cf => do
                let eqTy ← mkEq (mkApp (mkConst ``Logic.endp) xvE) nilC
                unless ← isDefEq (← inferType cf.signE) eqTy do
                  throwError "replayInduction: the falsy (endp {mv.name}) \
                              fact's value is not Logic.endp of the \
                              measured var's env value"
                let hCast ← mkExpectedTypeHint cf.signE eqTy
                mkAppM ``consp_toBool_of_endp_nil #[hCast]
              | none =>
              match facts.find? (fun f => f.test == atomT && !f.sign) with
              | some cf => do
                -- direct falsy (atom v) — J4's INTERLEAVE shape
                let eqTy ← mkEq (mkApp (mkConst ``Logic.atom) xvE) nilC
                unless ← isDefEq (← inferType cf.signE) eqTy do
                  throwError "replayInduction: the falsy (atom {mv.name}) \
                              fact's value is not Logic.atom of the \
                              measured var's env value"
                let hCast ← mkExpectedTypeHint cf.signE eqTy
                mkAppM ``consp_toBool_of_atom_nil #[hCast]
              | none => do
                -- J3 (design I5): a COMPOUND or-form ruling test — ACL2's
                -- `(IF a a c)` or-normal form (ZIP2/ZIP3) — whose NIL fact
                -- or-contains the (ATOM mv) leaf. Invert along the EMITTED
                -- term's shape; any other shape hard-fails.
                let rec orContains (t : SExpr) : Bool :=
                  t == atomT ||
                    match t with
                    | .cons (.atom (.symbol ifS))
                        (.cons a (.cons a2 (.cons c .nil))) =>
                      ifS.name == "IF" && a == a2
                        && (orContains a || orContains c)
                    | _ => false
                let some cf := facts.find?
                    (fun f => !f.sign && orContains f.test)
                  | throwError "replayInduction: no in-scope truthy \
                      (consp {mv.name}) / falsy (endp/atom {mv.name}) \
                      fact, and no nil or-form ruling fact contains \
                      (ATOM {mv.name}) — IH decrease underivable \
                      (frontier)"
                let rec invert (t : SExpr) (hNil : Expr) : MetaM Expr := do
                  if t == atomT then
                    mkAppM ``consp_toBool_of_atom_nil #[hNil]
                  else match t with
                    | .cons (.atom (.symbol ifS))
                        (.cons a (.cons a2 (.cons c .nil))) => do
                      unless ifS.name == "IF" && a == a2 do
                        throwError "replayInduction: ruling test {repr t} \
                            is not or-form (J3 inversion frontier)"
                      let hpair ← mkAppM ``cond_or_nil_inv #[hNil]
                      if orContains a then
                        invert a (← mkAppM ``And.left #[hpair])
                      else
                        invert c (← mkAppM ``And.right #[hpair])
                    | _ =>
                      throwError "replayInduction: or-form inversion \
                          reached a non-if non-(ATOM {mv.name}) component \
                          {repr t} (frontier)"
                invert cf.test cf.signE
            -- DECREASE FRAGMENTS by measured-subset arity (design I4):
            -- J2 single-var (CDR/CAR), J4 two-var sum SWAP; beyond = frontier
            let hLtRaw ←
              match measuredVars with
              | [mv] => do
                let mvT : SExpr := .atom (.symbol mv)
                let some mtm := alist.lookup mv
                  | throwError "replayInduction: IH omits the measured var \
                      {mv.name} (identity substitution — frontier)"
                let hToBool ← conspToBoolOf mv
                let cdrT : SExpr :=
                  .cons (.atom (.symbol { name := "CDR" })) (.cons mvT .nil)
                let carT : SExpr :=
                  .cons (.atom (.symbol { name := "CAR" })) (.cons mvT .nil)
                if mtm == cdrT then
                  mkAppM ``acl2Count_cdr_lt_of_consp #[hToBool]
                else if mtm == carT then
                  mkAppM ``acl2Count_car_lt_of_consp #[hToBool]
                else
                  throwError "replayInduction: measured substitution \
                      {repr mtm} beyond the J2 cdr/car fragment (frontier)"
              | [v1, v2] => do
                -- J4 SUM-measure, the SWAP fragment (INTERLEAVE's scheme,
                -- J1(b)-validated): v1 := (var v2), v2 := (CDR v1); the sum
                -- decreases by the named Count lemma from v1's consp-ness.
                let v1T : SExpr := .atom (.symbol v1)
                let v2T : SExpr := .atom (.symbol v2)
                let cdr1T : SExpr :=
                  .cons (.atom (.symbol { name := "CDR" })) (.cons v1T .nil)
                let some t1 := alist.lookup v1
                  | throwError "replayInduction: IH omits measured var \
                      {v1.name} (frontier)"
                let some t2 := alist.lookup v2
                  | throwError "replayInduction: IH omits measured var \
                      {v2.name} (frontier)"
                unless t1 == v2T && t2 == cdr1T do
                  throwError "replayInduction: sum-measure substitution \
                      ({v1.name} := {repr t1}, {v2.name} := {repr t2}) \
                      beyond the J4 swap fragment (frontier)"
                let hToBool ← conspToBoolOf v1
                let xv2E ← dpConcVar eV v2
                mkAppOptM ``acl2Count_swap_cdr_sum_lt_consp
                  #[none, some xv2E, some hToBool]
              | _ =>
                throwError "replayInduction: {measuredVars.length}-variable \
                    measure decrease discharge (frontier)"
            -- e' and the cast of the decrease to μ e' < μ e (defeq through
            -- the concrete envUpdate lookups)
            let formalsE ← mkListLit (mkConst ``Symbol) (formals.map reflectSymbol)
            let valsList := vals.map (·.1)
            let valsE ← mkListLit (mkConst ``SExpr) valsList
            let argsE ← mkListLit (mkConst ``SExpr) (args.map reflectSExpr)
            let e' ← mkAppM ``envUpdate #[eV, formalsE, valsE]
            let ltTy ← mkAppM ``LT.lt
              #[(mkApp μE e').headBeta, (mkApp μE eV).headBeta]
            unless ← isDefEq (← inferType hLtRaw) ltTy do
              throwError "replayInduction: the decrease fact does not match \
                          μ's env-update reduction (internal)"
            let hLt ← mkExpectedTypeHint hLtRaw ltTy
            let pIH' := mkAppN sihV #[e', hLt]
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
            let proofs := vals.map (·.2)
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
                let mut p ← rec.clause cfg' ctxD child
                -- ruling-literal peels, clause order
                for t in c.tests do
                  let (litPos, fact) ← do
                    match t with
                    | .cons (.atom (.symbol ns)) (.cons u .nil) =>
                      if ns.name == "NOT" then
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
                    if negLit == (.cons (.atom (.symbol { name := "NOT" }))
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
          mkLambdaFVars #[sihV] body
    mkLambdaFVars #[eV] inner
  -- 6. apply the induction at the ambient env (env-level motive — no
  -- controller-value instantiation plumbing)
  let indP ← mkAppM ``measure_strong_induction #[μE, P, step]
  return (mkApp indP cfg.envExpr).headBeta

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
partial def replayClauseSpineWith (rec : ClauseRec) (cfg : ReplayConfig) (ctx : ReplayCtx) (idStr : String)
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
    if (runeOf n).ty == "context-subst" then
      return ← replayClauseSpineWith rec cfg ctx idStr clauseLits rest accClause children
    -- a :BRANCH-SUBSTITUTION (remove-trivial-equivalences): ACL2 substitutes
    -- `var := val` THROUGHOUT the clause, justified by the clause's own
    -- `(not (equal var val))` literal, and scans the SUBSTITUTED literals.
    -- Mirror: byCases on that literal's value — truthy closes the clause;
    -- nil gives the value equality, `diffCollapse` transports the whole
    -- disjunction to the substituted clause, and the walk continues there.
    if (runeOf n).ty == "branch-substitution" then
      let .node _ varT valT _ prov := n
      -- :EQUIVALENCE is the RELATION name; only `equal` is supported
      unless prov.equivTerm == some (.atom (.symbol { name := "EQUAL" })) do
        throwError "replayClauseSpine: branch-substitution under equivalence \
                    {repr prov.equivTerm} at {idStr} (frontier — equal only)"
      let .atom (.symbol varSym) := varT
        | throwError "replayClauseSpine: branch-substitution variable \
                      {repr varT} is not a variable at {idStr}"
      -- the justifying clause literal `(not (equal … …))`, either orientation
      let mkNegEq (x y : SExpr) : SExpr :=
        .cons (.atom (.symbol { name := "NOT" }))
          (.cons (.cons (.atom (.symbol { name := "EQUAL" }))
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
        let mut curL : SExpr := .cons (.atom (.symbol { name := "IF" }))
          (.cons trivLit (.cons quoteT (.cons tailTerm .nil)))
        let mut curR : SExpr := tailTerm
        for (_, l) in (substLits.take kPos).reverse do
          let st : PathStep := { fn := { name := "IF" }, arity := 3, argIdx := 2,
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
        let pRest ← replayClauseSpineWith rec cfg ctx idStr shortened rest accClause children
        let p ← mkAppM ``evtrue_of_fuel_eq #[chainAll, pRest]
        mkLambdaFVars #[hNil] p
      let posL ← withLocalDeclD `hne (← mkAppM ``Ne #[vK, nilC]) fun hNe => do
        let p ← evtrueOfLitTrue cfg ctx (clauseLits.map (·.2)) (kIdx - 1) negEq hNe
        mkLambdaFVars #[hNe] p
      let _ := pK
      return ← mkAppM ``Classical.byCases #[negL, posL]
    -- a clause-level EQUAL-SELF step: the literal (equal X X) is TRUE by
    -- reflexivity and closes the whole disjunction (comm-rm's *1/1.2 after
    -- its branch-substitution trivializes the conclusion)
    if (runeOf n).ty == "equal-self" then
      -- this step CLOSES the clause; trailing spine items would be silently
      -- unreplayed — fail closed (audit #3 hardening)
      unless rest.isEmpty do
        throwError "replayClauseSpine: {rest.length} spine item(s) after a \
                    closing clause-level equal-self at {idStr} (frontier)"
      let (lhs, rhs) := nodeLhsRhs n
      unless rhs == quoteT do
        throwError "replayClauseSpine: clause-level equal-self with rhs \
                    {repr rhs} at {idStr} (frontier)"
      let some X := asEqualSelf lhs
        | throwError "replayClauseSpine: clause-level equal-self lhs \
                      {repr lhs} is not (equal X X) at {idStr}"
      let some k := clauseLits.findIdx? (·.2 == lhs)
        | throwError "replayClauseSpine: equal-self literal {repr lhs} not \
                      in the clause at {idStr}"
      let ctx ← pinTermOpaques cfg cfg.envExpr ctx lhs
      let vX ← ctxValExpr cfg ctx X
      let hEqT ← mkAppM ``Logic.equal_self #[vX]
      let tNeNil ← proveByDecide
        (← mkAppM ``Ne #[mkConst ``SExpr.t, mkConst ``SExpr.nil]) "t ≠ nil"
      let hne ← mkAppM ``ne_of_eq_of_ne #[hEqT, tNeNil]
      return ← evtrueOfLitTrue cfg ctx (clauseLits.map (·.2)) k lhs hne
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
          let p ← replayClauseSpineWith rec cfg ctx idStr restLits' items accClause children
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
        let p ← replayClauseSpineWith rec cfg ctx' idStr clauseLits items accClause children
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
        return ← composeSplit rec cfg ctx idStr lp chainOpt clit restLits branchSegs
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
        let pChild ← rec.clause cfg ctx child
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
        let p ← replayClauseSpineWith rec cfg ctx' idStr restLits contItems accClause' children
        mkLambdaFVars #[h] p
      mkAppM ``evtrue_dp_if_split
        #[cfg.worldExpr, cfg.envExpr, reflectSExpr lp.literal, reflectSExpr quoteT,
          reflectSExpr restTerm, vLit, pLit, hthen, helse]

/-- Replay a clause node: prove `EvTrue w env (disjoinTerm inputClause)`
    (for a single-literal clause this IS the literal/formula statement).
    Induction nodes hard-fail (the scaffold lands next); a pushed clause delegates
    to its pool-root child when the clauses coincide. -/
partial def replayClauseWith (rec : ClauseRec) (cfg : ReplayConfig) (ctx : ReplayCtx) (cn : ClauseNode) : MetaM Expr := do
  if cn.induction.isSome then
    return ← replayInduction rec cfg ctx cn
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
      return ← replayClauseWith rec cfg ctx child
    | _ => throwError "replayClause: push-clause with {cn.children.length} children at {cn.idStr}"
  -- a POOL-SUBSUMED root (synthetic; from (:POOL-SUBSUMED …)): its clause is
  -- an instance-superset of the MORE GENERAL pool root attached as its child
  if cn.steps.any (fun s => s.processor.toLower == "pool-subsumed") then
    return ← replaySubsumed rec cfg ctx cn
  -- a DESTRUCTOR-ELIMINATION node: the child clause is over the elim's fresh
  -- variables; replayElim bridges it back through the emitted ELIMSEQUENCE
  if let some st := cn.steps.find? (fun s => s.processor.toLower == "eliminate-destructors-clause") then
    unless clausifyInfos.isEmpty do
      throwError "replayClause: elim step alongside an effective clausify \
                  record at {cn.idStr} (frontier)"
    return ← replayElim rec cfg ctx cn st
  -- a GENERALIZE node: the child clause abstracts the emitted :TERMS by fresh
  -- :VARS; replayGeneralize replays the child at the env binding the fresh
  -- vars to the terms' values and substN-bridges back
  if let some st := cn.steps.find? (fun s => s.processor.toLower == "generalize-clause") then
    unless clausifyInfos.isEmpty do
      throwError "replayClause: generalize step alongside an effective \
                  clausify record at {cn.idStr} (frontier)"
    return ← replayGeneralize rec cfg ctx cn st
  -- an ELIMINATE-IRRELEVANCE node: the child clause is an order-preserving
  -- SUBSET of this clause (irrelevant literals dropped) — the child's truth
  -- closes the parent disjunction through whichever literal is truthy
  if cn.steps.any (fun s => s.processor.toLower == "eliminate-irrelevance-clause") then
    unless clausifyInfos.isEmpty do
      throwError "replayClause: eliminate-irrelevance step alongside an \
                  effective clausify record at {cn.idStr} (frontier)"
    return ← replayEliminateIrrelevance rec cfg ctx cn
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
    -- steps BEFORE the clausify record chain the formula to its input; steps
    -- AFTER it discharge dropped output clauses (tau/type-set verdicts on
    -- trivially-true conjuncts — the ratified DP carve-out)
    let allItems := cn.steps.flatMap (·.items)
    let clausifyIdx := allItems.findIdx (fun | .clausify _ => true | _ => false)
    let preSteps := (allItems.take clausifyIdx).filterMap fun
      | .step n => some n | _ => none
    let postSteps := (allItems.drop (clausifyIdx + 1)).filterMap fun
      | .step n => some n | _ => none
    -- the formula is the clause's DISJUNCTION; for a multi-literal clause the
    -- preprocess steps rewrite individual literals, lifted into the disjunction
    -- by path-directed congruence (including the lazy `if`'s then/else branches,
    -- sound here because each step's eval-equality is unconditional)
    let formula := disjoinTerm cn.inputClause
    let (chainOpt, finalT) ← replayPreprocessChainCore cfg ctx formula preSteps
    unless finalT == info.input do
      throwError "replayClause: preprocess chain reached {repr finalT}, the \
                  clausify input is {repr info.input}"
    -- one proof per output clause: a CHILD subgoal, or a post-clausify
    -- DISCHARGE node on a singleton clause
    let mut usedChildren : List String := []
    let mut pOuts : List Expr := []
    for cl in info.out do
      match cn.children.find? (·.inputClause == cl) with
      | some child =>
        usedChildren := usedChildren ++ [child.idStr]
        pOuts := pOuts ++ [← replayClauseWith rec cfg ctx child]
      | none =>
        let [lit] := cl
          | throwError "replayClause: clausify output {repr cl} has no child \
                        subgoal and is not a singleton dischargeable clause \
                        at {cn.idStr} (frontier)"
        let some n := postSteps.find? (fun n =>
            dischargeOrigins.contains (nodeOrigin n) && (nodeLhsRhs n).1 == lit)
          | throwError "replayClause: clausify output {repr cl} has no child \
                        subgoal and no post-clausify discharge node at \
                        {cn.idStr} (emission gap)"
        unless (nodeLhsRhs n).2 == quoteT do
          throwError "replayClause: discharge node for {repr lit} has rhs \
                      {repr (nodeLhsRhs n).2} ≠ (quote t) at {cn.idStr}"
        pOuts := pOuts ++ [← replayDischargeNode cfg ctx lit]
    for child in cn.children do
      unless usedChildren.contains child.idStr do
        throwError "replayClause: child {child.idStr} matches no clausify \
                    output at {cn.idStr} (linking gap)"
    let pInput ←
      match pOuts with
      | [pOut] =>
        if info.out.length == 1 then bridgeClausify cfg ctx info pOut
        else bridgeClausifyMulti cfg ctx info pOuts
      | _ => bridgeClausifyMulti cfg ctx info pOuts
    match chainOpt with
    | none => return pInput
    | some (ch, false) => return ← mkAppM ``evtrue_of_fuel_eq #[ch, pInput]
    | some (ch, true) => return ← mkAppM ``evtrue_of_evrel_siff #[ch, pInput]
  | _ :: _ :: _ =>
    throwError "replayClause: multiple clausify records at {cn.idStr} (frontier)"
  | [] =>
  if lits.isEmpty && cn.inputClause.length == 1 then
    -- a SINGLE-literal clause discharged entirely at PREPROCESS: clause-level
    -- step nodes chain the formula to 't (no literal bracketing is emitted at
    -- preprocess sites). A MULTI-literal clause with only step items falls
    -- through to the SPINE — clause-level branch-substitution/equal-self
    -- steps are spine shapes (comm-rm's *1/1.2).
    let stepNodes := (cn.steps.flatMap (·.items)).filterMap fun
      | .step n => some n | _ => none
    if stepNodes.isEmpty then
      throwError "replayClause: no literal or step items in clause {cn.idStr} \
                  (discharge composition frontier)"
    unless cn.children.isEmpty do
      throwError "replayClause: preprocess chain with child clauses at {cn.idStr} \
                  (clausify-split frontier)"
    let [formula] := cn.inputClause
      | throwError "replayClause: internal — single-literal guard"
    return ← replayPreprocessChain cfg ctx formula stepNodes
  rec.clauseSpine cfg ctx cn.idStr (cn.inputClause.zipIdx.map fun (l, i) => (i + 1, l))
    ((cn.steps.flatMap (·.items)).filter fun
      | .clausify _ => false | _ => true)
    [] cn.children

/- The tied clause-level knot — the ONLY remaining mutual at this layer.
   Public names/signatures identical to the pre-WP2 mutual members. -/
mutual

partial def replayClause (cfg : ReplayConfig) (ctx : ReplayCtx) (cn : ClauseNode) :
    MetaM Expr :=
  replayClauseWith ⟨replayClause, replayClauseSpine⟩ cfg ctx cn

partial def replayClauseSpine (cfg : ReplayConfig) (ctx : ReplayCtx) (idStr : String)
    (clauseLits : List (Nat × SExpr)) (items : List ClauseItem)
    (accClause : List SExpr) (children : List ClauseNode) : MetaM Expr :=
  replayClauseSpineWith ⟨replayClause, replayClauseSpine⟩ cfg ctx idStr
    clauseLits items accClause children

end

/-- The tied record itself (recipes outside this file recurse through it). -/
def clauseRec : ClauseRec := ⟨replayClause, replayClauseSpine⟩


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
    | _, _ => throwFrontier m!"proveTotality: arity {formals.length} unsupported (frontier)"
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
    | _ => throwFrontier m!"proveTotality: arity {formals.length} unsupported (frontier)"
  | some just =>
    -- RECURSIVE (D5 scope): measure (acl2-count m), o<, single measured formal
    unless just.wfRel.name == "O<" do
      throwFrontier m!"proveTotality: well-founded relation {just.wfRel.name} \
          unsupported (frontier: o< only)"
    let some measuredFormal := just.measuredSubset.head?
      | throwFrontier m!"proveTotality: empty measured subset"
    unless just.measuredSubset.length == 1 do
      throwFrontier m!"proveTotality: multi-formal measured subset unsupported \
          (frontier)"
    let wantedMeasure : SExpr :=
      .cons (.atom (.symbol { name := "ACL2-COUNT" }))
        (.cons (.atom (.symbol { name := measuredFormal.name })) .nil)
    unless just.measure == wantedMeasure do
      throwFrontier m!"proveTotality: measure {repr just.measure} unsupported \
          (frontier: (acl2-count <measured-formal>) only)"
    -- D9: the (o-p (measure)) obligation is absorbed by the Nat-typed
    -- measure; SHAPE-CHECK it (hard-fail on anything unexpected)
    let opClause : SExpr :=
      .cons (.cons (.atom (.symbol { name := "O-P" }))
        (.cons wantedMeasure .nil)) .nil
    unless just.terminationClauses.any (· == opClause) do
      throwFrontier m!"proveTotality: expected (o-p {repr wantedMeasure}) \
          obligation not found (emission shape changed?)"
    let countOf (e : Expr) : MetaM Expr := mkAppM ``SExpr.acl2Count #[e]
    match formals with
    | [f1] =>
      unless measuredFormal == f1 do
        throwFrontier m!"proveTotality: measured formal mismatch"
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
    | _ => throwFrontier m!"proveTotality: recursive arity {formals.length} \
        unsupported (frontier)"

/-- #37: the admission-derived totality environment. `defs.entries` lists the
    USER defuns in DEVELOPMENT order followed by the ground-zero defs
    (`Development.toWorld` folds ground zero at the bottom and inserts user
    defuns while unwinding — the old `.reverse` here iterated BACKWARDS, a
    latent order bug that never bit until a fn depended on another user fn's
    totality: perm calls memb/rm). Robust fix: FIXPOINT — passes over the
    candidate set until no progress, so each fn is proved once its
    dependencies are in scope regardless of entry order. A fn that never
    proves stays out (hypothesis-backed downstream — D6). -/
def buildTotalEnv (cfg : ReplayConfig)
    (justs : List (String × Justification))
    (upTo : Option String := none) :
    MetaM (List (String × Nat × Expr)) := do
  -- candidate set: the dev-order prefix up to `upTo` (the lazy-discharge
  -- optimization) plus the ground-zero defs (in scope for every fn).
  -- ASSUMES define-before-use (ACL2 admission order), so the prefix is
  -- dependency-closed; if that were ever violated the only effect is a
  -- frontier failure keeping the hypothesis (D6) — completeness, never
  -- soundness (audit #4)
  let gz := cfg.gzDefs.map (·.1.name)
  let all := cfg.worldVal.defs.entries
  let cands ← match upTo with
    | none => pure all
    | some target => do
      let userEntries := all.filter (fun (s, _) => !gz.contains s.name)
      let rec takeTo : List (Symbol × List Symbol × SExpr) →
          List (Symbol × List Symbol × SExpr)
        | [] => []
        | e :: rest => if e.1.name == target then [e] else e :: takeTo rest
      pure (takeTo userEntries ++ all.filter (fun (s, _) => gz.contains s.name))
  let mut totalEnv : List (String × Nat × Expr) := []
  let mut pending := cands
  let mut progress := true
  while progress do
    progress := false
    let mut still : List (Symbol × List Symbol × SExpr) := []
    for (s, formals, body) in pending do
      try
        let pf ← proveTotality cfg totalEnv s.name formals body
          (justs.lookup s.name)
        totalEnv := (s.name, formals.length, pf) :: totalEnv
        progress := true
      catch e =>
        -- keep ONLY the prover's TAGGED frontier-class failures (the fn
        -- stays hypothesis-backed — D6); anything else is a real defect:
        -- surface it (typed tag, not message prefix — fail-closed audit N1)
        unless isFrontierErr e do
          throw e
        still := still ++ [(s, formals, body)]
    pending := still
  return totalEnv

/-- The TP body walk: a proof of `ConvToP w envE t P` — the body converges
    to a value SATISFYING the lifted-corollary predicate `P` (the TP prover,
    lifter sprint 2026-07-06; the `memb_body_bool` route, mechanized).
    Return-path arms: quote leaves (`P` by kernel decision), `if`-splits
    (liftable or OPAQUE tests — tests need only CONVERGENCE, from the plain
    walk over `totalEnv`), and self-calls (the admission-licensed strong
    IH). Every other body shape is a tagged frontier (D6: the `tp:`
    hypothesis stays). -/
partial def tpWalk (cfg : ReplayConfig) (envE : Expr)
    (vals : List (Symbol × Expr × Expr))
    (facts : List (SExpr × Bool × Expr))
    (totalEnv : List (String × Nat × Expr))
    (self : Option (String × Symbol × Expr × Justification))
    (P : Expr) (t : SExpr) : MetaM Expr := do
  let varP : Symbol → Option (Expr × Expr) := fun s =>
    (vals.find? (fun (f, _, _) => f == s)).map (fun (_, v, p) => (v, p))
  match t with
  | .cons (.atom (.symbol qs)) (.cons qv .nil) =>
    if qs.name == "QUOTE" then
      -- leaf constant: the corollary holds of it by ground kernel decision
      let hP ← proveByDecide (mkApp P (reflectSExpr qv)).headBeta
        s!"tp corollary at leaf {repr qv}"
      return ← mkAppM ``convP_quote
        #[cfg.worldExpr, envE, reflectSExpr qv, P, hP]
    else
      tpWalkCall cfg envE vals facts totalEnv self P t
  | .cons (.atom (.symbol fs)) (.cons c (.cons th (.cons e .nil))) =>
    if fs.name == "IF" then
      if totLiftable c then
        let vc ← dpValExpr [] (dpValProof.dpVarVal envE varP) c
        let hc ← dpValProof cfg envE [] [] varP c
        let toBoolVc ← mkAppM ``Logic.toBool #[vc]
        let mkB (bval : Name) (pos : Bool) (branch : SExpr) : MetaM Expr := do
          withLocalDeclD `hb (← mkEq toBoolVc (mkConst bval)) fun hb => do
            let p ← tpWalk cfg envE vals ((c, pos, hb) :: facts)
              totalEnv self P branch
            mkLambdaFVars #[hb] p
        let ht ← mkB ``Bool.true true th
        let he ← mkB ``Bool.false false e
        return ← mkAppM ``convP_if_split
          #[cfg.worldExpr, envE, reflectSExpr c, reflectSExpr th,
            reflectSExpr e, vc, P, hc, ht, he]
      else
        -- OPAQUE (user-fn) test: converge it by the PLAIN walk (the fn's
        -- own totality is in totalEnv — buildTpEnv runs after totality),
        -- split on the existential verdict
        let hcEx ← totWalk cfg envE vals facts totalEnv none c
        let mkB (bval : Name) (pos : Bool) (branch : SExpr) : MetaM Expr :=
          withLocalDeclD `vc (mkConst ``SExpr) fun vc => do
            let convTy ← mkAppM ``ConvTo
              #[cfg.worldExpr, envE, reflectSExpr c, vc]
            withLocalDeclD `hcv convTy fun hcv => do
              let hbTy ← mkEq (← mkAppM ``Logic.toBool #[vc]) (mkConst bval)
              withLocalDeclD `hb hbTy fun hb => do
                let p ← tpWalk cfg envE vals ((c, pos, hb) :: facts)
                  totalEnv self P branch
                mkLambdaFVars #[vc, hcv, hb] p
        let ht ← mkB ``Bool.true true th
        let he ← mkB ``Bool.false false e
        return ← mkAppM ``convP_if_split_ex
          #[cfg.worldExpr, envE, reflectSExpr c, reflectSExpr th,
            reflectSExpr e, P, hcEx, ht, he]
    else
      tpWalkCall cfg envE vals facts totalEnv self P t
  | _ => tpWalkCall cfg envE vals facts totalEnv self P t
where
  /-- Call arms: SELF-calls via the strong IH; everything else a frontier. -/
  tpWalkCall (cfg : ReplayConfig) (envE : Expr)
      (vals : List (Symbol × Expr × Expr))
      (facts : List (SExpr × Bool × Expr))
      (totalEnv : List (String × Nat × Expr))
      (self : Option (String × Symbol × Expr × Justification))
      (P : Expr) (t : SExpr) : MetaM Expr := do
    let varP : Symbol → Option (Expr × Expr) := fun s =>
      (vals.find? (fun (f, _, _) => f == s)).map (fun (_, v, p) => (v, p))
    let .cons (.atom (.symbol fs)) argsSpine := t
      | throwFrontier m!"proveTp: body shape {repr t} unsupported (frontier)"
    let some (selfName, measuredFormal, ih, just) := self
      | throwFrontier m!"proveTp: call to {fs.name} on the return path of a \
          non-recursive body (frontier)"
    unless fs.name == selfName do
      throwFrontier m!"proveTp: return-path call to {fs.name} (not the \
          self-call) unsupported (frontier)"
    let args := (argsSpine.toList?).getD []
    match cfg.worldVal.defs.get? fs with
    | none => throwFrontier m!"proveTp: self {fs.name} not in world"
    | some (formals, body) =>
      unless args.length == formals.length do
        throwFrontier m!"proveTp: self-call arity mismatch {repr t}"
      let mIdx := formals.findIdx (· == measuredFormal)
      unless totLiftable args[mIdx]! do
        throwFrontier m!"proveTp: self-call MEASURED argument not liftable \
            {repr t} (frontier)"
      unless vals.any (fun (f, _, _) => f == measuredFormal) do
        throwFrontier m!"proveTp: measured formal has no bound value"
      let dec ← totDischargeDecrease just measuredFormal facts args[mIdx]!
      let hNs ← proveNotSpecial fs
      let hDef ← totWalk.totDefFact cfg fs formals body
      match formals, args with
      | [f1], [a1] =>
        let av ← dpValExpr [] (dpValProof.dpVarVal envE varP) a1
        let ap ← dpValProof cfg envE [] [] varP a1
        let hbody ← mkAppM' ih #[av, dec]
        return ← mkAppM ``convP_defn_1
          #[cfg.worldExpr, envE, reflectSymbol fs, reflectSExpr a1, av,
            reflectSymbol f1, reflectSExpr body, P, hNs, hDef, ap, hbody]
      | [f1, f2], [a1, a2] =>
        let aM := args[mIdx]!
        let vM ← dpValExpr [] (dpValProof.dpVarVal envE varP) aM
        let pM ← dpValProof cfg envE [] [] varP aM
        let aO := args[1 - mIdx]!
        let assemble (vO pO : Expr) : MetaM Expr := do
          let hbody ← mkAppM' ih #[vM, dec, vO]
          let (v1, v2, p1, p2) :=
            if mIdx == 0 then (vM, vO, pM, pO) else (vO, vM, pO, pM)
          mkAppM ``convP_defn_2
            #[cfg.worldExpr, envE, reflectSymbol fs, reflectSExpr a1,
              reflectSExpr a2, v1, v2, reflectSymbol f1, reflectSymbol f2,
              reflectSExpr body, P, hNs, hDef, p1, p2, hbody]
        if totLiftable aO then
          let vO ← dpValExpr [] (dpValProof.dpVarVal envE varP) aO
          let pO ← dpValProof cfg envE [] [] varP aO
          return ← assemble vO pO
        else
          -- opaque non-measured argument: plain-walk convergence, value
          -- bound by ∃-elimination (as in the totality prover)
          let hcEx ← totWalk cfg envE vals facts totalEnv none aO
          let k ← withLocalDeclD `vo (mkConst ``SExpr) fun vO => do
            let convTy ← mkAppM ``ConvTo
              #[cfg.worldExpr, envE, reflectSExpr aO, vO]
            withLocalDeclD `hcv convTy fun hcv => do
              mkLambdaFVars #[vO, hcv] (← assemble vO hcv)
          return ← mkAppM ``exists_conv_elim #[hcEx, k]
      | _, _ =>
        throwFrontier m!"proveTp: self-call arity {args.length} unsupported \
            (frontier)"

/-- Prove `tp:fn` (the `mkTpHypType` statement) from the fn's body and its
    EMITTED `:TYPE-PRESCRIPTION` corollary — the TP prover. The corollary is
    CONSUMED (ACL2's emitted type fact — never inferred); the walk proves the
    body's value satisfies it; argument strictness + determinism pin every
    convergence value (`tp_hyp_*_of_body`). Frontier failures are tagged
    (D6: the hypothesis stays visible). -/
def proveTp (cfg : ReplayConfig)
    (totalEnv : List (String × Nat × Expr))
    (justs : List (String × Justification))
    (name : String) (cor : SExpr) : MetaM Expr := do
  let fs : Symbol := { name := name }
  let some (formals, body) := cfg.worldVal.defs.get? fs
    | throwFrontier m!"proveTp: {name} not defined in the world (frontier)"
  let hNs ← proveNotSpecial fs
  let hDef ← totWalk.totDefFact cfg fs formals body
  -- P := fun v => <corollary, (fn formals…) ↦ v, value-lifted> = SExpr.t —
  -- EXACTLY mkTpHypType's conclusion, so the proof inhabits the offered type
  let appPat : SExpr :=
    .cons (.atom (.symbol fs))
      ((formals.map (SExpr.atom ∘ Atom.symbol)).foldr SExpr.cons .nil)
  let P ← withLocalDeclD `v (mkConst ``SExpr) fun vV => do
    let lifted ← dpValExpr [(appPat, vV)]
      (fun s => throwFrontier m!"proveTp: corollary of {name} mentions the \
          free variable {s.name} outside the application (frontier)") cor
    mkLambdaFVars #[vV] (← mkEq lifted (mkConst ``SExpr.t))
  let mkEnvE (avs : List Expr) : MetaM Expr := do
    let formalsE ← mkListLit (mkConst ``Symbol) (formals.map reflectSymbol)
    let avsE ← mkListLit (mkConst ``SExpr) avs
    mkAppM ``bindArgs #[formalsE, avsE]
  let varProofs (envE : Expr) (avs : List Expr) :
      MetaM (List (Symbol × Expr × Expr)) := do
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
    | _, _ => throwFrontier m!"proveTp: arity {formals.length} unsupported (frontier)"
  let mkConvToPTy (envB : Expr) : MetaM Expr :=
    mkAppM ``ConvToP #[cfg.worldExpr, envB, reflectSExpr body, P]
  match justs.lookup name with
  | none =>
    -- NON-RECURSIVE: the walk alone gives the ∀-body form
    match formals with
    | [f1] =>
      let hbody ← withLocalDeclD `av (mkConst ``SExpr) fun av => do
        let envE ← mkEnvE [av]
        let vals ← varProofs envE [av]
        let p ← tpWalk cfg envE vals [] totalEnv none P body
        mkLambdaFVars #[av] p
      mkAppM ``tp_hyp_1_of_body
        #[cfg.worldExpr, reflectSymbol fs, reflectSymbol f1,
          reflectSExpr body, P, hNs, hDef, hbody]
    | [f1, f2] =>
      let hbody ← withLocalDeclD `av1 (mkConst ``SExpr) fun av1 =>
        withLocalDeclD `av2 (mkConst ``SExpr) fun av2 => do
          let envE ← mkEnvE [av1, av2]
          let vals ← varProofs envE [av1, av2]
          let p ← tpWalk cfg envE vals [] totalEnv none P body
          mkLambdaFVars #[av1, av2] p
      mkAppM ``tp_hyp_2_of_body
        #[cfg.worldExpr, reflectSymbol fs, reflectSymbol f1,
          reflectSymbol f2, reflectSExpr body, P, hNs, hDef, hbody]
    | _ => throwFrontier m!"proveTp: arity {formals.length} unsupported (frontier)"
  | some just =>
    -- RECURSIVE (D5 scope, as in proveTotality)
    unless just.wfRel.name == "O<" do
      throwFrontier m!"proveTp: well-founded relation {just.wfRel.name} \
          unsupported (frontier: o< only)"
    let some measuredFormal := just.measuredSubset.head?
      | throwFrontier m!"proveTp: empty measured subset"
    unless just.measuredSubset.length == 1 do
      throwFrontier m!"proveTp: multi-formal measured subset unsupported (frontier)"
    unless just.measure ==
        (.cons (.atom (.symbol { name := "ACL2-COUNT" }))
          (.cons (.atom (.symbol { name := measuredFormal.name })) .nil)) do
      throwFrontier m!"proveTp: measure {repr just.measure} unsupported \
          (frontier: (acl2-count <measured-formal>) only)"
    let countOf (e : Expr) : MetaM Expr := mkAppM ``SExpr.acl2Count #[e]
    let selfC := fun (ih : Expr) => some (name, measuredFormal, ih, just)
    match formals with
    | [f1] =>
      unless measuredFormal == f1 do
        throwFrontier m!"proveTp: measured formal mismatch"
      let step ← withLocalDeclD `av (mkConst ``SExpr) fun av => do
        let ihType ← withLocalDeclD `bv (mkConst ``SExpr) fun bv => do
          let lt ← mkAppM ``Nat.lt #[← countOf bv, ← countOf av]
          let cvty ← mkConvToPTy (← mkEnvE [bv])
          mkForallFVars #[bv] (← mkArrow lt cvty)
        withLocalDeclD `ih ihType fun ih => do
          let envE ← mkEnvE [av]
          let vals ← varProofs envE [av]
          let p ← tpWalk cfg envE vals [] totalEnv (selfC ih) P body
          mkLambdaFVars #[av, ih] p
      let hbody ← mkAppM ``tp_1_rec
        #[reflectSymbol f1, reflectSExpr body, cfg.worldExpr, P, step]
      mkAppM ``tp_hyp_1_of_body
        #[cfg.worldExpr, reflectSymbol fs, reflectSymbol f1,
          reflectSExpr body, P, hNs, hDef, hbody]
    | [f1, f2] =>
      let step ←
        if measuredFormal == f1 then
          withLocalDeclD `av1 (mkConst ``SExpr) fun av1 => do
            let ihType ← withLocalDeclD `bv (mkConst ``SExpr) fun bv => do
              let lt ← mkAppM ``Nat.lt #[← countOf bv, ← countOf av1]
              let inner ← withLocalDeclD `cv (mkConst ``SExpr) fun cv => do
                mkForallFVars #[cv] (← mkConvToPTy (← mkEnvE [bv, cv]))
              mkForallFVars #[bv] (← mkArrow lt inner)
            withLocalDeclD `ih ihType fun ih =>
              withLocalDeclD `av2 (mkConst ``SExpr) fun av2 => do
                let envE ← mkEnvE [av1, av2]
                let vals ← varProofs envE [av1, av2]
                let p ← tpWalk cfg envE vals [] totalEnv (selfC ih) P body
                mkLambdaFVars #[av1, ih, av2] p
        else if measuredFormal == f2 then
          withLocalDeclD `av2 (mkConst ``SExpr) fun av2 => do
            let ihType ← withLocalDeclD `cv (mkConst ``SExpr) fun cv => do
              let lt ← mkAppM ``Nat.lt #[← countOf cv, ← countOf av2]
              let inner ← withLocalDeclD `bv (mkConst ``SExpr) fun bv => do
                mkForallFVars #[bv] (← mkConvToPTy (← mkEnvE [bv, cv]))
              mkForallFVars #[cv] (← mkArrow lt inner)
            withLocalDeclD `ih ihType fun ih =>
              withLocalDeclD `av1 (mkConst ``SExpr) fun av1 => do
                let envE ← mkEnvE [av1, av2]
                let vals ← varProofs envE [av1, av2]
                let p ← tpWalk cfg envE vals [] totalEnv (selfC ih) P body
                mkLambdaFVars #[av2, ih, av1] p
        else
          throwError "proveTp: measured formal not among the formals (internal)"
      let recLemma :=
        if measuredFormal == f1 then ``tp_2_rec else ``tp_2_rec_snd
      let hbody ← mkAppM recLemma
        #[reflectSymbol f1, reflectSymbol f2, reflectSExpr body,
          cfg.worldExpr, P, step]
      mkAppM ``tp_hyp_2_of_body
        #[cfg.worldExpr, reflectSymbol fs, reflectSymbol f1,
          reflectSymbol f2, reflectSExpr body, P, hNs, hDef, hbody]
    | _ => throwFrontier m!"proveTp: recursive arity {formals.length} \
        unsupported (frontier)"

/-- Substitute a hypothesis fvar by LET-BINDING its discharge proof instead
    of textual replacement (`replaceFVar`): `k` uses of the hypothesis share
    ONE copy of the (potentially enormous) discharge term instead of `k`
    copies. Proof-term scale fix (2026-07-06): perm-is-an-equivalence
    measured 3.87e9 Expr nodes (without sharing) from duplicated rule-hyp
    discharge proofs alone. No-op when the fvar does not occur. -/
def letBindFVar (body v value : Expr) : MetaM Expr := do
  if !body.containsFVar v.fvarId! then return body
  let ty ← inferType v
  let name ← v.fvarId!.getUserName
  return .letE name ty value (body.abstract #[v]) false

/-- Flatten an ACL2 `and`-antecedent: `(if A rest 'nil)` right-nesting →
    `[A, …]`; anything else is a single hypothesis. -/
partial def flattenAnd : SExpr → List SExpr
  | t@(.cons (.atom (.symbol ifS)) (.cons a (.cons rest (.cons e .nil)))) =>
    if ifS.name == "IF" && e == quoteNil then a :: flattenAnd rest else [t]
  | t => [t]

/-- D5 PRELUDE-CONSTANT registry (design §D5, WP3): ground-zero rules ACL2
    admits at boot with proofs SKIPPED (`ld-skip-proofsp`) — no replayable
    evidence exists, so each is proved ONCE in Lean about the trusted-core
    primitive (`GzRules.lean`), resting on the `LexorderOrder` theorems.
    Entry: rule name ↦ (the constant, the primitive's no-shadow fn). A
    ground-zero rule name can never collide with a user rule — ACL2 refuses
    the redefinition at admission. -/
def d5GzRules : List (String × Name × String) :=
  [("LEXORDER-REFLEXIVE",  (``gz_rule_lexorder_reflexive,  "LEXORDER")),
   ("LEXORDER-TRANSITIVE", (``gz_rule_lexorder_transitive, "LEXORDER"))]

/-- Discharge a GROUND-ZERO rule's `rule:<name>` hypothesis by its D5
    prelude constant: instantiate at the theorem's world + the primitive's
    no-shadow fact, then type-hint against the hypothesis type built FROM
    THE EMITTED SPEC (`mkRuleHypType`) — a drifted emission or a mis-stated
    constant fails here (fail-closed recompute-check, kernel-backed at
    `Meta.check`). -/
def dischargeGzRuleHyp (cfg : ReplayConfig) (spec : RuleSpec) (decl : Name)
    (noShadowFn : String) : MetaM Expr := do
  let hno ← proveNoShadow cfg { name := noShadowFn }
  mkExpectedTypeHint (mkApp2 (mkConst decl) cfg.worldExpr hno)
    (← mkRuleHypType cfg spec)

/-- D1 MIRROR REGISTRY (design §D1, WP4): replayed theorems as per-theorem
    Lean CONSTANTS. Entry: theorem name ↦ (the `addDecl`'d constant — type
    `∀ env, <kept-condition telescope> → EvTrue w ⟪Goal⟫` — and its kept
    condition strings, `total:`/`tp:`/`rule:` in telescope order).
    `dischargeRuleHyp` APPLIES the constant instead of re-replaying the
    dependency's tree per consumer — the kernel checks each proof once and a
    reference is O(1), collapsing the multiplicative dependency-tree blowup
    (the ≈557M-node perm-equivalence precedent, design §4). -/
abbrev MirrorRegistry := List (String × Name × List String)

/-- DISCHARGE a `rule:<thm>` hypothesis from its dependency theorem's replayed
    mirror (v1 step 5, docs/plans/2026-07-05_theorem-dependency-hypotheses.md):
    obtain the dependency's mirror — by APPLYING its D1 registry constant at
    the consumer's own telescope fvars (same world, identical hypothesis
    statements) when registered, else by replaying the dependency INSIDE the
    same hypothesis telescope (`ctx` — its own conditions stay as the shared
    fvars, so transitive conditions compose) — then DECODE the mirror to the
    stored-rule statement. The decode recomputes ACL2's create-rewrite-rule
    normalization between two EMITTED artifacts — the defthm formula (the
    dependency's Goal clause) and the stored rule — and hard-fails on any
    mismatch: strip `implies`, flatten the `and`-antecedent (must equal the
    rule's :HYPS), then either the equality conclusion IS (equal lhs rhs), or
    the boolean-strengthened form (conclusion = lhs, rhs = 'T) pinned by the
    head fn's EMITTED :TYPE-PRESCRIPTION. All value-level: MP on
    `Logic.implies`, two-valued `Logic.equal` decode, TP boolean pin. -/
def dischargeRuleHyp (cfg : ReplayConfig) (ctx : ReplayCtx) (spec : RuleSpec)
    (depProofs : List (String × ClauseProof))
    (mirrors : MirrorRegistry := []) : MetaM Expr := do
  let some cp := depProofs.lookup spec.name
    | throwFrontier m!"dischargeRuleHyp: no dependency proof for rule {spec.name}"
  let some depRoot := cp.root
    | throwFrontier m!"dischargeRuleHyp: dependency {spec.name} has no proof tree"
  let [formula] := depRoot.inputClause
    | throwFrontier m!"dischargeRuleHyp: dependency {spec.name}'s Goal is not a                   single-literal clause (frontier)"
  -- recompute-and-check the create-rewrite-rule normalization
  let (hypsF, concl) := match formula with
    | .cons (.atom (.symbol impS)) (.cons h (.cons c .nil)) =>
      if impS.name == "IMPLIES" then (flattenAnd h, c) else ([], formula)
    | _ => ([], formula)
  unless hypsF == spec.hyps do
    throwFrontier m!"dischargeRuleHyp: {spec.name}'s flattened antecedent                 {repr hypsF} ≠ the stored rule's :HYPS {repr spec.hyps}                 (normalization divergence — frontier)"
  let eqForm : SExpr := .cons (.atom (.symbol { name := "EQUAL" }))
    (.cons spec.lhs (.cons spec.rhs .nil))
  let routeEqual := concl == eqForm
  let routeBool := concl == spec.lhs && spec.rhs == quoteT
  unless routeEqual || routeBool do
    throwFrontier m!"dischargeRuleHyp: {spec.name}'s conclusion {repr concl}                 matches neither (equal lhs rhs) nor the boolean-strengthened                 lhs ⇒ 'T shape (frontier)"
  let w := cfg.worldExpr
  withLocalDeclD `env' (mkConst ``ACL2.Env) fun envV => do
    let cfgD := { cfg with envExpr := envV }
    let mut ctxD := { ctx with varVals := [], vals := [], litFacts := [],
                               branchFacts := [], segFacts := [] }
    ctxD ← pinTermOpaques cfgD envV ctxD formula
    -- premises: EvTrue w env' hᵢ for each stored-rule hyp
    let premDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
      (spec.hyps.zipIdx.map fun (h, i) =>
        (Name.mkSimple s!"h{i}", BinderInfo.default,
         fun (_ : Array Expr) => do
           pure (← mkAppM ``EvTrue #[w, envV, reflectSExpr h]))).toArray
    let ctxDFixed := ctxD
    withLocalDecls premDecls fun premVs => do
      -- the dependency's mirror at env'. D1 registry hit: APPLY the
      -- dependency's constant at the consumer's own telescope fvars for its
      -- kept conditions (same world — identical hypothesis statements; a
      -- missing/ambiguous mapping is a DEFECT, not a frontier: the consumer
      -- telescope offers every total:/tp:/rule: the dependency could keep).
      -- Otherwise re-replay the dependency inside the shared telescope; a
      -- replay wall in its tree is a FRONTIER for the discharge (keep-hyp).
      let pDep ←
        match mirrors.find? (fun (n, _, _) => n == spec.name) with
        | some (_, decl, depConds) => do
          let condArgs ← depConds.toArray.mapM fun c => do
            if c.startsWith "total:" then
              let fn := (c.drop "total:".length).toString
              let some h := ctx.totalHyps.lookup fn
                | throwError "dischargeRuleHyp: registry dependency \
                    {spec.name} keeps {c}, absent from the consumer \
                    telescope (internal)"
              pure h
            else if c.startsWith "tp:" then
              let fn := (c.drop "tp:".length).toString
              let some (_, _, h) := ctx.tpHyps.find? (fun (nm, _, _) => nm == fn)
                | throwError "dischargeRuleHyp: registry dependency \
                    {spec.name} keeps {c}, absent from the consumer \
                    telescope (internal)"
              pure h
            else if c.startsWith "rule:" then
              let rn := (c.drop "rule:".length).toString
              match ctx.ruleHyps.filter (fun (r, _) => r.runeKey == rn) with
              | [(_, h)] => pure h
              | [] => throwError "dischargeRuleHyp: registry dependency \
                  {spec.name} keeps {c}, absent from the consumer \
                  telescope (internal)"
              | _ => throwError "dischargeRuleHyp: registry dependency \
                  {spec.name} keeps {c} but the consumer telescope offers \
                  several same-named rules (ambiguous — refuse rather than \
                  guess)"
            else throwError "dischargeRuleHyp: registry dependency \
                {spec.name} keeps unrecognized condition {c} (internal)"
          pure (mkAppN (mkConst decl) (#[envV] ++ condArgs))
        | none =>
          try replayClause cfgD ctxDFixed depRoot
          catch e => throwFrontier m!"dischargeRuleHyp: dependency {spec.name}'s \
              replay failed (frontier): {e.toMessageData}"
      let convF ← ctxValProof cfgD ctxDFixed formula
      let hFne ← mkAppM ``ne_nil_of_evtrue_conv #[pDep, convF]
      -- conclusion-value truthiness: bare conclusion, or through MP
      let hvC ←
        if spec.hyps.isEmpty then
          pure hFne
        else do
          -- antecedent truthiness from the premises
          let hvHs ← (spec.hyps.zipIdx.toArray.mapM fun (h, i) => do
            let convH ← ctxValProof cfgD ctxDFixed h
            mkAppM ``ne_nil_of_evtrue_conv #[premVs[i]!, convH])
          let rec andNe (hs : List Expr) : MetaM Expr := do
            match hs with
            | [] => throwError "dischargeRuleHyp: internal — no hyps"
            | [h1] => pure h1
            | h1 :: rest => mkAppM ``and_value_ne_nil #[h1, ← andNe rest]
          let hvH ← andNe hvHs.toList
          mkAppM ``implies_value_mp #[hFne, hvH]
      -- the target eval-equality
      let body ←
        if routeEqual then do
          let hEq ← mkAppM ``Logic.eq_of_equal_ne_nil #[hvC]
          let convL ← ctxValProof cfgD ctxDFixed spec.lhs
          let convR ← ctxValProof cfgD ctxDFixed spec.rhs
          mkAppM ``fuel_eq_of_conv #[convL, convR, hEq]
        else do
          -- boolean route: the conclusion's head fn's EMITTED TP pins the
          -- truthy value to exactly t
          let .cons (.atom (.symbol fs)) argsSpine := concl
            | throwFrontier m!"dischargeRuleHyp: boolean conclusion {repr concl}                           is not a fn application (frontier)"
          -- TWO-VALUED trusted-core conclusion (same registry as the
          -- recognizer arm): TRUE-LISTP/CONSP evaluate through their Logic
          -- lifts, whose boolean range is the core's own PROVED semantics —
          -- no emitted TP required. USER fns still consume the EMITTED
          -- :TYPE-PRESCRIPTION (type facts from ACL2, never Lean inference).
          let coreBool? : Option (Name × Name) :=
            if fs.name == "TRUE-LISTP" then
              some (``Logic.trueListp, ``logic_trueListp_ne_nil_t)
            else if fs.name == "CONSP" then
              some (``Logic.consp, ``logic_consp_ne_nil_t)
            else none
          let hT ← match coreBool? with
            | some (liftC, neLemma) => do
              let vC ← ctxValExpr cfgD ctxDFixed concl
              unless vC.isAppOfArity liftC 1 do
                throwFrontier m!"dischargeRuleHyp: value of {repr concl} is                               not ({liftC} _) (frontier)"
              mkAppM neLemma #[vC.appArg!, hvC]
            | none => do
              let some (_, _, tpHyp) := ctx.tpHyps.find? (fun (nm, _, _) => nm == fs.name)
                | throwFrontier m!"dischargeRuleHyp: no :TYPE-PRESCRIPTION hypothesis                           for {fs.name} (emit more, frontier)"
              let some (formals, _) := cfg.worldVal.defs.get? fs
                | throwFrontier m!"dischargeRuleHyp: {fs.name} not defined in the world"
              let args := (argsSpine.toList?).getD []
              unless formals.length == args.length do
                throwFrontier m!"dischargeRuleHyp: arity mismatch instantiating the                         TP of {fs.name}"
              let some (vC, convC) := ctxDFixed.val? concl
                | throwFrontier m!"dischargeRuleHyp: conclusion {repr concl} has no                           pinned value (frontier)"
              let fact := mkAppN tpHyp ((#[envV] : Array Expr)
                ++ (args.map reflectSExpr).toArray ++ #[vC, convC])
              mkAppM ``tp_cond_boolean_t #[vC, fact, hvC]
          let pq ← mkAppM ``re_val_quote #[w, envV, reflectSExpr SExpr.t]
          let hCast ← proveByDecide
            (← mkEq (mkConst ``SExpr.t) (reflectSExpr SExpr.t)) "t reflects"
          let hEq ← mkAppM ``Eq.trans #[hT, hCast]
          mkAppM ``fuel_eq_of_conv #[← ctxValProof cfgD ctxDFixed concl, pq, hEq]
      let pf ← mkLambdaFVars (#[envV] ++ premVs) body
      mkExpectedTypeHint pf (← mkRuleHypType cfg spec)

/-- The CONDITIONAL generic mirror: bind the machine-generated hypothesis
    telescope (per defined fn: totality; plus the lifted TP corollary when one was
    emitted), replay the theorem under it, and λ-abstract. Returns the proof and
    the condition descriptions (the c2 pattern — obligations explicit in the
    type, discharged later by termination emission / Driver Stage 5). -/
def replayProofConditional (cfg : ReplayConfig) (tps : List (String × SExpr))
    (cp : ClauseProof) (justs : List (String × Justification) := [])
    (rules : List RuleSpec := []) (depProofs : List (String × ClauseProof) := [])
    (mirrors : MirrorRegistry := []) :
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
    rules.map (fun r => s!"rule:{r.runeKey}")
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
      -- v1 STEP 5 — LAZY rule-hypothesis discharge: derive each USED
      -- rule:<thm> hypothesis from its dependency's replayed mirror,
      -- REVERSE creation order. Creation order is TOPOLOGICAL in the
      -- dependency DAG (ACL2 admits a defthm only after the rules it cites
      -- exist), so a discharge proof can only introduce uses of STRICTLY
      -- EARLIER rules' fvars — one reverse pass substitutes them all.
      let mut prfR := prf
      for (spec, hypV) in (rules.zip ruleVs.toList).reverse do
        if prfR.containsFVar hypV.fvarId! then
          try
            let pf ←
              -- a GROUND-ZERO rule has no dependency theorem to replay
              -- (boot-admitted, proofs skipped): its D5 prelude constant
              -- discharges it instead
              match d5GzRules.lookup spec.name with
              | some (decl, nsFn) => dischargeGzRuleHyp cfg spec decl nsFn
              | none => dischargeRuleHyp cfg ctx spec depProofs mirrors
            -- LET-bind, don't substitute: every use site shares one copy
            prfR ← letBindFVar prfR hypV pf
          catch e =>
            -- keep ONLY the discharger's TAGGED frontier-class failures (the
            -- hypothesis stays visible in the type — D6, like totality);
            -- anything else is a real defect: surface it (typed tag, not
            -- message prefix — fail-closed audit N1)
            unless isFrontierErr e do
              throw e
      let prf ← instantiateMVars prfR
      -- bind only the hypotheses the replay ACTUALLY USED: an unconsumed offer must
      -- not weaken the statement (hypothesis types are mutually independent, so
      -- dropping unused ones is well-formed).
      let used := (condsAll.zip (totalVs ++ tpVs ++ ruleVs).toList).filter
        fun (_, v) => prf.containsFVar v.fvarId!
      -- #37 LAZY discharge: prove admission totality only for the USED
      -- total: hypotheses and SUBSTITUTE; likewise the TP prover for USED
      -- tp: hypotheses (whose walks also need totality facts — the bound
      -- covers both name sets). Frontier failures keep the hypothesis
      -- (D6 — visible in the type).
      let usedTotalNames := used.filterMap fun (c, _) =>
        if c.startsWith "total:" then some ((c.drop "total:".length).toString) else none
      let usedTpNames := used.filterMap fun (c, _) =>
        if c.startsWith "tp:" then some ((c.drop "tp:".length).toString) else none
      let neededFns := usedTotalNames ++ usedTpNames
      let totalEnv ←
        if neededFns.isEmpty then pure []
        else
          -- `defs.entries` is DEV order (user defuns first, ground zero at
          -- the tail — see buildTotalEnv); the lazy bound is the needed fn
          -- LATEST in dev order
          let lastUsed? := (cfg.worldVal.defs.entries.filter
            (fun (s, _, _) => neededFns.contains s.name)).getLast?
          buildTotalEnv cfg justs (upTo := lastUsed?.map (fun (s, _, _) => s.name))
      let mut prf := prf
      let mut kept : List (String × Expr) := []
      for (c, v) in used do
        if c.startsWith "total:" then
          match totalEnv.find? (fun (n, _, _) => s!"total:{n}" == c) with
          | some (_, _, pf) => prf ← letBindFVar prf v pf
          | none => kept := kept ++ [(c, v)]
        else if c.startsWith "tp:" then
          -- the TP prover: derive the emitted-corollary hypothesis from the
          -- fn's body (lifter sprint 2026-07-06); frontier → keep (D6)
          let fnName := (c.drop "tp:".length).toString
          match tps.lookup fnName with
          | some cor =>
            try
              let pf ← proveTp cfg totalEnv justs fnName cor
              let pf ← mkExpectedTypeHint pf (← inferType v)
              prf ← letBindFVar prf v pf
            catch e =>
              unless isFrontierErr e do
                throw e
              kept := kept ++ [(c, v)]
          | none => kept := kept ++ [(c, v)]
        else
          kept := kept ++ [(c, v)]
      let p ← mkLambdaFVars (kept.map (·.2)).toArray prf
      return (p, kept.map (·.1))

end ACL2.Replay.Driver
