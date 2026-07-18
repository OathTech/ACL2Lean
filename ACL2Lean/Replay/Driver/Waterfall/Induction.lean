/-
  Driver/Waterfall/Induction — split from Driver/Core (WP2 Stage 3a, 2026-07-17;
  see docs/plans/2026-07-18_driver-modular-refactor.md).

  The INDUCTION processor (scheme replay, IH solidify, measure decrease) —
  the home of the #37 decrease-fragment rework.
-/
import ACL2Lean.Replay.Driver.Waterfall

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

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
            -- DECREASE via the emitted-obligation prover (#37 rework,
            -- design I4; docs/plans/2026-07-18_decrease-prover-rework.md):
            -- locate the scheme fn's EMITTED termination clause for THIS
            -- substitution, verify its ruling literals against the case's
            -- facts, and discharge the strict count decrease by the Count
            -- walk. The covering-clause precondition (incl. the sound-
            -- induction distinct-variable condition) ran in
            -- checkCoveringClause; a decrease ACL2 did not emit is never
            -- proved.
            let .cons (.atom (.symbol schemeFn)) argSpine := ind.term
              | throwError "replayInduction: induction term {repr ind.term} \
                  is not an application (frontier)"
            let some schemeActuals := argSpine.toList?
              | throwError "replayInduction: induction term args not a list \
                  (frontier)"
            let some schemeFormals :=
                ((cfg.worldVal.defs.get? schemeFn).map (·.1)).orElse
                  (fun _ => (cfg.gzDefs.find? (·.1 == schemeFn)).map (·.2.1))
              | throwError "replayInduction: scheme fn {schemeFn.name} \
                  neither in the world nor a ground-zero snapshot (frontier)"
            let some just := cfg.justs.lookup schemeFn.name
              | throwError "replayInduction: no emitted justification for \
                  scheme fn {schemeFn.name} (emission gap — frontier)"
            let ctxNow := ctxD
            let hLtRaw ← dischargeDecrease just
              schemeFormals schemeActuals
              (alist.map (·.1)) (alist.map (·.2))
              (facts.map (fun f => (f.test, f.sign)))
              (fun u => ctxValExpr cfg' ctxNow u)
              (fun b => match b with
                | .atom (.symbol mv) => conspToBoolOf mv
                | _ => throwFrontier m!"replayInduction: consp of non-var \
                    measured base {repr b} (frontier)")
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

end ACL2.Replay.Driver
