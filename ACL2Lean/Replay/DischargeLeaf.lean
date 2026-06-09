/-
  Decision-procedure discharge leaves (c1 + c2) — the ratified carve-out (CLAUDE.md).

  A clause ACL2 closed by a verdict-only decision procedure (tau / type-set
  forward-chain) carries an emitted DISCHARGE NODE `(disjoin clause) ⇒ t`
  (origins `preprocess/tau*`, `preprocess/type-set-fc`, …). There is no internal
  step record to mirror — ACL2 itself has only the verdict — so the replay
  discharges the leaf's precisely-stated obligation with a kernel-checked
  decision procedure:

  1. `dpSpine` splits the disjoined clause `(if l₁ 't (if l₂ 't … lₖ))` into its
     literals.
  2. `dpValProof` builds, per literal, the VALUE-characterized convergence
     `∃N ∀f≥N, evalOpt f w env lᵢ = some vᵢ` where `vᵢ` is an explicit
     `Logic`-primitive expression over the clause variables' env values
     (`(env.get? s).getD nil`).
  3. (c2) An OPAQUE user-fn subterm (e.g. `(cd2 n)`, `(len2 x)`) becomes a
     quantified value `vop` with a CONVERGENCE HYPOTHESIS
     `∃N ∀f≥N, eval opTerm = some vop` (totality — Driver Stage 5 discharges it
     at composition time) and, when the development carries an emitted
     `:TYPE-PRESCRIPTION` for the fn, a TYPE HYPOTHESIS: the corollary
     (instantiated at the occurrence's actuals, lifted to Logic primitives,
     `= t`). The leaf proof is CONDITIONAL on exactly these hypotheses — all
     read off the emitted artifact, never invented.
  4. The DP FACT
     `F : ∀ vars vops, tp₁ = t → … → v₁ = nil → … → v_{k-1} = nil → vₖ = t`
     — the clause's truth over all values — is proved by the carved-out decision
     procedure: try the fixed simp/split_ifs/omega tactic unsplit first, else a
     one-level SExpr case-split per value (recursively through Atom/Number;
     name-free `MVarId.cases`) and the same fixed tactic per leaf. Fails loudly
     if any case survives.
  5. `re_dp_if_split` folds the spine: each literal's value either is non-nil
     (the `'t` then-branch fires) or nil (descend, accumulating the hypothesis);
     at the last literal `F` supplies `vₖ = t` (`re_val_cast`).

  The result: `(vops…) → (hConv…) → (hTP…) → ∃N ∀f≥N, eval (disjoin clause) = some t`
  — the discharge node's exact claim, conditional on the emitted facts. With
  `assumeFact := true`, a DP fact the fixed tactic cannot close is NOT sorried:
  it becomes a further bound hypothesis (`hfact : <the fact>`), so the returned
  proof is CONDITIONAL — its TYPE states the exact missing obligation, no
  `sorryAx` anywhere, and a later prover (lean-smt, richer emission) completes
  it by application. Wiring into the surrounding tree (preprocess transformation
  chain, induction parents, totality discharge) is the composition frontier,
  tracked separately.
-/
import ACL2Lean.Replay.Driver

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta Lean.Elab

-- (dpUnary/dpBinary/dpKnownHead/collectOpaques/dpValExpr/dpConcVar/dpValProof
--  moved to Replay/Driver.lean — they are general driver infrastructure now,
--  shared by the clause-spine replay and this DP lift.)

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
def dpLeafTactic : TermElabM (TSyntax `tactic) :=
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
partial def dpSplitAtoms (g : MVarId) : TermElabM (List MVarId) := do
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
partial def dpSplitVars (g : MVarId) (n : Nat) : TermElabM (List MVarId) := do
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

/-- Build and PROVE the DP fact
    `∀ vars vops, tp₁ = t → … → v₁ = nil → … → v_{k-1} = nil → vₖ = t`
    — the discharged clause's truth over all variable AND opaque values, under the
    emitted type-prescription hypotheses — by the carved-out decision procedure.
    Hard-fails if any case survives the fixed tactic. -/
def dpFactStmt (tests : List SExpr) (last : SExpr) (vars : List Symbol)
    (opaques : List SExpr) (tpCors : List SExpr) : TermElabM Expr := do
  let total := vars.length + opaques.length
  let decls : Array (Name × BinderInfo × (Array Expr → TermElabM Expr)) :=
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

def proveDpFact (stmt : Expr) (total : Nat) : TermElabM Expr := do
  let tac ← dpLeafTactic
  -- FIRST try the fixed tactic on the unsplit goal (sufficient for
  -- propositional/equality facts, and avoids the case explosion); only on
  -- failure case-split the values and close every leaf. Each attempt uses a
  -- FRESH metavariable (a failed attempt may leave its mvar half-assigned).
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

/-- Replay a decision-procedure DISCHARGE LEAF: prove the discharge node's claim
    `∃N ∀f≥N, evalOpt f w env (disjoin clause) = some t`, CONDITIONAL on, per
    opaque user-fn subterm: its convergence (totality) and — when the development
    carries one — its emitted type-prescription corollary. `tps` maps fn name ↦
    corollary (from the parsed `:TYPE-PRESCRIPTION` events). Returns the
    (lambda-abstracted) proof and the list of assumed conditions. -/
def replayDischargeLeaf (cfg : ReplayConfig) (clauseTerm : SExpr)
    (tps : List (String × SExpr) := []) (assumeFact : Bool := false) :
    TermElabM (Expr × List String) := do
  let (tests, last) := dpSpine clauseTerm
  let lits := tests ++ [last]
  let vars := (lits.flatMap freeVars).eraseDups
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
      return (op, some (substTerm formals args cor))
  let conds :=
    opaques.map (fun op => s!"total:{op}") ++
    (opCors.filterMap fun (op, c?) => c?.map fun _ =>
      s!"tp:{(op.toList?.getD []).head?.getD .nil}")
  -- quantify the opaque values, their convergence hypotheses, and TP hypotheses
  let vopDecls : Array (Name × BinderInfo × (Array Expr → TermElabM Expr)) :=
    (Array.range opaques.length).map fun i =>
      (Name.mkSimple s!"vop{i}", .default, fun _ => pure (mkConst ``SExpr))
  let (p, assumed) ← withLocalDecls vopDecls fun vops => do
    let opqMap := opaques.zip vops.toList
    let hConvDecls : Array (Name × BinderInfo × (Array Expr → TermElabM Expr)) :=
      (List.range opaques.length).toArray.map fun i =>
        (Name.mkSimple s!"hconv{i}", .default, fun _ => do
          mkEvalSomeExist cfg.worldExpr cfg.envExpr opaques[i]! vops[i]!)
    withLocalDecls hConvDecls fun hconvs => do
      let opqP := opaques.zip hconvs.toList
      -- TP hypothesis types: instantiated corollary lifted CONCRETELY, = t
      let tpCorsPresent := opCors.filterMap (·.2)
      let tpDecls : Array (Name × BinderInfo × (Array Expr → TermElabM Expr)) :=
        (List.range tpCorsPresent.length).toArray.map fun i =>
          (Name.mkSimple s!"htp{i}", .default, fun _ => do
            mkEq (← dpValExpr opqMap (dpConcVar cfg.envExpr) tpCorsPresent[i]!)
                 (mkConst ``SExpr.t))
      withLocalDecls tpDecls fun htps => do
        let stmt ← dpFactStmt tests last vars opaques tpCorsPresent
        let total := vars.length + opaques.length
        -- Prove the DP fact. With `assumeFact`, an unclosable fact is NOT sorried:
        -- it becomes a further BOUND HYPOTHESIS of the returned proof — the proof
        -- is CONDITIONAL, its type states the exact missing obligation, and a
        -- later prover (lean-smt, richer emission) discharges it by application.
        -- No sorryAx anywhere; reported loudly upstream as `assumed`.
        let fact? ←
          tryCatchRuntimeEx
            (try
              pure (some (← proveDpFact stmt total))
            catch e =>
              if assumeFact then pure none else throw e)
            (fun e =>
              if assumeFact then pure none else throw e)
        let concArgs ← vars.mapM (fun s => liftM (dpConcVar cfg.envExpr s))
        match fact? with
        | some fact =>
          -- instantiate the fact: concrete var values, opaque value fvars, TP hyps
          let factConc := mkAppN fact (concArgs.toArray ++ vops ++ htps)
          let prf ← goSpine cfg opqMap opqP clauseTerm factConc
          return (← mkLambdaFVars (vops ++ hconvs ++ htps) prf, false)
        | none =>
          withLocalDeclD `hfact stmt fun hFact => do
            let factConc := mkAppN hFact (concArgs.toArray ++ vops ++ htps)
            let prf ← goSpine cfg opqMap opqP clauseTerm factConc
            return (← mkLambdaFVars (vops ++ hconvs ++ htps ++ #[hFact]) prf, true)
  return (p, if assumed then conds ++ ["ASSUMED:dp-fact"] else conds)
where
  /-- Fold `re_dp_if_split` over the spine, feeding nil-hypotheses to the fact. -/
  goSpine (cfg : ReplayConfig) (opqMap opqP : List (SExpr × Expr))
      (t : SExpr) (fPartial : Expr) : TermElabM Expr := do
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
          | throwError "replayDischargeLeaf: DP fact arity mismatch at {repr c}"
        let helse ← withLocalDeclD `h dom fun h => do
          let p ← goSpine cfg opqMap opqP e (mkApp fPartial h)
          mkLambdaFVars #[h] p
        mkAppM ``re_dp_if_split
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr c, reflectSExpr th, reflectSExpr e,
            vc, pc, hthen, helse]
      else closeLast cfg opqMap opqP t fPartial
    | _ => closeLast cfg opqMap opqP t fPartial
  closeLast (cfg : ReplayConfig) (opqMap opqP : List (SExpr × Expr))
      (t : SExpr) (fPartial : Expr) : TermElabM Expr := do
    -- fPartial : concVal(t) = SExpr.t ; cast the value-characterized convergence.
    let pt ← dpValProof cfg cfg.envExpr opqMap opqP (t := t)
    let vt ← dpValExpr opqMap (dpConcVar cfg.envExpr) t
    mkAppM ``re_val_cast
      #[cfg.worldExpr, cfg.envExpr, reflectSExpr t, vt, mkConst ``SExpr.t, pt, fPartial]

end ACL2.Replay.Driver
