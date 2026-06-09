/-
  Decision-procedure discharge leaves (c1) — the ratified carve-out (CLAUDE.md).

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
     (`(env.get? s).getD nil`). Primitive-only terms (c1); an opaque user-fn
     subterm hard-fails (c2: totality + type-prescriptions).
  3. The DP FACT `F : ∀ vars, v₁ = nil → … → v_{k-1} = nil → vₖ = t` — the
     clause's truth, abstracted over the variable values — is proved by the
     carved-out decision procedure: one-level SExpr case-split per variable
     (recursively through Atom/Number), then `simp_all` with the Logic
     definitions and `omega`. Deterministic and name-free (`MVarId.cases` +
     one fixed closing tactic); fails loudly if any case survives.
  4. `re_dp_if_split` folds the spine: each literal's value either is non-nil
     (the `'t` then-branch fires) or nil (descend, accumulating the hypothesis);
     at the last literal `F` supplies `vₖ = t` (`re_val_cast`).

  The result: `∃N ∀f≥N, evalOpt f w env (disjoin clause) = some t` — the
  discharge node's exact claim. Wiring this into the surrounding tree (the
  preprocess transformation chain, induction parents) is the composition
  frontier, tracked separately.
-/
import ACL2Lean.Replay.Driver

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta Lean.Elab

/-- DP-lift primitives (unary): ACL2 name → (Logic function, `callBuiltin` rfl lemma). -/
def dpUnary : List (String × Name × Name) :=
  [("not",      ``Logic.not,      ``callBuiltin_not),
   ("zp",       ``Logic.zp,       ``callBuiltin_zp),
   ("consp",    ``Logic.consp,    ``callBuiltin_consp),
   ("integerp", ``Logic.integerp, ``callBuiltin_integerp),
   ("car",      ``Logic.car,      ``callBuiltin_car),
   ("cdr",      ``Logic.cdr,      ``callBuiltin_cdr)]

/-- DP-lift primitives (binary). -/
def dpBinary : List (String × Name × Name) :=
  [("equal",    ``Logic.equal,   ``callBuiltin_equal),
   ("<",        ``Logic.lt,      ``callBuiltin_lt),
   ("binary-+", ``Logic.plus,    ``callBuiltin_plus),
   ("implies",  ``Logic.implies, ``callBuiltin_implies),
   ("iff",      ``Logic.iff,     ``callBuiltin_iff)]

/-- The `Logic`-primitive VALUE of a primitive-only term, with variable values
    supplied by `varVal`. Used twice with the SAME structure — abstractly (vars ↦
    bound fvars, for the DP fact's statement) and concretely (vars ↦
    `(env.get? s).getD nil`) — so the fact's instantiation matches the built
    proofs syntactically. -/
partial def dpValExpr (varVal : Symbol → MetaM Expr) (t : SExpr) : MetaM Expr := do
  match t with
  | .atom (.symbol s) => varVal s
  | .cons (.atom (.symbol fs)) (.cons a .nil) =>
    if fs.name == "quote" then return reflectSExpr a
    else match dpUnary.lookup fs.name with
      | some (fn, _) => return mkApp (mkConst fn) (← dpValExpr varVal a)
      | none => throwError "dpValExpr: unary {fs.name} is not a DP-lift primitive (c2 frontier): {repr t}"
  | .cons (.atom (.symbol fs)) (.cons a (.cons b .nil)) =>
    match dpBinary.lookup fs.name with
    | some (fn, _) => return mkApp2 (mkConst fn) (← dpValExpr varVal a) (← dpValExpr varVal b)
    | none => throwError "dpValExpr: binary {fs.name} is not a DP-lift primitive (c2 frontier): {repr t}"
  | .cons (.atom (.symbol fs)) (.cons c (.cons th (.cons e .nil))) =>
    if fs.name == "if" then
      -- value-level if (inside a literal): `cond (toBool cv) tv ev`
      let vc ← dpValExpr varVal c
      let vt ← dpValExpr varVal th
      let ve ← dpValExpr varVal e
      mkAppM ``cond #[mkApp (mkConst ``Logic.toBool) vc, vt, ve]
    else throwError "dpValExpr: ternary {fs.name} is not a DP-lift primitive (c2 frontier): {repr t}"
  | _ => throwError "dpValExpr: unsupported term shape (c2 frontier): {repr t}"

/-- A clause variable's concrete value: `(env.get? s).getD nil`. -/
def dpConcVar (envExpr : Expr) (s : Symbol) : MetaM Expr := do
  mkAppM ``Option.getD
    #[← mkAppM ``Std.HashMap.get? #[envExpr, reflectSymbol s], mkConst ``SExpr.nil]

/-- Value-characterized convergence of a primitive-only term:
    `∃N ∀f≥N, evalOpt f w env t = some (dpValExpr concrete t)`. -/
partial def dpValProof (cfg : ReplayConfig) (envExpr : Expr) (t : SExpr) : MetaM Expr := do
  match t with
  | .atom (.symbol s) =>
    let hNotT ← proveIsNamedFalse s "t"
    mkAppM ``re_val_var #[cfg.worldExpr, envExpr, reflectSymbol s, hNotT]
  | .cons (.atom (.symbol fs)) (.cons a .nil) =>
    if fs.name == "quote" then
      mkAppM ``re_val_quote #[cfg.worldExpr, envExpr, reflectSExpr a]
    else match dpUnary.lookup fs.name with
      | some (fn, cbLemma) =>
        let pa ← dpValProof cfg envExpr a
        let va ← dpValExpr (dpConcVar envExpr) a
        let rv := mkApp (mkConst fn) va
        let hNs ← proveNotSpecial fs
        let hNo ← proveNoShadow cfg fs
        let hr ← mkAppM cbLemma #[va]
        mkAppM ``conv_builtin1
          #[cfg.worldExpr, envExpr, reflectSymbol fs, reflectSExpr a, va, rv, hNs, hNo, pa, hr]
      | none => throwError "dpValProof: unary {fs.name} is not a DP-lift primitive (c2 frontier)"
  | .cons (.atom (.symbol fs)) (.cons a (.cons b .nil)) =>
    match dpBinary.lookup fs.name with
    | some (fn, cbLemma) =>
      let pa ← dpValProof cfg envExpr a
      let pb ← dpValProof cfg envExpr b
      let va ← dpValExpr (dpConcVar envExpr) a
      let vb ← dpValExpr (dpConcVar envExpr) b
      let rv := mkApp2 (mkConst fn) va vb
      let hNs ← proveNotSpecial fs
      let hNo ← proveNoShadow cfg fs
      let hr ← mkAppM cbLemma #[va, vb]
      mkAppM ``conv_builtin2
        #[cfg.worldExpr, envExpr, reflectSymbol fs, reflectSExpr a, reflectSExpr b,
          va, vb, rv, hNs, hNo, pa, pb, hr]
    | none =>
      if fs.name == "if" then throwError "dpValProof: malformed if (2 args): {repr t}"
      else throwError "dpValProof: binary {fs.name} is not a DP-lift primitive (c2 frontier)"
  | .cons (.atom (.symbol fs)) (.cons c (.cons th (.cons e .nil))) =>
    if fs.name == "if" then
      let pc ← dpValProof cfg envExpr c
      let pt ← dpValProof cfg envExpr th
      let pe ← dpValProof cfg envExpr e
      let vc ← dpValExpr (dpConcVar envExpr) c
      let vt ← dpValExpr (dpConcVar envExpr) th
      let ve ← dpValExpr (dpConcVar envExpr) e
      mkAppM ``re_val_if
        #[cfg.worldExpr, envExpr, reflectSExpr c, reflectSExpr th, reflectSExpr e,
          vc, vt, ve, pc, pt, pe]
    else throwError "dpValProof: ternary {fs.name} is not a DP-lift primitive (c2 frontier)"
  | _ => throwError "dpValProof: unsupported term shape (c2 frontier): {repr t}"

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
    variable's one-level `SExpr` split introduced), then return the leaves. -/
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

/-- Case one level of each clause variable (`SExpr`: nil/atom/cons — cons
    components are NOT recursed into; only the `dpv*`-named intro'd variables are
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
    | none => throwError "dpSplitVars: expected {n} more clause variables to split"
    | some fv =>
      let subs ← g.cases fv
      subs.toList.flatMapM (fun s => dpSplitVars s.mvarId (n - 1))

/-- Build and PROVE the DP fact
    `∀ vars, absVal(l₁) = nil → … → absVal(l_{k-1}) = nil → absVal(lₖ) = t`
    — the discharged clause's truth over all variable values — by the carved-out
    decision procedure (case-split + simp + omega). Hard-fails if any case
    survives the fixed tactic. -/
def proveDpFact (tests : List SExpr) (last : SExpr) (vars : List Symbol) :
    TermElabM Expr := do
  let decls : Array (Name × BinderInfo × (Array Expr → TermElabM Expr)) :=
    (Array.range vars.length).map fun i =>
      (Name.mkSimple s!"dpv{i}", .default, fun _ => pure (mkConst ``SExpr))
  let stmt ← withLocalDecls decls fun fvars => do
    let varMap := vars.zip fvars.toList
    let absVal := dpValExpr fun s =>
      match varMap.find? (fun (v, _) => v == s) with
      | some (_, fv) => pure fv
      | none => throwError "proveDpFact: unmapped variable {s.name}"
    let hypTys ← tests.mapM fun t => do
      mkEq (← absVal t) (mkConst ``SExpr.nil)
    let conclTy ← do mkEq (← absVal last) (mkConst ``SExpr.t)
    let body ← hypTys.foldrM (fun h acc => mkArrow h acc) conclTy
    mkForallFVars fvars body
  let tac ← dpLeafTactic
  -- FIRST try the fixed tactic on the unsplit goal (sufficient for
  -- propositional/equality facts, and avoids the case explosion); only on
  -- failure case-split the variables and close every leaf. Each attempt uses a
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
  let mv ← mkFreshExprMVar stmt
  let (_, g) ← mv.mvarId!.intros
  let leaves ← dpSplitVars g vars.length
  for leaf in leaves do
    let remaining ← Lean.Elab.runTactic leaf tac
    unless remaining.1.isEmpty do
      throwError "proveDpFact: the DP leaf tactic left {remaining.1.length} goal(s) — \
                  the discharged clause's lift is not closable by simp+omega \
                  (clause fact: {stmt})"
  instantiateMVars mv

/-- Replay a decision-procedure DISCHARGE LEAF: prove the discharge node's exact
    claim `∃N ∀f≥N, evalOpt f w env (disjoin clause) = some t` by folding
    `re_dp_if_split` over the spine, with the DP fact closing the last literal. -/
def replayDischargeLeaf (cfg : ReplayConfig) (clauseTerm : SExpr) : TermElabM Expr := do
  let (tests, last) := dpSpine clauseTerm
  let vars := ((tests ++ [last]).flatMap freeVars).eraseDups
  let fact ← proveDpFact tests last vars
  -- instantiate the fact at the concrete variable values
  let concArgs ← vars.mapM (fun s => liftM (dpConcVar cfg.envExpr s))
  let factConc := mkAppN fact concArgs.toArray
  -- fold the spine
  let rec goSpine (t : SExpr) (fPartial : Expr) : TermElabM Expr := do
    match t with
    | .cons (.atom (.symbol fs)) (.cons c (.cons th (.cons e .nil))) =>
      if fs.name == "if" && th == quoteT then
        let pc ← dpValProof cfg cfg.envExpr c
        let vc ← dpValExpr (dpConcVar cfg.envExpr) c
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
          let p ← goSpine e (mkApp fPartial h)
          mkLambdaFVars #[h] p
        mkAppM ``re_dp_if_split
          #[cfg.worldExpr, cfg.envExpr, reflectSExpr c, reflectSExpr th, reflectSExpr e,
            vc, pc, hthen, helse]
      else closeLast t fPartial
    | _ => closeLast t fPartial
  goSpine clauseTerm factConc
where
  closeLast (t : SExpr) (fPartial : Expr) : TermElabM Expr := do
    -- fPartial : concVal(t) = SExpr.t ; cast the value-characterized convergence.
    let pt ← dpValProof cfg cfg.envExpr t
    let vt ← dpValExpr (dpConcVar cfg.envExpr) t
    mkAppM ``re_val_cast
      #[cfg.worldExpr, cfg.envExpr, reflectSExpr t, vt, mkConst ``SExpr.t, pt, fPartial]

end ACL2.Replay.Driver
