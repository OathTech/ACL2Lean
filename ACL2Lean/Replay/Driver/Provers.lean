/-
  Driver/Provers — split from Driver/Core (WP2 Stage 3a, 2026-07-17;
  see docs/plans/2026-07-18_driver-modular-refactor.md).

  Walker-independent obligation provers: totality from admission
  (proveTotality/buildTotalEnv), the TP prover (tpWalk/proveTp), and the
  D5 ground-zero rule-hypothesis dischargers.
-/
import ACL2Lean.Replay.Driver.TsConsumer

namespace ACL2.Replay.Driver

open ACL2 ACL2.Replay Lean Lean.Meta

/-- The bound-formal VALUE facts for a `bindArgs formals avs` environment:
    per formal, its value expr and a proof of `∃N ∀f≥N, eval env formal =
    some av` (the `re_val_var_get` route over the positional `bindArgs`
    lookup lemmas). Shared by both provers — `proveTotality` and `proveTp`
    carried byte-identical copies differing only in the frontier message,
    and increment 4's arity-3 TP arm would have made a third (the
    de-duplication norm; `who` keeps the frontier text per-prover). -/
def bindArgsVarProofs (cfg : ReplayConfig) (who : String) (envE : Expr)
    (formals : List Symbol) (avs : List Expr) :
    MetaM (List (Symbol × Expr × Expr)) := do
  let sy := reflectSymbol
  let ne (a b : Symbol) : MetaM Expr := do
    mkDecideProof (← mkAppM ``Ne #[sy a, sy b])
  let valOf (f : Symbol) (av g : Expr) : MetaM Expr :=
    mkAppM ``re_val_var_get #[cfg.worldExpr, envE, sy f, av, g]
  match formals, avs with
  | [f], [av] =>
    let g ← mkAppM ``bindArgs_single_get_self #[sy f, av]
    return [(f, av, ← valOf f av g)]
  | [f1, f2], [av1, av2] =>
    let hne ← ne f1 f2
    let g1 ← mkAppM ``bindArgs_pair_get_fst #[sy f1, sy f2, av1, av2]
    let g2 ← mkAppM ``bindArgs_pair_get_snd #[sy f1, sy f2, av1, av2, hne]
    return [(f1, av1, ← valOf f1 av1 g1), (f2, av2, ← valOf f2 av2 g2)]
  | [f1, f2, f3], [av1, av2, av3] =>
    let g1 ← mkAppM ``bindArgs_triple_get_fst
      #[sy f1, sy f2, sy f3, av1, av2, av3]
    let g2 ← mkAppM ``bindArgs_triple_get_snd
      #[sy f1, sy f2, sy f3, av1, av2, av3, ← ne f1 f2]
    let g3 ← mkAppM ``bindArgs_triple_get_thd
      #[sy f1, sy f2, sy f3, av1, av2, av3, ← ne f1 f3, ← ne f2 f3]
    return [(f1, av1, ← valOf f1 av1 g1), (f2, av2, ← valOf f2 av2 g2),
            (f3, av3, ← valOf f3 av3 g3)]
  | _, _ =>
    throwFrontier m!"{who}: arity {formals.length} unsupported (frontier)"

/-- Prove `total:fn` (the `mkTotalityHypType` statement) from the admission
    data; throws a named-frontier error when out of the D5 scope.
    `recTerm?` (sorting arc 2026-07-28): the RECORDED-TERMINATION bundle —
    when present, the strong induction runs over the INTERPRETED count
    (`interpCount`, design I1 bookkeeping) and self-call decreases come
    from the replayed admission waterfall instead of the destructor walk. -/
def proveTotality (cfg : ReplayConfig)
    (totalEnv : List (String × Nat × Expr))
    (name : String) (formals : List Symbol) (body : SExpr)
    (just? : Option Justification)
    (recTerm? : Option RecTermInfo := none) : MetaM Expr := do
  let fs : Symbol := { name := name }
  let hNs ← proveNotSpecial fs
  let hDef ← totWalk.totDefFact cfg fs formals body
  let mkEnvE (avs : List Expr) : MetaM Expr := do
    let formalsE ← mkListLit (mkConst ``Symbol) (formals.map reflectSymbol)
    let avsE ← mkListLit (mkConst ``SExpr) avs
    mkAppM ``bindArgs #[formalsE, avsE]
  let varProofs (envE : Expr) (avs : List Expr) : MetaM (List (Symbol × Expr × Expr)) :=
    bindArgsVarProofs cfg "proveTotality" envE formals avs
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
    | [_, _, _] =>
      let hbody ← withLocalDeclD `av1 (mkConst ``SExpr) fun av1 =>
        withLocalDeclD `av2 (mkConst ``SExpr) fun av2 =>
          withLocalDeclD `av3 (mkConst ``SExpr) fun av3 => do
            let envE ← mkEnvE [av1, av2, av3]
            let vals ← varProofs envE [av1, av2, av3]
            let p ← totWalk cfg envE vals [] totalEnv none body
            mkLambdaFVars #[av1, av2, av3] p
      mkAppM ``totality_3_of_body
        #[cfg.worldExpr, reflectSymbol fs, reflectSymbol formals[0]!,
          reflectSymbol formals[1]!, reflectSymbol formals[2]!,
          reflectSExpr body, hNs, hDef, hbody]
    | _ => throwFrontier m!"proveTotality: arity {formals.length} unsupported (frontier)"
  | some just =>
    -- RECURSIVE: the emitted justification classified through the UNIFIED
    -- MEASURE TABLE (R3, 2026-08-14 — `Replay/MeasureTable.lean`). This
    -- gate used to accept exactly ONE shape, `(acl2-count <single measured
    -- formal>)`, which the overspecialization audit's F6 found blocking
    -- 100% of the main-row `total:` debt — shapes the μ-registry and
    -- `dischargeDecrease` already understood. The row now decides, and
    -- every row is answered below (a walk or its own named frontier).
    unless just.wfRel.name == "O<" do
      throwFrontier m!"proveTotality: well-founded relation {just.wfRel.name} \
          unsupported (frontier: o< only)"
    let some row := MeasureShape.ofJustification? just
      | throwFrontier m!"proveTotality: measure {repr just.measure} with \
          measured subset {repr (just.measuredSubset.map (·.name))} is not a \
          registered measure-table row (frontier)"
    -- D9: the (o-p (measure)) obligation is absorbed by the Nat-typed
    -- measure; SHAPE-CHECK it (hard-fail on anything unexpected)
    unless just.terminationClauses.any
        (· == ACL2.Replay.opObligationClause just.measure) do
      throwFrontier m!"proveTotality: expected (o-p {repr just.measure}) \
          obligation not found (emission shape changed?)"
    -- the recorded route is 1-ary ONLY for now (audit F4: at other arities
    -- the wrapper lemmas and the self-call decrease are μ-typed against
    -- the table row, and a mismatched μ aborts UNTAGGED instead of
    -- frontiering — gate it here).
    let recTerm? := if formals.length == 1 then recTerm? else none
    match row with
    | .sumCount v1 v2 =>
      -- THE SUM ROW (audit F6's largest cell): both formals measured, so
      -- the induction is over the PAIR (`totality_2_rec_sum_mu`).
      match formals with
      | [f1, f2] =>
        unless v1 == f1 && v2 == f2 do
          throwFrontier m!"proveTotality: sum measure over \
              ({v1.name} {v2.name}) does not follow the formal order \
              ({f1.name} {f2.name}) — μ and the emitted decrease would \
              associate differently (frontier)"
        let envEat := fun (bv cv : Expr) => do
          let formalsE ← mkListLit (mkConst ``Symbol)
            [reflectSymbol f1, reflectSymbol f2]
          let avsE ← mkListLit (mkConst ``SExpr) [bv, cv]
          mkAppM ``bindArgs #[formalsE, avsE]
        let muAt := fun (a b : Expr) => do
          mkAppM ``HAdd.hAdd #[← mkAppM ``SExpr.consCount #[a],
            ← mkAppM ``SExpr.consCount #[b]]
        let μE ← withLocalDeclD `u1 (mkConst ``SExpr) fun u1 =>
          withLocalDeclD `u2 (mkConst ``SExpr) fun u2 => do
            mkLambdaFVars #[u1, u2] (← muAt u1 u2)
        let step ← withLocalDeclD `av1 (mkConst ``SExpr) fun av1 =>
          withLocalDeclD `av2 (mkConst ``SExpr) fun av2 => do
            let ihType ← withLocalDeclD `bv (mkConst ``SExpr) fun bv =>
              withLocalDeclD `cv (mkConst ``SExpr) fun cv => do
                let lt ← mkAppM ``Nat.lt #[← muAt bv cv, ← muAt av1 av2]
                let envB ← envEat bv cv
                let conv ← mkConvPropEx cfg.worldExpr envB (reflectSExpr body)
                mkForallFVars #[bv, cv] (← mkArrow lt conv)
            withLocalDeclD `ih ihType fun ih => do
              let envE ← envEat av1 av2
              let vals ← varProofs envE [av1, av2]
              let p ← totWalk cfg envE vals [] totalEnv
                (some (name, row, ih, just, none)) body
              mkLambdaFVars #[av1, av2, ih] p
        mkAppM ``totality_2_rec_sum_mu
          #[μE, cfg.worldExpr, reflectSymbol fs, reflectSymbol f1,
            reflectSymbol f2, reflectSExpr body, hNs, hDef, step]
      | _ =>
        throwFrontier m!"proveTotality: sum measure at arity \
            {formals.length} unsupported (frontier)"
    | _ =>
    let some measuredFormal := row.vars.head?
      | throwFrontier m!"proveTotality: measure row {row.headName} has no \
          measured variable (internal)"
    -- the induction MEASURE: the table ROW's registered μ head on the
    -- destructor route, the INTERPRETED count on the recorded route (μ is
    -- proof bookkeeping — design I1; the statement never mentions it).
    let muHead? : Option Lean.Name :=
      match row.muHeads with
      | some [h] => some h
      | _ => none
    let countOf (e : Expr) : MetaM Expr :=
      match recTerm? with
      | some info => mkAppM ``ACL2.Replay.interpCount
          #[cfg.worldExpr, reflectSymbol info.cntSym, e]
      | none =>
        match muHead? with
        | some h => mkAppM h #[e]
        | none => throwFrontier m!"proveTotality: measure row \
            {row.headName} has no registered μ and no recorded admission \
            replay to interpret it (frontier)"
    -- ONE μ for every arity arm — the table row's registered head (or the
    -- recorded route's `interpCount`), λ-abstracted. The `*_rec_mu` family
    -- is used uniformly: the old consCount-hardcoded `totality_N_rec`
    -- wrappers are exactly their `μ := consCount` instances.
    let μ1E : MetaM Expr :=
      withLocalDeclD `v (mkConst ``SExpr) fun v => do
        mkLambdaFVars #[v] (← countOf v)
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
            (some (name, row, ih, just, recTerm?)) body
          mkLambdaFVars #[av, ih] p
      mkAppM ``totality_1_rec_mu
        #[← μ1E, cfg.worldExpr, reflectSymbol fs, reflectSymbol f1,
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
                (some (name, row, ih, just, none)) body
              mkLambdaFVars #[av1, ih, av2] p
        mkAppM ``totality_2_rec_mu
          #[← μ1E, cfg.worldExpr, reflectSymbol fs, reflectSymbol f1,
            reflectSymbol f2, reflectSExpr body, hNs, hDef, step]
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
                (some (name, row, ih, just, none)) body
              mkLambdaFVars #[av2, ih, av1] p
        mkAppM ``totality_2_rec_mu_snd
          #[← μ1E, cfg.worldExpr, reflectSymbol fs, reflectSymbol f1,
            reflectSymbol f2, reflectSExpr body, hNs, hDef, step]
      else
        throwError "proveTotality: measured formal {measuredFormal.name} is \
            not among the formals (internal)"
    | [f1, f2, f3] =>
      -- 3-ary, measured on the FIRST (`ZIP3`, `recon-tests/16-three-way`)
      -- or SECOND (`FILTER`/`ALL-REL`'s `(fn x e)`) formal. Audit F7: the
      -- second-formal restriction was fitted to FILTER's shape while ZIP3
      -- sat in the corpus demanding the first — and the TP prover's twin
      -- already accepted both, so the two provers disagreed about what
      -- 3-ary meant. `totality_3_rec_fst_mu` (Lemmas/TotalityArity) is the
      -- missing lemma; third-formal measures stay an honest frontier.
      let fstMeasured := measuredFormal == f1
      unless fstMeasured || measuredFormal == f2 do
        throwFrontier m!"proveTotality: 3-ary measured formal \
            {measuredFormal.name} is neither the first nor the second \
            formal (frontier)"
      let envEat := fun (bv cv dv : Expr) => do
        let formalsE ← mkListLit (mkConst ``Symbol)
          [reflectSymbol f1, reflectSymbol f2, reflectSymbol f3]
        let avsE ← mkListLit (mkConst ``SExpr) [bv, cv, dv]
        mkAppM ``bindArgs #[formalsE, avsE]
      let step ← withLocalDeclD `avM (mkConst ``SExpr) fun avM => do
        let ihType ← withLocalDeclD `bv (mkConst ``SExpr) fun bv => do
          let lt ← mkAppM ``Nat.lt #[← countOf bv, ← countOf avM]
          let inner ← withLocalDeclD `ax (mkConst ``SExpr) fun ax =>
            withLocalDeclD `av3 (mkConst ``SExpr) fun av3 => do
              let envB ←
                if fstMeasured then envEat bv ax av3 else envEat ax bv av3
              let conv ← mkConvPropEx cfg.worldExpr envB (reflectSExpr body)
              mkForallFVars #[ax, av3] conv
          mkForallFVars #[bv] (← mkArrow lt inner)
        withLocalDeclD `ih ihType fun ih =>
          withLocalDeclD `ax (mkConst ``SExpr) fun ax =>
            withLocalDeclD `av3 (mkConst ``SExpr) fun av3 => do
              let envE ←
                if fstMeasured then envEat avM ax av3 else envEat ax avM av3
              let vals ← varProofs envE
                (if fstMeasured then [avM, ax, av3] else [ax, avM, av3])
              let p ← totWalk cfg envE vals [] totalEnv
                (some (name, row, ih, just, recTerm?)) body
              mkLambdaFVars #[avM, ih, ax, av3] p
      mkAppM (if fstMeasured then ``totality_3_rec_fst_mu
              else ``totality_3_rec_snd_mu)
        #[← μ1E, cfg.worldExpr, reflectSymbol fs, reflectSymbol f1,
          reflectSymbol f2, reflectSymbol f3, reflectSExpr body, hNs, hDef,
          step]
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
    (upTo : Option String := none)
    (termReplayed : List (String × Name × List String × List SExpr) := [])
    (hypFVars : List (String × Expr) := [])
    (tpCors : List (String × SExpr) := []) :
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
  let mut purePhaseDone := false
  while progress || !purePhaseDone do
    unless progress do purePhaseDone := true
    progress := false
    let mut still : List (Symbol × List Symbol × SExpr) := []
    for (s, formals, body) in pending do
      try
        -- RECORDED-TERMINATION route (sorting arc 2026-07-28): when this
        -- defun's admission waterfall was replayed as a replayed statement, assemble
        -- the bundle (byte-checks inside; frontier keeps the fn on the
        -- destructor route's honest frontier).
        -- PHASE ordering: the recorded route only fires once the PURE
        -- routes have SATURATED (`!progress` on the previous sweep of this
        -- pass — `pending` unchanged), so its hyp-backed augmentation
        -- covers only genuinely route-less dependencies (O<), not fns a
        -- later pure pass would have proved unconditionally.
        let recTerm? ←
          match purePhaseDone, termReplayed.find? (fun (n, _, _, _) => n == s.name),
                justs.lookup s.name with
          | true, some (_, c, conds, goalLits), some just =>
            try
              pure (some (← mkRecTermInfo cfg totalEnv hypFVars tpCors just
                c conds goalLits))
            catch e =>
              unless isFrontierErr e do throw e
              pure none
          | _, _, _ => pure none
        -- HYPOTHESIS-backed totality entries for the recorded route (audit
        -- F1 follow-through): the conjunct walk must converge O</ACL2-COUNT
        -- applications whose own admissions are beyond every route (O<'s
        -- O-FIRST-EXPT decreases). The telescope OFFERS their totality —
        -- augmenting with the hyp fvars makes the resulting proof honestly
        -- CONDITIONAL on them (Stage-5's kept recompute surfaces the fvars
        -- in the theorem's cond list; the audit verified that accounting
        -- fail-closes). Recorded-route calls only — the fixpoint's normal
        -- entries stay unconditional.
        let hypBacked : String × Expr → Option (String × Nat × Expr) :=
          fun (c, fv) =>
            if c.startsWith "total:" then
              let n := (c.drop "total:".length).toString
              if totalEnv.any (fun (m, _, _) => m == n) then none
              else
                (cfg.worldVal.defs.get? { name := n }).map
                  (fun (fs, _) => (n, fs.length, fv))
            else none
        let totalEnvFor := match recTerm? with
          | none => totalEnv
          | some _ => totalEnv ++ hypFVars.filterMap hypBacked
        let pf ← proveTotality cfg totalEnvFor s.name formals body
          (justs.lookup s.name) recTerm?
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

/-- Pin every argument term of a return-path call to a VALUE plus its
    convergence proof, then run the continuation (TP-replay arc increment
    5, 2026-08-13). A liftable argument is pinned by the DP value lift; an
    OPAQUE one (a user-fn call, e.g. `REV`'s `(REV (CDR X))`) by
    ∃-elimination over the plain totality walk — the same device the
    self-call arm uses for its non-measured argument. Needed because the
    ARGS-VALUED hypothesis shape (`mkTpHypTypeAv`) is stated at the
    argument VALUES, so a callee step must supply them. -/
partial def tpArgValues (cfg : ReplayConfig) (envE : Expr)
    (vals : List (Symbol × Expr × Expr))
    (facts : TotFacts)
    (totalEnv : List (String × Nat × Expr))
    (args : List SExpr) (acc : List (Expr × Expr))
    (k : List (Expr × Expr) → MetaM Expr) : MetaM Expr := do
  let varP : Symbol → Option (Expr × Expr) := fun s =>
    (vals.find? (fun (f, _, _) => f == s)).map (fun (_, v, p) => (v, p))
  match args with
  | [] => k acc.reverse
  | a :: rest =>
    if totLiftable a then
      let v ← dpValExpr [] (dpValProof.dpVarVal envE varP) a
      let p ← dpValProof cfg envE [] [] varP a
      tpArgValues cfg envE vals facts totalEnv rest ((v, p) :: acc) k
    else
      let hcEx ← totWalk cfg envE vals facts totalEnv none a
      let cont ← withLocalDeclD `av (mkConst ``SExpr) fun av => do
        let convTy ← mkAppM ``ConvTo
          #[cfg.worldExpr, envE, reflectSExpr a, av]
        withLocalDeclD `hcv convTy fun hcv => do
          mkLambdaFVars #[av, hcv]
            (← tpArgValues cfg envE vals facts totalEnv rest
              ((av, hcv) :: acc) k)
      mkAppM ``exists_conv_elim #[hcEx, cont]

-- THE TP PROVER (mutual since increment 3): the body walk, its call
-- arms, the CALLEE-TP arm, and `proveTp` itself — the callee arm proves
-- the CALLEE's prescription by re-entering the prover.
mutual

/-- The TP body walk: a proof of `ConvToP w envE t P` — the body converges
    to a value SATISFYING the lifted-corollary predicate `P` (the TP prover,
    lifter sprint 2026-07-06; the `memb_body_bool` route, mechanized).
    Return-path arms: quote leaves (`P` by kernel decision), `if`-splits
    (liftable or OPAQUE tests — tests need only CONVERGENCE, from the plain
    walk over `totalEnv`), self-calls (the admission-licensed strong IH),
    2-ary registered PRIMITIVES over ACL2's own emitted leaves (`kit`), and
    CALLEE calls whose own emitted type prescription supplies the position
    (`tpWalkCallee`, increment 3). Every other body shape is a tagged
    frontier (D6: the `tp:` hypothesis stays). -/
partial def tpWalk (cfg : ReplayConfig) (envE : Expr)
    (vals : List (Symbol × Expr × Expr))
    (facts : TotFacts)
    (totalEnv : List (String × Nat × Expr))
    (self : Option (String × Symbol × Expr × Justification))
    (kit : TpKit) (P : Expr) (t : SExpr) : MetaM Expr := do
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
      -- RETURN-PATH UNARY PRIMITIVE (the D-A consumer, 2026-08-14):
      -- ACL2 stores no type-prescription for its primitives, so the only
      -- statement it makes about such an occurrence is the emitted
      -- verdict (leaf or SUBTERM) — `tpTsLeaf` consumes exactly that plus
      -- the emitted type-alist. An unregistered head falls through to the
      -- call arms, which keep the honest frontier.
      match kit.cls with
      | some cls =>
        if tpTsUnary.any (fun (n, _, _, _) => n == qs.name) then
          tpTsLeaf cfg envE vals facts kit cls P t
        else tpWalkCall cfg envE vals facts totalEnv self kit P t
      | none => tpWalkCall cfg envE vals facts totalEnv self kit P t
  | .cons (.atom (.symbol fs)) (.cons c (.cons th (.cons e .nil))) =>
    if fs.name == "IF" then
      if totLiftable c then
        let vc ← dpValExpr [] (dpValProof.dpVarVal envE varP) c
        let hc ← dpValProof cfg envE [] [] varP c
        let toBoolVc ← mkAppM ``Logic.toBool #[vc]
        let mkB (bval : Name) (pos : Bool) (branch : SExpr) : MetaM Expr := do
          withLocalDeclD `hb (← mkEq toBoolVc (mkConst bval)) fun hb => do
            let p ← tpWalk cfg envE vals ((c, pos, hb, none) :: facts)
              totalEnv self kit P branch
            mkLambdaFVars #[hb] p
        let ht ←
          if ← isDefEq vc (mkConst ``SExpr.nil) then
            -- VACUOUS truthy branch (`mkVacuousTruthyBranch`, shared with
            -- the totality walk): `(COMPLEX-RATIONALP _)` in ACL2-COUNT's
            -- own body is definitionally nil on the complex-free value
            -- space, so the branch hypothesis refutes itself. ACL2 emits a
            -- real verdict for that leaf — the vacuity is OURS (BUG-009's
            -- pinned domain restriction), and it fails CLOSED if complex
            -- values are ever modelled.
            mkVacuousTruthyBranch toBoolVc
              (← mkAppM ``ConvToP
                #[cfg.worldExpr, envE, reflectSExpr th, P])
          else mkB ``Bool.true true th
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
                let p ← tpWalk cfg envE vals
                  ((c, pos, hb, some (vc, hcv)) :: facts)
                  totalEnv self kit P branch
                mkLambdaFVars #[vc, hcv, hb] p
        let ht ← mkB ``Bool.true true th
        let he ← mkB ``Bool.false false e
        return ← mkAppM ``convP_if_split_ex
          #[cfg.worldExpr, envE, reflectSExpr c, reflectSExpr th,
            reflectSExpr e, P, hcEx, ht, he]
    else
      tpWalkCall cfg envE vals facts totalEnv self kit P t
  | .cons (.atom (.symbol fs)) (.cons a (.cons b .nil)) =>
    -- RETURN-PATH PRIMITIVE (TP-replay arc increments 1–2, 2026-08-12): a
    -- 2-ary registered builtin ACL2 itself enumerated as a return-path
    -- LEAF of this fn's type prescription. ADMISSIBILITY IS ENTIRELY
    -- EMITTED — the term must be one of ACL2's `:LEAVES` and the type-set
    -- verdict ACL2 computed for it must lie inside the corollary class's
    -- type-set. The Lean side contributes only the class's value CLOSURE
    -- lemma and its ARG-OBLIGATION PROFILE; it never derives a type.
    -- Anything unregistered falls through to the call arms (self-call,
    -- else frontier).
    match dpBinary.lookup fs.name, kit.cls with
    | some (fn, cb), some cls =>
      let some (prof, closure) := tpClosure2.lookup (cls, fs.name)
        | throwFrontier m!"proveTp: return-path {fs.name} has no value-closure \
            lemma for the {repr cls} corollary class (frontier)"
      tpEmittedLeafOk kit cls t
      -- PER-ARGUMENT obligation, off the registered PROFILE: a constrained
      -- position carries `P` (the TP walk); an unconstrained one carries
      -- only `TpArgAny`, i.e. plain convergence by the totality walk — the
      -- Lean side never invents a type for it
      let argOf (constrained : Bool) (u : SExpr) : MetaM (Expr × Expr) := do
        if constrained then
          return (P, ← tpWalk cfg envE vals facts totalEnv self kit P u)
        else
          let hEx ← totWalk cfg envE vals facts totalEnv none u
          return (mkConst ``ACL2.Replay.TpArgAny, ← mkAppM ``convP_any #[hEx])
      let (pA, pa) ← argOf prof.fstConstrained a
      let (pB, pb) ← argOf prof.sndConstrained b
      let hNs ← proveNotSpecial fs
      let hNo ← proveNoShadow cfg fs
      -- the CLOSURE obligation, RECOMPUTED from the driver's own `P` and
      -- the profile's per-argument predicates — a registered lemma that
      -- does not state exactly this (wrong class, or a profile claiming
      -- more/less than the lemma proves) fails here
      let clTy ← withLocalDeclD `u (mkConst ``SExpr) fun u =>
        withLocalDeclD `v (mkConst ``SExpr) fun v => do
          let pg := (mkApp P (mkApp2 (mkConst fn) u v)).headBeta
          mkForallFVars #[u, v]
            (← mkArrow (mkApp pA u).headBeta
              (← mkArrow (mkApp pB v).headBeta pg))
      -- an ARG-INDEXED class's facts take the residue argument's VALUE as
      -- their leading parameter (increment 5); the type hint below is
      -- still the whole check
      let closureE ←
        if cls.argIndexed then
          let some (av, _) := kit.argVar.bind varP
            | throwFrontier m!"proveTp: the {repr cls} residue argument has \
                no bound value in {kit.fnName}'s walk (frontier)"
          pure (mkApp (mkConst closure) av)
        else pure (mkConst closure)
      let hcl ← mkExpectedTypeHint closureE clTy
      return ← mkAppM ``convP_builtin2
        #[cfg.worldExpr, envE, reflectSymbol fs, reflectSExpr a,
          reflectSExpr b, mkConst fn, P, pA, pB, hNs, hNo, mkConst cb,
          hcl, pa, pb]
    | _, _ => tpWalkCall cfg envE vals facts totalEnv self kit P t
  | .atom (.symbol vsym) =>
    -- RESIDUE-ARGUMENT LEAF (TP-replay arc increment 5, 2026-08-13):
    -- `BINARY-APPEND`/`APP` return their second argument `Y` on the
    -- base path, and ACL2's own corollary covers exactly that leaf by
    -- its EQUALITY disjunct `(EQUAL (fn X Y) Y)` — which is why the
    -- emitted verdict there is the unknown `-1` and no mask applies.
    -- ADMISSIBILITY IS EMITTED: the variable must BE the corollary's
    -- residue argument (`tpCorArgVar?` of the fn's own corollary) and
    -- must be one of ACL2's enumerated `:LEAVES`. Any other return-path
    -- variable is a frontier.
    let some cls := kit.cls
      | throwFrontier m!"proveTp: return-path variable {vsym.name} under an \
          UNRECOGNIZED corollary class for {kit.fnName} (frontier)"
    -- NOT the args-valued residue argument: the variable is an ordinary
    -- return-path leaf, and ACL2's own type-alist for the ADDRESSED leaf
    -- says what it is on this branch (the D-A consumer, 2026-08-14) —
    -- INTEGER-ABS's `X` leaf under `(INTEGERP X) ∧ ¬(< X '0)`.
    unless kit.argVar == some vsym do
      return ← tpTsLeaf cfg envE vals facts kit cls P t
    let some leafFact := tpArgLeafFact.lookup cls
      | throwFrontier m!"proveTp: the {repr cls} corollary class has no \
          residue-leaf fact — a return-path variable {vsym.name} is not \
          covered by it (frontier)"
    unless kit.argVar == some vsym do
      throwFrontier m!"proveTp: return-path variable {vsym.name} is not \
          {kit.fnName}'s corollary residue argument (frontier)"
    unless kit.leaves.any (fun l => l.term == t) do
      throwFrontier m!"proveTp: {repr t} is not an emitted \
          :TYPE-PRESCRIPTION leaf of {kit.fnName} (frontier)"
    let some (av, hav) := varP vsym
      | throwFrontier m!"proveTp: residue argument {vsym.name} has no bound \
          value (frontier)"
    -- RECOMPUTED against the driver's own `P` at that value
    let hP ← mkExpectedTypeHint (mkApp (mkConst leafFact) av)
      (mkApp P av).headBeta
    -- every implicit given (the predicate is higher-order: inference from
    -- `hP`'s concrete type alone would mis-solve `P`/`v`)
    return ← mkAppOptM ``convP_of_val
      #[cfg.worldExpr, envE, reflectSExpr t, P, av, hP, hav]
  | _ => tpWalkCall cfg envE vals facts totalEnv self kit P t
/-- Call arms: the SELF-call via the strong IH; a call to ANOTHER
    function via that callee's own type prescription (`tpWalkCallee`);
    everything else a frontier. -/
partial def tpWalkCall (cfg : ReplayConfig) (envE : Expr)
    (vals : List (Symbol × Expr × Expr))
    (facts : TotFacts)
    (totalEnv : List (String × Nat × Expr))
    (self : Option (String × Symbol × Expr × Justification))
    (kit : TpKit) (P : Expr) (t : SExpr) : MetaM Expr := do
  let varP : Symbol → Option (Expr × Expr) := fun s =>
    (vals.find? (fun (f, _, _) => f == s)).map (fun (_, v, p) => (v, p))
  let .cons (.atom (.symbol fs)) argsSpine := t
    | throwFrontier m!"proveTp: body shape {repr t} unsupported (frontier)"
  let args := (argsSpine.toList?).getD []
  -- NOT the self-call: the only admissible route is the CALLEE's OWN
  -- emitted type prescription (increment 3). Reachable from a
  -- non-recursive body too — `self` is consulted only to recognize the
  -- self-call, never to license the callee route.
  let isSelfCall : Bool := match self with
    | some (selfName, _, _, _) => fs.name == selfName
    | none => false
  unless isSelfCall do
    return ← tpWalkCallee cfg envE vals facts totalEnv kit P t fs args
  let some (selfName, measuredFormal, ih, just) := self
    | throwFrontier m!"proveTp: call to {fs.name} on the return path of a \
        non-recursive body (frontier)"
  unless fs.name == selfName do
    throwFrontier m!"proveTp: return-path call to {fs.name} (not the \
        self-call) unsupported (frontier)"
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
    let kit : DecreaseKit := {
      cfg := cfg, envE := envE
      facts := facts.map (fun (f, pos, _) => (f, pos))
      valOf := fun u => dpValExpr [] (dpValProof.dpVarVal envE varP) u
      convOf := fun u => dpValProof cfg envE [] [] varP u
      conspTrueOf := fun b => do
        let conspTest : SExpr :=
          .cons (.atom (.symbol { name := "CONSP" })) (.cons b .nil)
        match facts.find? (fun (f, pos, _) => f == conspTest && pos) with
        | some (_, _, pf, _) => pure pf
        | none => throwFrontier m!"dischargeDecrease: decrease at \
            {repr b} needs an in-scope (consp {repr b}) fact (frontier)"
      endpFalseOf := fun b => do
        let endpTest : SExpr :=
          .cons (.atom (.symbol { name := "ENDP" })) (.cons b .nil)
        match facts.find? (fun (f, pos, _) => f == endpTest && !pos) with
        | some (_, _, pf, _) => pure pf
        | none => throwFrontier m!"dischargeDecrease: registry decrease \
            at {repr b} needs a refuted (endp {repr b}) fact (frontier)"
      -- the GENERAL accessor: the TP walk's facts carry each ruling test's
      -- `toBool = <sign>` proof, so an arbitrary ruler is a direct lookup
      factOf? := fun test pos => pure
        ((facts.find? (fun (f, p, _) => f == test && p == pos)).map
          (fun (_, _, pf, _) => pf)) }
    let dec ← dischargeDecrease just
      formals (formals.map (fun f => .atom (.symbol f)))
      formals args kit
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
    | [f1, f2, f3], [a1, a2, a3] =>
      -- 3-ary self-call (TP-replay arc increment 4, 2026-08-13):
      -- `(ALL-REL FN (CDR X) E)` / `(ZIP3 (CDR X) (CDR Y) (CDR Z))`. The
      -- IH's argument order is (measured value, decrease, the remaining
      -- values in FORMAL order) — the `tp_3_rec`/`tp_3_rec_snd` shape,
      -- mirroring `proveTotality`'s 3-ary scaffold. A non-measured
      -- argument that is not liftable is a frontier here (the 2-ary
      -- opaque ∃-elimination has no 3-ary customer yet).
      let vals3 ← [a1, a2, a3].mapM fun a => do
        unless totLiftable a do
          throwFrontier m!"proveTp: 3-ary self-call argument {repr a} not \
              liftable (frontier)"
        let v ← dpValExpr [] (dpValProof.dpVarVal envE varP) a
        let p ← dpValProof cfg envE [] [] varP a
        pure (v, p)
      let vs := vals3.map (·.1)
      let ps := vals3.map (·.2)
      let others := (List.range 3).filter (· != mIdx)
      let hbody ← mkAppM' ih (#[vs[mIdx]!, dec] ++ (others.map (vs[·]!)).toArray)
      return ← mkAppM ``convP_defn_3
        #[cfg.worldExpr, envE, reflectSymbol fs, reflectSExpr a1,
          reflectSExpr a2, reflectSExpr a3, vs[0]!, vs[1]!, vs[2]!,
          reflectSymbol f1, reflectSymbol f2, reflectSymbol f3,
          reflectSExpr body, P, hNs, hDef, ps[0]!, ps[1]!, ps[2]!, hbody]
    | _, _ =>
      throwFrontier m!"proveTp: self-call arity {args.length} unsupported \
          (frontier)"

/-- The CALLEE-TP return-path arm (TP-replay arc increment 3, 2026-08-13):
    a return-path call to a function OTHER than the one whose prescription
    is being proved — `SORTFN1`'s `(SORTFN1-INSERT (CAR X) (SORTFN1 (CDR X)))`
    leaf, or the `BINARY-+` summand `(HOW-MANY-SMALLER (CAR X) (CDR X))`
    inside `BNEXT-SIZE`'s. ADMISSIBILITY IS ENTIRELY EMITTED:
    * the callee is a world fn with its OWN emitted `:TYPE-PRESCRIPTION`
      corollary (`kit.cors` — the caller's own offer table), in a
      recognized class;
    * that class either IS the position's class, or IMPLIES it by a
      registered `tpClassImp` fact whose direction is cross-checked
      against ACL2's own emitted type-set masks;
    * the call OCCURS in ACL2's `:LEAVES` enumeration for the fn being
      proved and — when the call IS one of those leaves — the verdict
      ACL2 computed for it lies inside the position class's type-set (a
      NESTED position is covered by the enclosing leaf's own check, in
      the arm that admitted it).
    The P-fact is not assumed: the prover runs RECURSIVELY on the callee
    (cycle-guarded by `kit.seen`, with the caller's own justification and
    totality data), so the callee's prescription is proved from ITS body
    and ITS emitted corollary by exactly this machinery. The call's
    CONVERGENCE is the plain totality walk. -/
partial def tpWalkCallee (cfg : ReplayConfig) (envE : Expr)
    (vals : List (Symbol × Expr × Expr))
    (facts : TotFacts)
    (totalEnv : List (String × Nat × Expr))
    (kit : TpKit) (P : Expr) (t : SExpr) (fs : Symbol) (args : List SExpr) :
    MetaM Expr := do
  let some cls := kit.cls
    | throwFrontier m!"proveTp: return-path call to {fs.name} under an \
        UNRECOGNIZED corollary class for {kit.fnName} (frontier)"
  let some (gFormals, _) := cfg.worldVal.defs.get? fs
    | throwFrontier m!"proveTp: return-path call to {fs.name}, which is not \
        a world fn (frontier)"
  unless args.length == gFormals.length do
    throwFrontier m!"proveTp: return-path call arity mismatch {repr t} \
        (frontier)"
  let some gcor := kit.cors.lookup fs.name
    | throwFrontier m!"proveTp: {fs.name} has no emitted \
        :TYPE-PRESCRIPTION corollary (frontier)"
  let gAppPat : SExpr :=
    .cons (.atom (.symbol fs))
      ((gFormals.map (SExpr.atom ∘ Atom.symbol)).foldr SExpr.cons .nil)
  let some gcls := tpCorClass? gAppPat gcor
    | throwFrontier m!"proveTp: {fs.name}'s emitted corollary {repr gcor} is \
        not a recognized class (frontier)"
  -- ACL2'S OWN LEAF DATA (shared with the primitive arm)
  tpEmittedLeafOk kit cls t
  -- CYCLE GUARD: never re-enter a prescription already on the stack
  if kit.seen.contains fs.name then
    throwFrontier m!"proveTp: CYCLE in the callee-TP chain {kit.seen} → \
        {fs.name} (frontier)"
  -- the direction check both implication registries share: a registered
  -- entry whose direction ACL2's own emitted type-set masks contradict is
  -- refused
  let checkedImp (reg : List ((TpCorClass × TpCorClass) × Name)) :
      MetaM Name := do
    let some n := reg.lookup (gcls, cls)
      | throwFrontier m!"proveTp: {fs.name}'s corollary class {repr gcls} \
          neither matches nor implies the {repr cls} class \
          {kit.fnName}'s prescription needs (frontier)"
    unless tsSubsumed gcls.tsMask cls.tsMask do
      throwFrontier m!"proveTp: registered class implication {repr gcls} ⇒ \
          {repr cls} contradicts the emitted type-set masks \
          ({gcls.tsMask} not inside {cls.tsMask}) (frontier)"
    pure n
  let hEx ← totWalk cfg envE vals facts totalEnv none t
  if gcls.argIndexed then
    -- ARGS-VALUED CALLEE (TP-replay arc increment 5, 2026-08-13):
    -- `REV`'s `(APP (REV (CDR X)) (CONS (CAR X) 'NIL))` leaf. The callee's
    -- own prescription is the args-valued shape — "a cons, OR the residue
    -- ARGUMENT's value" — so the position's predicate follows only once it
    -- holds of that argument's value too. That premise is PROVED, by
    -- walking the residue argument under the position's own predicate
    -- (the same walker, the same registries); nothing is assumed about it.
    let some gArgVar := tpCorArgVar? gAppPat gcor
      | throwFrontier m!"proveTp: {fs.name}'s corollary is arg-indexed but \
          its residue argument does not resolve (frontier)"
    let some gArgIdx := gFormals.findIdx? (· == gArgVar)
      | throwFrontier m!"proveTp: {fs.name}'s residue argument \
          {gArgVar.name} is not one of its formals (frontier)"
    let impName ← checkedImp tpClassImpAv
    let gTp ← proveTp cfg totalEnv kit.justs fs.name gcor
      (cors := kit.cors) (seen := kit.seen) (argValued := true)
    tpArgValues cfg envE vals facts totalEnv args [] fun avs => do
      let (yv, hyConv) := avs[gArgIdx]!
      -- the POSITION's predicate at the residue argument's value
      let hresWalk ← tpWalk cfg envE vals facts totalEnv none kit P
        args[gArgIdx]!
      let hresY ← mkAppM ``convP_at_val #[hresWalk, hyConv]
      let hP ← withLocalDeclD `v (mkConst ``SExpr) fun vV => do
        let convTy ← mkValConvPropEx cfg.worldExpr envE (reflectSExpr t) vV
        withLocalDeclD `hc convTy fun hc => do
          let inst := mkAppN gTp
            (#[envE] ++ (args.map reflectSExpr).toArray ++
             (avs.map (·.1)).toArray ++ #[vV] ++
             (avs.map (·.2)).toArray ++ #[hc])
          let body := mkAppN (mkConst impName) #[yv, vV, hresY, inst]
          mkLambdaFVars #[vV, hc]
            (← mkExpectedTypeHint body (mkApp P vV).headBeta)
      return mkAppN (mkConst ``ACL2.Replay.convP_of_conv_ex)
        #[cfg.worldExpr, envE, reflectSExpr t, P, hEx, hP]
  else
    -- CLASS MATCH: same class, or a registered implication whose direction
    -- ACL2's own emitted type-set masks confirm
    let imp? : Option Name ←
      if gcls == cls then pure none else pure (some (← checkedImp tpClassImp))
    let gTp ← proveTp cfg totalEnv kit.justs fs.name gcor
      (cors := kit.cors) (seen := kit.seen)
    -- the position's obligation, RECOMPUTED from the driver's own `P`:
    -- `∀ v, (the call converges to v) → P v`. A callee proof of the wrong
    -- statement, or a class implication that does not close the gap, fails
    -- at this type hint (kernel-backed at `Meta.check`).
    let hP ← withLocalDeclD `v (mkConst ``SExpr) fun vV => do
      let convTy ← mkValConvPropEx cfg.worldExpr envE (reflectSExpr t) vV
      withLocalDeclD `hc convTy fun hc => do
        let inst := mkAppN gTp
          (#[envE] ++ (args.map reflectSExpr).toArray ++ #[vV, hc])
        let body := match imp? with
          | none => inst
          | some n => mkApp2 (mkConst n) vV inst
        mkLambdaFVars #[vV, hc]
          (← mkExpectedTypeHint body (mkApp P vV).headBeta)
    return mkAppN (mkConst ``ACL2.Replay.convP_of_conv_ex)
      #[cfg.worldExpr, envE, reflectSExpr t, P, hEx, hP]

/-- Prove `tp:fn` (the `mkTpHypType` statement) from the fn's body and its
    EMITTED `:TYPE-PRESCRIPTION` corollary — the TP prover. The corollary is
    CONSUMED (ACL2's emitted type fact — never inferred); the walk proves the
    body's value satisfies it; argument strictness + determinism pin every
    convergence value (`tp_hyp_*_of_body`). Frontier failures are tagged
    (D6: the hypothesis stays visible).
    `seen` is the CALLEE-TP recursion stack (increment 3): the prescriptions
    already being proved further up. An empty stack is the ordinary entry
    point; `tpWalkCallee` re-enters with the caller's stack, and a fn that
    is already on it is a cycle (frontier, never an assumption).
    `argValued` (increment 5) targets the ARGS-VALUED hypothesis shape
    instead (`mkTpHypTypeAv`): the corollary's bare-formal occurrences —
    `BINARY-APPEND`'s `(EQUAL (BINARY-APPEND X Y) Y)` disjunct — lift to
    the ARGUMENT VALUES, so the predicate is built under the walk's own
    argument binders and the assembly is the `*_av` lemma family. -/
partial def proveTp (cfg : ReplayConfig)
    (totalEnv : List (String × Nat × Expr))
    (justs : List (String × Justification))
    (name : String) (cor : SExpr)
    (cors : List (String × SExpr) := []) (seen : List String := [])
    (argValued : Bool := false) :
    MetaM Expr := do
  let fs : Symbol := { name := name }
  let some (formals, body) := cfg.worldVal.defs.get? fs
    | throwFrontier m!"proveTp: {name} not defined in the world (frontier)"
  let hNs ← proveNotSpecial fs
  let hDef ← totWalk.totDefFact cfg fs formals body
  -- P := fun v => <corollary, (fn formals…) ↦ v, value-lifted> = SExpr.t —
  -- EXACTLY mkTpHypType's conclusion, so the proof inhabits the offered
  -- type. In the ARGS-VALUED mode a bare FORMAL occurrence lifts to that
  -- argument's bound VALUE instead of frontiering — exactly
  -- `mkTpHypTypeAv`'s lift, so `mkP avs` at the walk's binders IS the
  -- offered hypothesis's predicate at those arguments.
  let appPat : SExpr :=
    .cons (.atom (.symbol fs))
      ((formals.map (SExpr.atom ∘ Atom.symbol)).foldr SExpr.cons .nil)
  let mkP (avs : List Expr) : MetaM Expr :=
    withLocalDeclD `v (mkConst ``SExpr) fun vV => do
      let lifted ← dpValExpr [(appPat, vV)]
        (fun s => do
          unless argValued do
            throwFrontier m!"proveTp: corollary of {name} mentions the \
                free variable {s.name} outside the application (frontier)"
          let some i := formals.findIdx? (· == s)
            | throwFrontier m!"proveTp: corollary of {name} mentions the \
                free variable {s.name} outside the application/formals \
                (frontier)"
          let some e := avs[i]?
            | throwFrontier m!"proveTp: corollary of {name} mentions the \
                formal {s.name}, which has no bound argument value here \
                (frontier)"
          pure e) cor
      mkLambdaFVars #[vV] (← mkEq lifted (mkConst ``SExpr.t))
  -- the EMITTED return-path data this fn's walk may consume: ACL2's own
  -- `:LEAVES` (leaf term + type-set verdict) and the corollary's class
  let kit : TpKit :=
    { fnName := name, leaves := (cfg.tpLeaves.lookup name).getD []
      cls := tpCorClass? appPat cor
      justs := justs, cors := cors, seen := name :: seen
      argVar := if argValued then tpCorArgVar? appPat cor else none }
  let mkEnvE (avs : List Expr) : MetaM Expr := do
    let formalsE ← mkListLit (mkConst ``Symbol) (formals.map reflectSymbol)
    let avsE ← mkListLit (mkConst ``SExpr) avs
    mkAppM ``bindArgs #[formalsE, avsE]
  let varProofs (envE : Expr) (avs : List Expr) :
      MetaM (List (Symbol × Expr × Expr)) :=
    bindArgsVarProofs cfg "proveTp" envE formals avs
  -- the D5 admission scope shared by both modes: `o<` on
  -- `(acl2-count <single measured formal>)`
  -- classified through the SAME measure table as `proveTotality` (R3,
  -- 2026-08-14) so the two provers cannot disagree about what a measure
  -- shape IS. The TP assembly's `tp_*_rec` wrappers are `consCount`-typed
  -- throughout, so only the `count` ROW is assemblable here; every other
  -- registered row keeps its own honest frontier (widening it means
  -- μ-generic `tp_*_rec_mu` twins, not a new classifier).
  let measuredOf (just : Justification) : MetaM Symbol := do
    unless just.wfRel.name == "O<" do
      throwFrontier m!"proveTp: well-founded relation {just.wfRel.name} \
          unsupported (frontier: o< only)"
    let some row := MeasureShape.ofJustification? just
      | throwFrontier m!"proveTp: measure {repr just.measure} with measured \
          subset {repr (just.measuredSubset.map (·.name))} is not a \
          registered measure-table row (frontier)"
    match row with
    | .count v => pure v
    | _ =>
      throwFrontier m!"proveTp: measure-table row {row.headName} has no \
          consCount-typed TP assembly (frontier: the `count` row only)"
  if argValued then
    -- THE ARGS-VALUED ASSEMBLY (increment 5). Only the shape the corpus
    -- demands is covered — 2-ary, recursive, measured on the FIRST formal
    -- (`BINARY-APPEND`/`APP`); anything else keeps the honest frontier.
    let some just := justs.lookup name
      | throwFrontier m!"proveTp: args-valued {name} is not recursive \
          (frontier)"
    let measuredFormal ← measuredOf just
    let countOf (e : Expr) : MetaM Expr := mkAppM ``SExpr.consCount #[e]
    match formals with
    | [f1, f2] =>
      unless measuredFormal == f1 do
        throwFrontier m!"proveTp: args-valued 2-ary measured formal \
            {measuredFormal.name} is not the first formal (frontier)"
      let Pav ← withLocalDeclD `u0 (mkConst ``SExpr) fun u0 =>
        withLocalDeclD `u1 (mkConst ``SExpr) fun u1 => do
          mkLambdaFVars #[u0, u1] (← mkP [u0, u1])
      let step ← withLocalDeclD `av1 (mkConst ``SExpr) fun av1 => do
        let ihType ← withLocalDeclD `bv (mkConst ``SExpr) fun bv => do
          let lt ← mkAppM ``Nat.lt #[← countOf bv, ← countOf av1]
          let inner ← withLocalDeclD `cv (mkConst ``SExpr) fun cv => do
            let ty ← mkAppM ``ConvToP #[cfg.worldExpr, ← mkEnvE [bv, cv],
              reflectSExpr body, ← mkP [bv, cv]]
            mkForallFVars #[cv] ty
          mkForallFVars #[bv] (← mkArrow lt inner)
        withLocalDeclD `ih ihType fun ih =>
          withLocalDeclD `av2 (mkConst ``SExpr) fun av2 => do
            let envE ← mkEnvE [av1, av2]
            let vals ← varProofs envE [av1, av2]
            let p ← tpWalk cfg envE vals [] totalEnv
              (some (name, measuredFormal, ih, just)) kit (← mkP [av1, av2])
              body
            mkLambdaFVars #[av1, ih, av2] p
      let hbody ← mkAppM ``tp_2_rec_av
        #[reflectSymbol f1, reflectSymbol f2, reflectSExpr body,
          cfg.worldExpr, Pav, step]
      return ← mkAppM ``tp_hyp_2_av_of_body
        #[cfg.worldExpr, reflectSymbol fs, reflectSymbol f1,
          reflectSymbol f2, reflectSExpr body, Pav, hNs, hDef, hbody]
    | _ =>
      throwFrontier m!"proveTp: args-valued arity {formals.length} \
          unsupported (frontier)"
  -- the VALUE-ONLY predicate (`mkTpHypType`'s): built with no argument
  -- values in scope, so a bare-formal occurrence is the honest frontier
  let P ← mkP []
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
        let p ← tpWalk cfg envE vals [] totalEnv none kit P body
        mkLambdaFVars #[av] p
      mkAppM ``tp_hyp_1_of_body
        #[cfg.worldExpr, reflectSymbol fs, reflectSymbol f1,
          reflectSExpr body, P, hNs, hDef, hbody]
    | [f1, f2] =>
      let hbody ← withLocalDeclD `av1 (mkConst ``SExpr) fun av1 =>
        withLocalDeclD `av2 (mkConst ``SExpr) fun av2 => do
          let envE ← mkEnvE [av1, av2]
          let vals ← varProofs envE [av1, av2]
          let p ← tpWalk cfg envE vals [] totalEnv none kit P body
          mkLambdaFVars #[av1, av2] p
      mkAppM ``tp_hyp_2_of_body
        #[cfg.worldExpr, reflectSymbol fs, reflectSymbol f1,
          reflectSymbol f2, reflectSExpr body, P, hNs, hDef, hbody]
    | _ => throwFrontier m!"proveTp: arity {formals.length} unsupported (frontier)"
  | some just =>
    -- RECURSIVE (D5 scope, as in proveTotality)
    let measuredFormal ← measuredOf just
    let countOf (e : Expr) : MetaM Expr := mkAppM ``SExpr.consCount #[e]
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
          let p ← tpWalk cfg envE vals [] totalEnv (selfC ih) kit P body
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
                let p ← tpWalk cfg envE vals [] totalEnv (selfC ih) kit P body
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
                let p ← tpWalk cfg envE vals [] totalEnv (selfC ih) kit P body
                mkLambdaFVars #[av2, ih, av1] p
        else
          -- (unreached: the 2-ary arm's measured formal is f1 or f2 by
          -- construction) — TAGGED like proveTotality's twin, so a future
          -- reachable path keeps the hypothesis instead of aborting
          throwFrontier m!"proveTp: measured formal not among the formals \
              (frontier)"
      let recLemma :=
        if measuredFormal == f1 then ``tp_2_rec else ``tp_2_rec_snd
      let hbody ← mkAppM recLemma
        #[reflectSymbol f1, reflectSymbol f2, reflectSExpr body,
          cfg.worldExpr, P, step]
      mkAppM ``tp_hyp_2_of_body
        #[cfg.worldExpr, reflectSymbol fs, reflectSymbol f1,
          reflectSymbol f2, reflectSExpr body, P, hNs, hDef, hbody]
    | [f1, f2, f3] =>
      -- 3-ary (TP-replay arc increment 4, 2026-08-13): the measured
      -- formal's POSITION is read off the emitted justification, never
      -- special-cased — `ZIP3` is measured on its first formal, `ALL-REL`
      -- and `FILTER` on their second (the `(fn x e)` shape). The third
      -- position has no corpus customer and stays a tagged frontier.
      let mIdx3 := [f1, f2, f3].findIdx (· == measuredFormal)
      let others := (List.range 3).filter (· != mIdx3)
      let step ←
        if mIdx3 ≥ 2 then
          throwFrontier m!"proveTp: 3-ary measured formal \
              {measuredFormal.name} is not the first or second formal \
              (frontier)"
        else
          withLocalDeclD `avm (mkConst ``SExpr) fun avm => do
            let envAt := fun (mv o1 o2 : Expr) => do
              let avs := (List.range 3).map fun i =>
                if i == mIdx3 then mv else if i == others[0]! then o1 else o2
              mkEnvE avs
            let ihType ← withLocalDeclD `bv (mkConst ``SExpr) fun bv => do
              let lt ← mkAppM ``Nat.lt #[← countOf bv, ← countOf avm]
              let inner ← withLocalDeclD `ov1 (mkConst ``SExpr) fun ov1 =>
                withLocalDeclD `ov2 (mkConst ``SExpr) fun ov2 => do
                  mkForallFVars #[ov1, ov2]
                    (← mkConvToPTy (← envAt bv ov1 ov2))
              mkForallFVars #[bv] (← mkArrow lt inner)
            withLocalDeclD `ih ihType fun ih =>
              withLocalDeclD `av1 (mkConst ``SExpr) fun av1 =>
                withLocalDeclD `av2 (mkConst ``SExpr) fun av2 => do
                  let envE ← envAt avm av1 av2
                  let avs := (List.range 3).map fun i =>
                    if i == mIdx3 then avm
                    else if i == others[0]! then av1 else av2
                  let vals ← varProofs envE avs
                  let p ← tpWalk cfg envE vals [] totalEnv (selfC ih) kit P body
                  mkLambdaFVars #[avm, ih, av1, av2] p
      let recLemma := if mIdx3 == 0 then ``tp_3_rec else ``tp_3_rec_snd
      let hbody ← mkAppM recLemma
        #[reflectSymbol f1, reflectSymbol f2, reflectSymbol f3,
          reflectSExpr body, cfg.worldExpr, P, step]
      mkAppM ``tp_hyp_3_of_body
        #[cfg.worldExpr, reflectSymbol fs, reflectSymbol f1,
          reflectSymbol f2, reflectSymbol f3, reflectSExpr body, P, hNs,
          hDef, hbody]
    | _ => throwFrontier m!"proveTp: recursive arity {formals.length} \
        unsupported (frontier)"

end

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
    Entry: rule name ↦ (the constant, the primitives' no-shadow fns, in
    the constant's hypothesis order). A ground-zero rule name can never
    collide with a user rule — ACL2 refuses the redefinition at
    admission. -/
def d5GzRules : List (String × Name × List String) :=
  [("LEXORDER-REFLEXIVE",  (``gz_rule_lexorder_reflexive,  ["LEXORDER"])),
   ("LEXORDER-TRANSITIVE", (``gz_rule_lexorder_transitive, ["LEXORDER"])),
   ("DEFAULT-CAR",         (``gz_rule_default_car,
                            ["CAR", "CONSP", "NOT"])),
   ("DEFAULT-CDR",         (``gz_rule_default_cdr,
                            ["CDR", "CONSP", "NOT"])),
   ("CONS-CAR-CDR",        (``gz_rule_cons_car_cdr,
                            ["CONSP", "CAR", "CDR", "CONS"])),
   ("FOLD-CONSTS-IN-+",    (``gz_rule_fold_consts_in_plus, ["BINARY-+"]))]

/-- Discharge a GROUND-ZERO rule's `rule:<name>` hypothesis by its D5
    prelude constant: instantiate at the theorem's world + the primitives'
    no-shadow facts, then type-hint against the hypothesis type built FROM
    THE EMITTED SPEC (`mkRuleHypType`) — a drifted emission or a mis-stated
    constant fails here (fail-closed recompute-check, kernel-backed at
    `Meta.check`). -/
def dischargeGzRuleHyp (cfg : ReplayConfig) (spec : RuleSpec) (decl : Name)
    (noShadowFns : List String) : MetaM Expr := do
  let mut e := mkApp (mkConst decl) cfg.worldExpr
  for fn in noShadowFns do
    e := mkApp e (← proveNoShadow cfg { name := fn })
  mkExpectedTypeHint e (← mkRuleHypType cfg spec)

/-- D1 REPLAYED REGISTRY (design §D1, WP4): replayed theorems as per-theorem
    Lean CONSTANTS. Entry: theorem name ↦ (the `addDecl`'d constant — type
    `∀ env, <kept-condition telescope> → EvTrue w ⟪Goal⟫` — and its kept
    condition strings, `total:`/`tp:`/`rule:` in telescope order).
    `dischargeRuleHyp` APPLIES the constant instead of re-replaying the
    dependency's tree per consumer — the kernel checks each proof once and a
    reference is O(1), collapsing the multiplicative dependency-tree blowup
    (the ≈557M-node perm-equivalence precedent, design §4).

    `formula` is the dependency's TRANSLATED Goal clause — the entry's
    identity beyond its name (WP5, the cross-book transfer: two books can
    each carry a theorem called TRUE-LISTP-RM, and a name-only lookup
    picks whichever came first). `crossBook` marks an entry produced by
    the WP5 pre-pass — a dependency book's tree replayed at the CONSUMER's
    world. Such an entry's kept conditions were chosen by the DEPENDENCY
    book's telescope, so the consumer need not offer them: a missing
    mapping is a FRONTIER (hypothesis kept), where for a same-book entry
    it stays an internal DEFECT. -/
structure ReplayedEntry where
  thm : String
  decl : Name
  conds : List String
  formula : SExpr
  crossBook : Bool := false
  deriving Repr, Inhabited

abbrev ReplayedRegistry := List ReplayedEntry

/-- Macro-side D1 registry (P3, the capstone REPLAYED-STATEMENT finding —
    the dated label said "capstone-mirror"; this layer is replayed
    statements, not the product, per docs/LEXICON.md): each
    `driver_replayed%` invocation registers its enclosing definition
    (world, ACL2 theorem name, decl, kept conds) so LATER same-world
    invocations' dependency discharges APPLY the constant instead of
    re-replaying the tree — parity with the runner's ReplayedStatements
    route. The re-replay route can frontier where the standalone replay
    was green (TRUE-LISTP-RM inside the ORDERED-PERMS telescope); the
    registry route maps the dep's kept conds onto the consumer's own
    telescope fvars (`depReplayedProofAt`). Lives here (upstream) because
    an `initialize` cannot be evaluated in its defining module. -/
initialize replayedRegistryExt :
    Lean.SimplePersistentEnvExtension
      (Name × String × Name × List String × SExpr)
      (List (Name × String × Name × List String × SExpr)) ←
  Lean.registerSimplePersistentEnvExtension {
    addEntryFn := fun l e => e :: l
    addImportedFn := fun ess => (ess.map (·.toList)).toList.flatten }

end ACL2.Replay.Driver
