/-
  Driver/Provers — split from Driver/Core (WP2 Stage 3a, 2026-07-17;
  see docs/plans/2026-07-18_driver-modular-refactor.md).

  Walker-independent obligation provers: totality from admission
  (proveTotality/buildTotalEnv) and the D5 ground-zero rule-hypothesis
  dischargers. The TP prover (tpWalk/proveTp) lives in Driver/TpProver.
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
        -- strong induction on av2's count, av1 inner-∀
        -- (`totality_2_rec_mu_snd` — the μ-generic form applied below;
        -- name corrected 2026-08-16, residual item 7)
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


-- THE TP PROVER (`tpArgValues`, the `tpWalk`/`tpWalkCall`/`tpWalkCallee`/
-- `proveTp` mutual block) MOVED to Driver/TpProver (T1+2 sprint P5b) —
-- the module-size ratchet, resolved by a MOVE at the docstring's own
-- seam (the J-P3b-f / J-RT2e precedent), never by loosening the
-- baseline. `bindArgsVarProofs` above stays here: it is the piece BOTH
-- provers share.

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
   ("FOLD-CONSTS-IN-+",    (``gz_rule_fold_consts_in_plus, ["BINARY-+"])),
   -- the arithmetic-3 comm/assoc + if-lifting runes (T1+2 sprint P4b):
   -- criterion class (ii) — `:SOURCE :INCLUDE-BOOK`, no tree in any
   -- captured log — the FOLD-CONSTS-IN-+ class exactly. The rune IS the
   -- rule name here (ACL2's `|…|` bar-quoted symbols).
   ("(+ y x)",             (``gz_rule_plus_comm,    ["BINARY-+"])),
   ("(+ y (+ x z))",       (``gz_rule_plus_comm2,   ["BINARY-+"])),
   ("(+ (+ x y) z)",       (``gz_rule_plus_assoc,   ["BINARY-+"])),
   ("(+ x (if a b c))",    (``gz_rule_plus_if_lift, ["BINARY-+"])),
   ("(equal (if a b c) x)", (``gz_rule_equal_if_lift, ["EQUAL"]))]

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
