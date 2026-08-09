import ACL2Lean.Replay.Driver
import ACL2Lean.Replay.Runner
import ACL2Lean.Replay.ParametricInstantiate
import ACL2Lean.Imported.SimpleWorld
import ACL2Lean.Imported.AppAssoc
import ACL2Lean.Imported.Lifting
import ACL2Lean.Imported.Perm
import ACL2Lean.Imported.Sorting

namespace ACL2.Imported.Mirrors

open ACL2 ACL2.Replay ACL2.Replay.Driver ACL2.Lifting Lean Lean.Meta Lean.Elab

/-- `driver_replayed% dev world "thm-name"` — the DRIVER's conditional replayed statement
    for the named theorem of the development `dev`, over the derived world
    constant `world`: a `∀ env, <hypotheses> → ∃N∀f≥N ∃v, eval = some v ∧
    v ≠ nil` proof OBJECT (ACL2's truthiness claim, G2) produced by
    `replayProofConditional` from the reconstructed tree.
    UNCHECKED INVARIANT (audit 2026-07-31 inside finding 4): `world`
    must be `derive_world`'s output for THIS `dev` — the macro takes
    them as independent arguments; a mismatched pair is fail-closed
    (the `by decide` world facts and defeq statement pins at every
    consumer die), never silently wrong, but the pairing itself is by
    convention. -/
syntax depsClauseDR := &" deps " "[" ident,* "]"

elab "driver_replayed%" devId:ident worldId:ident nm:str
    wt:(&" with_termination")?
    deps:(depsClauseDR)? : term => do
  let devName ← Lean.resolveGlobalConstNoOverload devId
  let worldName ← Lean.resolveGlobalConstNoOverload worldId
  let dev ← unsafe Meta.evalExpr Development (mkConst ``ACL2.Development)
    (mkConst devName)
  let some cp := Driver.findThm dev nm.getString
    | throwError "{nm.getString}: not found in the development (or ambiguous \
                  up to case — findThm refuses to guess)"
  -- CROSS-BOOK dependency trees (2a): `deps [devA, devB]` offers the named
  -- developments' theorem trees for rule:/cong: discharge, mirroring the
  -- sweep's prior-book accumulation (the consumer books' worlds re-emit
  -- the included defuns, so the trees replay at THIS world; fail-closed —
  -- a missing tree keeps the hypothesis).
  let mut crossTrees : List (String × ClauseProof) := []
  let mut crossRules : List ACL2.RuleSpec := []
  if let some d := deps then
    -- depsClauseDR children: [0] atom " deps " [1] "[" [2] sepBy [3] "]"
    for depId in (d.raw[2].getSepArgs.map (fun a => (⟨a⟩ : Ident))) do
      let depName ← Lean.resolveGlobalConstNoOverload depId
      let depDev ← unsafe Meta.evalExpr Development
        (mkConst ``ACL2.Development) (mkConst depName)
      crossTrees := crossTrees ++ ACL2.Replay.Runner.bookTrees depDev
      -- P3 cross-rules: the dep book's stored rules ride with its trees
      crossRules := crossRules
        ++ (ACL2.Replay.Runner.allBookRules depDev).filter
          (fun r => !crossRules.any (fun o => o.runeKey == r.runeKey))
  -- TERMINATION PRE-PASS (the runner's route, mirrored; OPT-IN via
  -- `with_termination` — a consumer whose induction scheme needs a
  -- non-destructor decrease, e.g. qsort's filter call sites, discharges
  -- its totality from the fn's REPLAYED admission waterfall). Each
  -- recorded admission is replayed ONCE PER WORLD and declared as a
  -- `ReplayedTermination.*` constant, its undischarged conditions
  -- persisted in a companion `*_conds` constant so later invocations
  -- reuse both without re-replaying. A failed or circular replay is
  -- skipped (the consumer then hard-fails at the honest frontier).
  let mut termReplayed : List (String × Name × List String × List SExpr)
    := []
  if wt.isSome then
    let condsTy := mkApp (mkConst ``List [.zero]) (mkConst ``String)
    for (fn, tcp) in ACL2.Replay.Runner.recordedTerminationDefuns
        dev.justifications dev do
      let base := String.map (fun c => if c.isAlphanum then c else '_')
        s!"term_mirror_{worldName}_{fn}"
      let mName := Name.mkStr2 "ReplayedTermination" base
      let condsName := Name.mkStr2 "ReplayedTermination" s!"{base}_conds"
      -- CACHE-KEY HAZARD (audit 2026-07-31 inside finding 2, same
      -- hazard the runner documents for its constants): the
      -- alphanumeric sanitizer is not injective across (world, fn)
      -- pairs. A collision is fail-closed (the cached constant is only
      -- ever APPLIED, so a type mismatch fails unification) — but
      -- guard the partial-state case with a named error.
      let conds? ← do
        if (← getEnv).contains mName then
          unless (← getEnv).contains condsName do
            throwError "driver_replayed% with_termination: cached \
              termination constant {mName} exists WITHOUT its companion \
              {condsName} (partial cache state or sanitizer collision)"
          some <$> (unsafe Meta.evalExpr (List String) condsTy
            (mkConst condsName))
        else
          let (status, reg?) ← ACL2.Replay.Runner.replayAdmission dev
            dev.toWorld (mkConst worldName) tcp mName
            (crossTrees := crossTrees)
          if reg?.isNone then
            throwError "driver_replayed% with_termination: the {fn} \
              admission pre-pass FAILED ({status}) — the consumer would \
              hard-fail at the decrease frontier"
          match reg? with
          | some conds => do
            Lean.addAndCompile (.defnDecl {
              name := condsName, levelParams := [], type := condsTy,
              value := Lean.toExpr conds, hints := .opaque,
              safety := .safe })
            pure (some conds)
          | none => pure none
      if let some conds := conds? then
        if ACL2.Replay.Runner.admissionCircular fn conds then
          -- circularity guard, now LOUD (audit 2026-07-31 inside
          -- finding 3): the consumer will hard-fail at the decrease
          -- frontier; name the cause here.
          logInfo m!"driver_replayed% with_termination: {fn}'s replayed \
            admission is conditional on its own facts ({conds}) — \
            SKIPPED (circularity guard); the consumer replay will \
            hard-fail at the decrease frontier if it needs it"
        else
          termReplayed := termReplayed
            ++ [(fn, mName, conds, (tcp.root.map (·.inputClause)).getD [])]
  Meta.withLocalDeclD `env (mkConst ``Env) fun env => do
    -- channels + config from the SHARED builder (1a): the macro constructs
    -- NO channel of its own — `bookChannels`/`mkBookConfig` are the single
    -- derivation site, so a runner channel can never miss the macro again
    -- (the class that hard-failed fcRules/termination/equivRefls one at a
    -- time, and had silently dropped gzTps here until the unification).
    let ch := ACL2.Replay.Runner.bookChannels dev crossTrees crossRules
    let cfg := ACL2.Replay.Runner.mkBookConfig dev dev.toWorld
      (mkConst worldName) env termReplayed
    let mirrors : ACL2.Replay.Driver.ReplayedRegistry :=
      ((mirrorRegistryExt.getState (← getEnv)).filterMap
        fun (wn, thm, decl, conds) =>
          if wn == worldName then some (thm, decl, conds) else none)
    let (proof, conds) ← replayProofConditional cfg ch.tps cp
      dev.justifications
      (ACL2.Replay.Runner.combineRules
        (Driver.rulesBefore dev nm.getString) ch.crossRules) ch.depProofs
      mirrors
      (equivRefls := ch.equivRefls) (termReplayed := termReplayed)
      (congTrees := some ch.localTrees)
    -- register the enclosing definition for later same-world consumers.
    -- INVARIANT (audit F6): the registered decl must be a plain
    -- `def X := driver_replayed% …` — the entry records THIS elaboration's
    -- kept-cond list as the constant's binder telescope; a differently-
    -- ascribed enclosing decl would register a lying shape (caught loudly
    -- by unification at the consumer, never silently).
    -- ASSUMED guard (remediation verifier N1, 2026-08-05): this path
    -- registers conds verbatim, bypassing `tryReplay`'s choke point — an
    -- ASSUMED:dp-fact condition states an obligation over
    -- independently-quantified opaques that can be FALSE, so a mirror
    -- carrying it must never be registered (same policy as the sweep;
    -- the with_termination sub-path already fails loudly via reg? none).
    if conds.contains assumedDpFactCond then
      throwError "driver_replayed%: the replay is conditional on an \
        ASSUMED dp-fact (an unproved, possibly-false obligation) — \
        refusing to register the mirror; fix the leaf's emission instead"
    if let some declName ← Lean.Elab.Term.getDeclName? then
      Lean.modifyEnv fun e =>
        mirrorRegistryExt.addEntry e (worldName, cp.name, declName, conds)
    Meta.mkLambdaFVars #[env] proof

/-- `parametric_replayed% dev "thm-name" [deps […]]` — the PARAMETRIC
    replayed statement (Phase 2 item c, the R6 scope abstraction): the
    named theorem's recorded tree replayed over an ABSTRACT `w : World`
    (`replayProofParametric`), yielding
    `∀ env, ∀ w, (USED pins/no-shadows…) → (kept telescope…) → EvTrue w env Φ`
    (`env` outermost — bound here before `w`; no premise mentions it, so
    the order is semantically inert).

    The abstraction set is READ OFF the development's emitted scope
    surface (`Development.scopes`): every signature fn AND witness defun
    of every `(:ENCAPSULATE-BEGIN :SIGS …)` scope is UNPINNED — witness
    bodies never enter the statement (the R6 witness rule) and an unfold
    demand on one hard-fails (the witness-dereference guard, design item
    5). Other canonical-model defuns are OFFERED definition pins; only
    USED ones are bound (a tree that never unfolds keeps none). The
    scope's constraint theorems surface as kept `rule:` premises in
    ACL2's STORED-RULE form (audit 2026-08-08: e.g. `(EQUAL (ORDEREDP
    (SORTFN1 X)) 'T)` — ACL2's iff→equal strengthening under the
    pre-scope booleanp type-prescription; over an abstract `w` with
    ORDEREDP unpinned this is STRONGER than the bare truthy constraint,
    so the model class is "worlds satisfying the stored rules", a
    subset of the bare-constraint models; concrete instantiations
    discharge it since the concrete rule replay produces exactly this
    shape). NOT registered in the mirror registry: the artifact's
    consumer is the R7b instantiation (Phase 3), not same-world replay
    composition. -/
elab "parametric_replayed%" devId:ident nm:str
    deps:(depsClauseDR)? : term => do
  let devName ← Lean.resolveGlobalConstNoOverload devId
  let dev ← unsafe Meta.evalExpr Development (mkConst ``ACL2.Development)
    (mkConst devName)
  let some cp := Driver.findThm dev nm.getString
    | throwError "{nm.getString}: not found in the development (or ambiguous \
                  up to case — findThm refuses to guess)"
  let scopes ← match dev.scopes with
    | .ok ss => pure ss
    | .error e => throwError "parametric_replayed%: {e}"
  -- the UNPINNED set (audit 2026-08-08 inside F1): sigs AND the scopes'
  -- witness defuns — a witness HELPER (e.g. SORTFN1-INSERT) is not a sig
  -- but its body is scope-local material; offering it a definition pin
  -- would let a tree-shape change silently condition the "parametric"
  -- statement on the witness (the banned masquerade). With the helper
  -- unpinned, such a demand hits the witness-dereference hard-fail.
  let sigFns := ((scopes.flatMap (fun sc =>
    sc.sigs ++ sc.witnesses.map (fun (n, _, _) => ({ name := n } : Symbol)))
    ).eraseDups)
  if sigFns.isEmpty then
    throwError "parametric_replayed%: {devName} has no constrained scope — \
      the parametric form is the encapsulate artifact (use driver_replayed%)"
  let mut crossTrees : List (String × ClauseProof) := []
  let mut crossRules : List ACL2.RuleSpec := []
  -- deps here feed OFFER derivation only (use:/rule: hypothesis types come
  -- from the dep trees' translated Goal clauses); with `discharge := false`
  -- nothing is ever discharged FROM them — cited dep theorems stay
  -- premises of the parametric statement.
  if let some d := deps then
    for depId in (d.raw[2].getSepArgs.map (fun a => (⟨a⟩ : Ident))) do
      let depName ← Lean.resolveGlobalConstNoOverload depId
      let depDev ← unsafe Meta.evalExpr Development
        (mkConst ``ACL2.Development) (mkConst depName)
      crossTrees := crossTrees ++ ACL2.Replay.Runner.bookTrees depDev
      crossRules := crossRules
        ++ (ACL2.Replay.Runner.allBookRules depDev).filter
          (fun r => !crossRules.any (fun o => o.runeKey == r.runeKey))
  Meta.withLocalDeclD `env (mkConst ``Env) fun env => do
    let ch := ACL2.Replay.Runner.bookChannels dev crossTrees crossRules
    -- worldExpr placeholder: `replayProofParametric` REPLACES it with the
    -- bound `w` fvar before any use; the `World` type constant is not a
    -- term, so an accidental leak fails elaboration instantly.
    let cfg := ACL2.Replay.Runner.mkBookConfig dev dev.toWorld
      (mkConst ``ACL2.World) env
    let (proof, conds) ← replayProofParametric cfg sigFns ch.tps cp
      dev.justifications
      (ACL2.Replay.Runner.combineRules
        (Driver.rulesBefore dev nm.getString) ch.crossRules) ch.depProofs
      (equivRefls := ch.equivRefls) (congTrees := some ch.localTrees)
    if conds.contains assumedDpFactCond then
      throwError "parametric_replayed%: the replay is conditional on an \
        ASSUMED dp-fact (an unproved, possibly-false obligation) — \
        refusing to emit the parametric constant"
    logInfo m!"parametric_replayed% {nm.getString}: sigs \
      [{", ".intercalate (sigFns.map (·.name))}]; premises \
      [{", ".intercalate conds}]"
    Meta.mkLambdaFVars #[env] proof

/-- `instantiate_parametric% const dev world "thm-name" [deps […]]` — the
    R7b "apply at a model" move at the CANONICAL world (Phase 3 queue
    item 1, audit O6 non-vacuity): apply the named PARAMETRIC constant
    at the dev's derived world and DISCHARGE every premise binder with
    the existing provers — no new proof machinery:

    - `hnoshadow_*` → `proveNoShadow` (kernel decide at the concrete world);
    - `htotal_*`    → `buildTotalEnv` (the admission-justification provers);
    - `htp_*`       → `proveTp`;
    - `hrule_*`     → `dischargeRuleHyp` (re-replays the dependency's
                      recorded tree — the constraint theorems' pass-1
                      chains, i.e. the R6 conservativity content);
    - `husethm_*`   → `dischargeUseHyp`.

    Dispatch is NAME-GUIDED but TYPE-CHECKED: the binder name selects the
    candidate class/key, the recomputed offer type must be `isDefEq` to
    the binder's instantiated type (a mismatch hard-fails — the name can
    narrow the search but never lie), and each discharge proof is checked
    against the binder type by application. An undischargeable premise
    is KEPT as an explicit hypothesis of the declared constant (the D6
    discipline — the logged KEPT list is the honest satisfiability
    frontier; an empty list is the full non-vacuity witness). Result:
    `∀ env, <kept premises> → EvTrue world env ⟦the theorem's formula⟧`. -/
syntax totalsClauseIP := &" totals " "[" ident,* "]"

elab "instantiate_parametric%" constId:ident devId:ident worldId:ident
    nm:str deps:(depsClauseDR)? tots:(totalsClauseIP)? : term => do
  let constName ← Lean.resolveGlobalConstNoOverload constId
  let devName ← Lean.resolveGlobalConstNoOverload devId
  let worldName ← Lean.resolveGlobalConstNoOverload worldId
  let dev ← unsafe Meta.evalExpr Development (mkConst ``ACL2.Development)
    (mkConst devName)
  unless (Driver.findThm dev nm.getString).isSome do
    throwError "instantiate_parametric%: {nm.getString} not found"
  let mut crossTrees : List (String × ClauseProof) := []
  let mut crossRules : List ACL2.RuleSpec := []
  let mut crossDevs : List (String × Development) := []
  if let some d := deps then
    for depId in (d.raw[2].getSepArgs.map (fun a => (⟨a⟩ : Ident))) do
      let depName ← Lean.resolveGlobalConstNoOverload depId
      let depDev ← unsafe Meta.evalExpr Development
        (mkConst ``ACL2.Development) (mkConst depName)
      crossTrees := crossTrees ++ ACL2.Replay.Runner.bookTrees depDev
      crossRules := crossRules
        ++ (ACL2.Replay.Runner.allBookRules depDev).filter
          (fun r => !crossRules.any (fun o => o.runeKey == r.runeKey))
      crossDevs := crossDevs ++ [(depName.toString, depDev)]
  let mut totsNames : List Name := []
  if let some t := tots then
    for dId in (t.raw[2].getSepArgs.map (fun a => (⟨a⟩ : Ident))) do
      totsNames := totsNames ++ [← Lean.resolveGlobalConstNoOverload dId]
  Meta.withLocalDeclD `env (mkConst ``Env) fun envV => do
    let (pf, keptNames, concl) ← instantiateParametricAt dev dev.toWorld
      (mkConst worldName) nm.getString crossTrees crossRules totsNames
      (mkConst constName) envV (crossDevs := crossDevs)
    logInfo m!"instantiate_parametric% {constName} @ {worldName}: \
      conclusion {concl}; KEPT premises: \
      [{", ".intercalate keptNames}] (empty = full non-vacuity witness)"
    Meta.mkLambdaFVars #[envV] pf

end ACL2.Imported.Mirrors
