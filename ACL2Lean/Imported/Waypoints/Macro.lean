import ACL2Lean.Replay.Driver
import ACL2Lean.Replay.Runner
import ACL2Lean.Replay.ParametricInstantiate
import ACL2Lean.Imported.SimpleWorld
import ACL2Lean.Imported.AppAssoc
import ACL2Lean.Imported.Lifting
import ACL2Lean.Imported.Perm
import ACL2Lean.Imported.Sorting

namespace ACL2.Imported.Waypoints

open ACL2 ACL2.Replay ACL2.Replay.Driver ACL2.Lifting Lean Lean.Meta Lean.Elab

/-- SEAM REACHABILITY — the ONE copy (R4, gate-cruft review 2026-08-11;
    there used to be two cosmetically-divergent inlines). Does `start`'s
    proof term transitively consume one of `seams`, and if so which? Only
    constants under one of `expandUnder` are expanded; a seam itself is
    matched by NAME and never expanded (its proof object is huge).
    Deterministic, in-Lean.

    MOVED here from `Waypoints/Catalog.lean` (R-1b, 2026-08-16) so the
    MIRROR-level gate (`MirrorProofs/SeamGate.lean`) can reuse it without
    importing the catalog — this module is upstream of both. Same
    namespace, so the catalog's call site is unchanged. -/
def seamReachesAny? (env : Lean.Environment) (start : Lean.Name)
    (seams : List Lean.Name)
    (expandUnder : List Lean.Name := [`ACL2.Imported.Waypoints]) :
    Option Lean.Name :=
  Id.run do
    let mut frontier : List Lean.Name := [start]
    let mut visited : Lean.NameSet := {}
    let mut found : Option Lean.Name := none
    while found.isNone && !frontier.isEmpty do
      let c := frontier.head!
      frontier := frontier.tail!
      unless visited.contains c do
        visited := visited.insert c
        if seams.contains c then
          found := some c
        else if expandUnder.any (·.isPrefixOf c) then
          if let some ci := env.find? c then
            -- v4.33 (4.30 #12973): theorem values need `allowOpaque`,
            -- or the seam walk cannot see through in-namespace theorems
            if let some v := ci.value? (allowOpaque := true) then
              frontier := v.getUsedConstants.toList ++ frontier
    return found

/-- The single-seam form — the waypoint-layer catalog gate's shape. -/
def seamReaches (env : Lean.Environment) (start seam : Lean.Name) : Bool :=
  (seamReachesAny? env start [seam]).isSome

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
    convention.

    HEARTBEAT-BOUND POLICY for the `set_option maxHeartbeats N in` lines
    that precede consumers of this macro (release-hygiene sweep,
    2026-08-19 — the TODO "heartbeat hacking" audit). Every such site
    guards ONE invocation of this macro, and this macro does no PROOF
    SEARCH: it walks a recorded ACL2 clause tree deterministically. A
    raise therefore cannot make a theorem replay that would otherwise
    fail on some other route — there is no other route — it only changes
    how long a runaway takes to surface. The bounds that actually protect
    the replay are INTERNAL and separately calibrated: `Runner.tryReplay`
    (3M user units per theorem, 10M for the admission class),
    `Runner.tryDischarge` (1M per DP leaf), `Harness.dischargeBudget` (3M
    per discharge window), `Discharge.dpOnlyProverGuard` (1M per DP
    attempt) — each with its own measured margin at its own docstring.
    So the module-level values are OUTER ENVELOPES over that same work.
    Each site below carries its MEASURED cost from the 2026-08-19 sweep
    (`lake env lean -D trace.profiler=true -D
    trace.profiler.useHeartbeats=true`), in USER units (1 unit = 1000
    heartbeats; the Lean default bound is 200 000 units). Re-measure with
    that command; a number without a date is stale by construction. -/
syntax depsClauseDR := &" deps " "[" ident,* "]"

elab "driver_replayed%" devId:ident worldId:ident nm:str
    wt:(&" with_termination")?
    uf:(&" usefi")?
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
  let mut crossDevs : List (String × Development) := []
  if let some d := deps then
    -- depsClauseDR children: [0] atom " deps " [1] "[" [2] sepBy [3] "]"
    for depId in (d.raw[2].getSepArgs.map (fun a => (⟨a⟩ : Ident))) do
      let depName ← Lean.resolveGlobalConstNoOverload depId
      let depDev ← unsafe Meta.evalExpr Development
        (mkConst ``ACL2.Development) (mkConst depName)
      crossTrees := crossTrees ++ ACL2.Replay.Runner.bookTrees depDev
      crossDevs := crossDevs ++ [(depName.toString, depDev)]
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
        s!"term_replayed_{worldName}_{fn}"
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
  -- THE `:USE (:FUNCTIONAL-INSTANCE …)` PRE-PASS (R4 wave 2g) — OPT-IN
  -- via `usefi`, and the sweep harness's own route mirrored here, so a
  -- waypoint module can replay a FUNCTIONAL-INSTANCE proof at all.
  --
  -- WHY IT HAS TO BE HERE. Before this wave the discharge existed ONLY
  -- as a `runBook` parameter the coverage harness supplies
  -- (`Tests/Coverage/Harness.lean`), so `sorting/sorts-equivalent`'s
  -- three capstones — whose entire proofs are one `:USE
  -- (:FUNCTIONAL-INSTANCE …)` node — were replayable by the SWEEP and
  -- by nothing else, and the waypoint layer had no route to them.
  --
  -- Three things, in the harness's order and for its reasons: the dep
  -- books' recorded ADMISSIONS carried to this world (transport first,
  -- re-replay as the fallback — the totality surface the instantiation
  -- needs); the LIBRARY PARAMETRIC constants, named as Name LITERALS so
  -- no import is forced on modules that do not have them (absent =
  -- `env.contains` misses = the rebuild route, unchanged); and the
  -- prepare itself, run in THIS shallow context because the composition
  -- overflows the worker stack inside a row telescope. Unlike the
  -- sweep this prepares only the ONE theorem being replayed, and a
  -- failed prepare HARD-FAILS here rather than being logged and skipped
  -- — a waypoint row states a frontier, it does not carry one.
  let mut preparedUseFi : List (String × Name × List (String × String)) := []
  if uf.isSome then
    let wVal := dev.toWorld
    let wExpr := mkConst worldName
    let mut termByFn : List (String × Name × List String × List SExpr) := []
    for (depName, depDev) in crossDevs do
      for (fn, tcp) in ACL2.Replay.Runner.recordedTerminationDefuns
          depDev.justifications depDev do
        unless termByFn.any (·.1 == fn) do
          let base := String.map (fun c => if c.isAlphanum then c else '_')
            s!"usefi_term_{worldName}_{fn}"
          let mName := Name.mkStr2 "ReplayedTermination" base
          -- THE COMPANION CONDS CONSTANT (close-out arc, J-1-2), the same
          -- device `crossBookRegistry` has always used for its own
          -- termination cache. A cached constant's CONDITION LIST cannot be
          -- assumed empty and cannot be recovered from the constant alone:
          -- BSORT's admission is CONDITIONAL (its measure decrease is
          -- licensed by HOW-MANY-BAD-PAIRS-BNEXT, a `:LINEAR` rule proved
          -- before the defun), so `usefi_term_…_BSORT` has a premise binder.
          -- Recording `[]` for it made `thmAt` apply the constant with no
          -- condition arguments, and the resulting application type mismatch
          -- surfaced as `depReplayedProofAt: dependency ORDEREDP-BSORT's
          -- replay failed (frontier)` — an error naming a different theorem
          -- entirely. Latent until now because the msort/qsort rows never
          -- need BSORT's totality; the FIRST row that does is
          -- BSORT-IS-ISORT, and the first pre-pass in a module registers the
          -- constant that every later row then re-reads.
          let mCondsName := Name.mkStr2 "ReplayedTermination" s!"{base}_conds"
          let condsTy := mkApp (mkConst ``List [.zero]) (mkConst ``String)
          let clause := (tcp.root.map (·.inputClause)).getD []
          let conds? : Option (List String) ←
            if (← getEnv).contains mName then do
              unless (← getEnv).contains mCondsName do
                throwError "driver_replayed% usefi: cached {mName} exists \
                  WITHOUT its companion {mCondsName} (partial cache state \
                  or sanitizer collision)"
              some <$> (unsafe Meta.evalExpr (List String) condsTy
                (mkConst mCondsName))
            else do
              let transported ← ACL2.Replay.Runner.tryTransportDepAdmission
                worldName.toString depName depDev.toWorld wVal wExpr fn tcp
                mName
              if transported then
                -- the transport carries UNCONDITIONAL dep constants only,
                -- so `[]` is a fact here, not an assumption — recorded
                -- explicitly so the cache branch above reads it back
                Lean.addAndCompile (.defnDecl {
                  name := mCondsName, levelParams := [], type := condsTy,
                  value := Lean.toExpr ([] : List String), hints := .opaque,
                  safety := .safe })
                pure (some ([] : List String))
              else do
                let (status, reg?) ← ACL2.Replay.Runner.replayAdmission depDev
                  wVal wExpr tcp mName (crossTrees := crossTrees)
                match reg? with
                | some conds =>
                  Lean.addAndCompile (.defnDecl {
                    name := mCondsName, levelParams := [], type := condsTy,
                    value := Lean.toExpr conds, hints := .opaque,
                    safety := .safe })
                  pure (some conds)
                | none =>
                  logInfo m!"driver_replayed% usefi: the {depName}/{fn} \
                    admission pre-pass did not land ({status}) — the \
                    instantiation will hard-fail if it needs that totality"
                  pure none
          if let some conds := conds? then
            unless ACL2.Replay.Runner.admissionCircular fn conds do
              termByFn := termByFn ++ [(fn, mName, conds, clause)]
    let libParametric : List (String × Name) :=
      [("WEAK-SORTFN1-IS-SORTFN2",
        "ACL2.Imported.Waypoints.weakSortfn1IsSortfn2Parametric".toName),
       ("STRONG-SSORTFN1-IS-SSORTFN2",
        "ACL2.Imported.Waypoints.strongSsortfn1IsSsortfn2Parametric".toName)]
    for (thmName, sigma, hypI) in Driver.theoremFnInstanceCites cp do
      let spec : Driver.UseFiSpec :=
        { name := thmName, subst := sigma, formula := hypI }
      let key := thmName ++ "|" ++ toString (hash (toString (repr hypI)))
      unless preparedUseFi.any (·.1 == key) do
        -- RECURSION-DEPTH guard (heartbeat/recursion sweep 2026-08-19,
        -- status recorded honestly): 131072 = 256x the 512 default, landed
        -- with the D2-a shallow-stack pre-pass (de629e9) as one of the three
        -- pieces that eliminated the usefi SIGABRT class. The DEPTH DRIVER
        -- IS UNPROFILED — `prepareUseFi` spends a native frame per telescope
        -- binder, so the depth is O(#binders of the FI telescope), but no
        -- measurement pins the constant. Same site as
        -- Tests/Coverage/Harness's copy. Named residue in TODO
        -- "heartbeat/recursion-limit raises".
        let (cName, argTys) ← Driver.withRealMaxRecDepth 131072 <|
          prepareUseFi crossDevs dev wVal wExpr spec termByFn libParametric
        preparedUseFi := preparedUseFi ++ [(key, cName, argTys)]
  let usefiDischarge? :
      Option (Driver.ReplayCtx → Driver.UseFiSpec → MetaM Expr) :=
    if uf.isSome then
      some (fun ctx spec => do
        let key := spec.name ++ "|" ++
          toString (hash (toString (repr spec.formula)))
        match preparedUseFi.find? (·.1 == key) with
        | some (_, cName, argTys) => applyPreparedUseFi cName argTys ctx
        | none => Driver.throwFrontier (m!"driver_replayed% usefi: no \
            prepared constant for {spec.name} (the pre-pass did not see \
            this cite)"))
    else none
  Meta.withLocalDeclD `env (mkConst ``Env) fun env => do
    -- channels + config from the SHARED builder (1a): the macro constructs
    -- NO channel of its own — `bookChannels`/`mkBookConfig` are the single
    -- derivation site, so a runner channel can never miss the macro again
    -- (the class that hard-failed fcRules/termination/equivRefls one at a
    -- time, and had silently dropped gzTps here until the unification).
    let ch := ACL2.Replay.Runner.bookChannels dev crossTrees crossRules
    -- SAME-WORLD entries: earlier `driver_replayed%` definitions over THIS
    -- world constant (the macro-side D1 registry).
    let sameWorld : ACL2.Replay.Driver.ReplayedRegistry :=
      ((replayedRegistryExt.getState (← getEnv)).filterMap
        fun (wn, thm, decl, conds, formula) =>
          if wn == worldName then
            some { thm := thm, decl := decl, conds := conds,
                   formula := formula }
          else none)
    -- WP5 CROSS-BOOK TRANSFER: the `deps [...]` books' demanded theorems
    -- replayed at THIS world (world-inclusion gated, `addDecl`'d once and
    -- cached by constant name across invocations in the same module).
    let (crossReg, crossTerm) ←
      if crossDevs.isEmpty then
        pure (([] : ACL2.Replay.Driver.ReplayedRegistry),
              ([] : List (String × Name × List String × List SExpr)))
      else
        (ACL2.Replay.Runner.crossBookRegistry worldName.toString dev.toWorld
          (mkConst worldName) crossDevs
          -- the SAME seed the sweep uses (P6's widening): a pin and its
          -- golden row must demand the same dependency set, or the pin
          -- stops being a check on what the sweep does.
          (ACL2.Replay.Runner.bookDemandSeed dev))
    -- THE CROSS-BOOK ADMISSION SEED (R4 wave 2g), mirroring `runBook`
    -- verbatim: an `:INCLUDE-BOOK`'d defun has NO admission proof in this
    -- book's own log, so its totality has no route at all — the transfer
    -- supplies the dependency book's own recorded waterfall, at THIS
    -- world. The macro was already computing it and DISCARDING it, which
    -- is why a consumer of an included defun (QSORT inside
    -- `sorts-equivalent`) kept a `total:` premise the sweep does not.
    -- Filtered exactly as the runner filters it: a fn with its OWN
    -- recorded admission in this book keeps that route.
    let recTermDefuns :=
      ACL2.Replay.Runner.recordedTerminationDefuns dev.justifications dev
    let termReplayed := termReplayed ++
      (crossTerm.filter fun (fn, _, _, _) =>
        !recTermDefuns.any (fun (g, _) => g == fn)
          && !termReplayed.any (fun (g, _, _, _) => g == fn))
    let cfg := ACL2.Replay.Runner.mkBookConfig dev dev.toWorld
      (mkConst worldName) env termReplayed
    let replayed := sameWorld ++ crossReg
    let (proof, conds) ← replayProofConditional cfg ch.tps cp
      (usefiDischarge := usefiDischarge?)
      dev.justifications
      (ACL2.Replay.Runner.combineRules
        (Driver.rulesBefore dev nm.getString) ch.crossRules) ch.depProofs
      replayed
      (equivRefls := ch.equivRefls) (termReplayed := termReplayed)
      (congTrees := some ch.localTrees)
    -- register the enclosing definition for later same-world consumers.
    -- INVARIANT (audit F6): the registered decl must be a plain
    -- `def X := driver_replayed% …` — or, since the v4.33 bump, the
    -- theorem-kind twin `replayed_theorem X := driver_replayed% …`
    -- (Runner.lean), which sets `Term.withDeclName` so this registration
    -- still sees the enclosing name — the entry records THIS elaboration's
    -- kept-cond list as the constant's binder telescope; a differently-
    -- ascribed enclosing decl would register a lying shape (caught loudly
    -- by unification at the consumer, never silently).
    -- ASSUMED guard (remediation verifier N1, 2026-08-05): this path
    -- registers conds verbatim, bypassing `tryReplay`'s choke point — an
    -- ASSUMED:dp-fact condition states an obligation over
    -- independently-quantified opaques that can be FALSE, so a replayed statement
    -- carrying it must never be registered (same policy as the sweep;
    -- the with_termination sub-path already fails loudly via reg? none).
    if conds.contains assumedDpFactCond || conds.contains assumedFiSelfCond then
      throwError "driver_replayed%: the replay is conditional on an \
        ASSUMED hypothesis (an unproved dp-fact, or a self-vacuous kept \
        usefi — audit 2026-08-09 outside D1) — \
        refusing to register the replayed statement. For a dp-fact the \
        fix is CITATION, not emission (close-out arc 2026-08-18): the \
        leaf already emits its :TAU-BASIS slice, and the consumer \
        (Driver/Discharge.parseTauBasisAllows -> Totality's rule-premise \
        gate) discharges it by citing the dependency theorem the slice \
        names. A leaf that lands here needs a slice shape that decode \
        does not yet cover — extend the decode, fail-closed"
    if let some declName ← Lean.Elab.Term.getDeclName? then
      Lean.modifyEnv fun e =>
        replayedRegistryExt.addEntry e (worldName, cp.name, declName, conds,
          disjoinTerm ((cp.root.map (·.inputClause)).getD []))
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
    shape). NOT registered in the replayed registry: the artifact's
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
    if conds.contains assumedDpFactCond || conds.contains assumedFiSelfCond then
      throwError "parametric_replayed%: the replay is conditional on an \
        ASSUMED hypothesis (dp-fact or self-vacuous kept usefi) — \
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

end ACL2.Imported.Waypoints
